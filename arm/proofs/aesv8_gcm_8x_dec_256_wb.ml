(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* WB AES-256-GCM decrypt main loop (nblk > 8): ENSURES_WHILE proof.          *)
(*                                                                            *)
(* Extends the proven <=8-block WB chain (inlined below) to the               *)
(* software-pipelined 8-blocks-per-iteration main loop L256_dec_main_loop     *)
(* (0x4c0..0xa0c), the GHASH catch-up prepretail (0xa10..0xedc), and the tail *)
(* cascade (from 0xee0), so correctness holds for arbitrary nblk >= 1.        *)
(*                                                                            *)
(* Binary: arm/aes_gcm/aesv8_gcm_8x_dec_256_wb.o                              *)
(*                                                                            *)
(* KEY PIPELINE FACT:                                                         *)
(*         GHASH lags stores by one 8-block group, so the ENSURES_WHILE       *)
(*         invariant is the TWO-STREAM form (store/counter stream at 8(i+1),  *)
(*         GHASH stream at 8i, bridged by raw ciphertext regs q8..q15), NOT   *)
(*         a lag-free single fold.                                            *)
(*                                                                            *)
(* The file holds, in order:                                                  *)
(*   - the machine code, the guard and the <=8-block chain: the band tails,   *)
(*     the shared front, the small-message path (nblk <= 4) and the readable  *)
(*     band and dispatch theorems; the symbolic counter layer (Sec 2) sits    *)
(*     ahead of the band-tail ivec closer that uses it;                       *)
(*   - the nblk > 8 proof: Sec 1 (scalar rungs), Sec 3 (FRONT-N), Secs 4-10   *)
(*     (the ENSURES_WHILE loop), Sec 11 (prepretail), Sec 12 (recomposition); *)
(*   - the two byte-list spines and the exported theorems (see the ROADMAP).  *)
(* ========================================================================= *)


(* ====================================================================== *)
(* The <=8-block WB chain comes first, so the whole decrypt proof is one  *)
(* file.                                                                   *)
(* ====================================================================== *)

(* The specification vocabulary and lemmas shared with the other AES-GCM
   proofs (ctr_block, nist_input_block, htable_mem_8, HTABLE_MEM_8_FLAT,
   DISCARD_STALE_TAC, ...), and the concrete-key instances of htable_mem_8. *)
needs "arm/proofs/utils/aes_gcm_common.ml";;
needs "arm/proofs/utils/aes_gcm_htable_kat.ml";;

needs "arm/proofs/aesv8_gcm_8x_dec_256_lemmas.ml";;
needs "arm/proofs/utils/aes_gcm_dec_spec.ml";;
needs "common/ghash_nist_bridge.ml";;

(* ------------------------------------------------------------------------- *)
(* Machine code (print_literal_from_elf "arm/aes_gcm/aesv8_gcm_8x_dec_256_wb.o") *)
(* ------------------------------------------------------------------------- *)

let aesv8_gcm_8x_dec_256_wb_mc = define_assert_from_elf "aesv8_gcm_8x_dec_256_wb_mc"
  "arm/aes_gcm/aesv8_gcm_8x_dec_256_wb.o"
[
  0xd503245f;       (* arm_BTI *)
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

(* `|- LENGTH aesv8_gcm_8x_dec_256_wb_mc = 5960`.  The code-region length in the
   nonoverlapping preconditions is spelled `LENGTH aesv8_gcm_8x_dec_256_wb_mc`
   (not the hardcoded 5960) so a future .text-size change needs no bookkeeping.
   But the ARM store-safety check (NONSELFMODIFYING_STATE_UPDATE_TAC ->
   ORTHOGONAL_COMPONENTS_RULE via NONOVERLAPPING_DRIVERS) does numeric arithmetic
   on that length, so each simulation init reduces it to the numeral first via
   RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]).  Same idiom as aes_xts_decrypt.ml. *)
let WB_MC_LEN = fst AESV8_GCM_8X_DEC_256_WB_EXEC;;

(* ------------------------------------------------------------------------- *)
(* Shared statement/capture machinery.                                        *)
(* ------------------------------------------------------------------------- *)

(* AES256_XOR_ENCRYPT_RECONSTRUCT and aes13 (the AES128_CIPHER_RECONSTRUCT
   pattern). *)
needs "arm/proofs/utils/aes_gcm_reconstruct.ml";;

(* The 12-slot aws-lc htable layout as one predicate over the abstract GHASH
   input key h (slot values = the byteswapped polyval_dot towers + packed
   karatsuba mids, exactly the per-slot hypotheses of the <=8-block band chain).
   htable_mem_4 pattern.  EXPAND (REWRITE_TAC[htable_mem_dec] + let_CONV)
   BEFORE stepping so the htable loads resolve. *)
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

(* ins->ext: the GHASH-tail Karatsuba mids use
   `ext vD.16b,vN.16b,vN.16b,#8` in place of `ins vD.d[0],vN.d[1]` (a false-dep
   break; both consumed lane-0-only, values identical).  The stepper models
   `ext vD,vN,vN,#8` on a 128-bit register as
   `word_subword (word_join vN vN:256 word) (64,128):128 word` (a rot-by-64).
   The normalization lives ONCE in the per-step normalizer
   GCM_SIMD_SIMPLIFY_CORE_TAC (aesv8_gcm_8x_dec_256_lemmas.ml): the lemma
   EXT8_LANE0_IS_SUBWORD_HI collapses the COMPOSED lane-0 projection
   `word_subword (<ext form>) (0,64)` (the only way any of the 9 sites consumes
   the ext register -- via eor .8b / pmull .1d) back to `word_subword vN (64,64)`,
   exactly the plain lane AWS-LC's `ins` gives.  So every tail bridge sees the
   same operand shapes as with `ins`, and ABBREV_INNER_PMULS's qq-numbering is
   the same.  AUTO_MERGE_MIDS_KM_TAC below is a numbering-agnostic safety net
   for the N>=3 mid pairing. *)

(* KEEPGH stepper. *)
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
(* Q-scoped, fixpoint-memoized single-pass per-step normalizer for the tails'
   GHASH multiply/reduce stepper.  Two composed levers:
     (a) a SINGLE pass (GCM_SIMD_SIMPLIFY_CORE_TAC) rather than the double-pass
         GCM_SIMD_SIMPLIFY_TAC; the second pass changes the pile on only 2/40
         KEEPGH steps in k=2 (block-boundary REV64 folds, re-done downstream by
         the Q19 bridge).
     (b) Q-scope and fixpoint-memoize the pass.  The KEEPGH windows keep
         Q16-Q19 across ~7-40 steps; the per-step normalizer's rules can ONLY fire on
         `read Qn s = <tower>`, and re-fold Q-reads already at a fixpoint.  gcm_simd_kgh_tbl
         memoizes proven fixpoints; is_qreg_read guards the O(1) head before the rewrites.
   Bit-identical to the full double-pass GCM_SIMD_SIMPLIFY_CORE_TAC applied
   per-asm (0 mismatches over the 40 KEEPGH steps of k=2), and skipping a proven
   fixpoint yields exactly F's output by construction.  The cache is reset per
   tail body via CLEAR_KEEPGH_MEMO_TAC in WB_PREP_TAC (each WB_TAIL_GEN2_k
   `prove` is hermetic).  Sole consumers: the 8 WB_TAIL_{1..8}_TAC. *)
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
(*     Shared inter-band machinery (bridge closers, spec folds, steppers)    *)
(* ------------------------------------------------------------------------- *)



(* ------------------------------------------------------------------------- *)
(* The WB 2-block bridge close (via GMULT2_FULL_CORRECT_BA), with
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

(* ========================================================================= *)
(* Band lemmas for the 3..8-block whole-blocks tails (bit_len = 128*N).      *)
(* ========================================================================= *)

(* ---- shared N>=3 band machinery ---- *)
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
let WB_MID_FIX = [WORD_SUBWORD_INSERT_INNER; WORD_SUBWORD_INSERT_OUTER; INSERT_SUBWORD_KILL;
                  WORD_INSERT_SUBWORD; JOINMID; JOIN_SUBWORD_RULES; RF8_SUBWORD;
                  WORD_SUBWORD_SUBWORD; WORD_SUBWORD_XOR];;
let POLYVAL_DOT_SYM = prove
 (`!a b:int128. polyval_dot a b = polyval_dot b a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polyval_dot] THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_PMUL_SYM]);;
let GCM_CTR_INC2_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc ctr0)`,
        subst [`word 2:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let _, GMULT3_FULL_CORRECT_BA = build_GMULTn_fast 3;;
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

(* ---- shared merge machinery (MERGE_ANY_TAC, MERGE_QQPAIR_KM_TAC); see the
   WB_8 header note for the greedy-pairing story. ---- *)

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

(* ---- WB_7/WB_8 stepping machinery.
   Keeping all of Q16-Q19 alive across the ~130 states of the stores window
   (ARM_STEPS_FOLD_KEEPGH_TAC) makes the per-step GCM_SIMD_SIMPLIFY pass
   rescan a linearly growing pile, O(n^2) overall.  Instead, step the window
   keeping ONLY the LATEST read Q18 fact (the machine's carried GHASH mid;
   store readbacks self-propagate), atomize it as `midacc`, and let the
   bridge expand it once. ---- *)
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
(* The per-step normalizer is GCM_SIMD_SIMPLIFY_CORE_TAC, NOT the double-pass
   GCM_SIMD_SIMPLIFY_TAC (= CORE THEN CORE).  The second CORE pass is a full
   RULE_ASSUM traversal of the whole carried GHASH pile; on the tail sim it is
   a no-op on 114/122 steps (it only folds the fresh REV64 byte-tree at the ~8
   block-boundary steps, and that fold is re-done downstream by the Q19
   bridge's WORD_BYTEREVERSE_REVERSEFIELDS/RF8_SUBWORD rewrites).  If a future
   edit needs the fixpoint here, restore GCM_SIMD_SIMPLIFY_TAC. *)
let ARM_STEPS_FOLD_Q18LATEST_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_CORE_TAC THEN
              DISCARD_STALE_Q18_TAC THEN DISCARD_OLDSTATE_KEEPQ18_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;
(* Merge variants that unfold karatsuba_mid inside the
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

(* Name-agnostic pairing of the leftover Karatsuba-mid qq atoms.  The per-step
   normalizer (GCM_SIMD_SIMPLIFY_CORE_TAC + EXT8_LANE0_IS_SUBWORD_HI) collapses
   the ext-form Karatsuba-mid lanes back to the ins-form lanes, but the qq
   numbers ABBREV_INNER_PMULS assigns are not stable across bands.  So this
   pairs the leftover mid pmuls by H-power (which keys off the KEY operand
   h2/h3/.., unaffected by the data-side ext form): after MERGE_ANY_TAC has
   merged everything it can, the only residual mismatch is a set of
   karatsuba-mid qq atoms UNIQUE to the LHS vs UNIQUE to the RHS; each
   LHS-unique qq merges with the RHS-unique qq of the SAME H-power
   (MERGE_QQPAIR_KM_TAC, closed by WORD_BLAST, so it is form-insensitive). *)
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

(* WB_7/WB_8 midacc bridges leave a stray zero limb in each 64-bit lane
   (from the carried mid entering the reduce as word 0 xor ...):
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

let GCM_CTR_INC3_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))`,
        subst [`word 3:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let _, GMULT4_FULL_CORRECT_BA = build_GMULTn_fast 4;;
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

let GCM_CTR_INC4_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))`,
        subst [`word 4:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let _, GMULT5_FULL_CORRECT_BA = build_GMULTn_fast 5;;
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

(* ============================================================================
   WB_6BLOCK machinery.  GHASH_POLYVAL_ACC_6 is proved here from
   GHASH_POLYVAL_ACC_BATCHED with the same recipe as the 3..5-block forms in
   common/ghash_nblock_karatsuba.ml.
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
let _, GMULT6_FULL_CORRECT_BA = build_GMULTn_fast 6;;
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

(* ============================================================================
   WB_7BLOCK machinery (ACC_7 proved from BATCHED like ACC_6 above).
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
let _, GMULT7_FULL_CORRECT_BA = build_GMULTn_fast 7;;
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

(* ============================================================================
   WB_8BLOCK machinery.

   MERGE NOTE: at N=8 the stock MERGE_2BLK_TAC mis-pairs the qq atoms -- its
   find_pair takes the FIRST signature-compatible candidate, and at N=8 that
   greedy choice pairs machine-lo with spec-hi atoms, leaving 4 unmergeable
   leftovers.  MERGE_ONE_ANY_TAC uses the same pairing signature but tries
   ALL candidate pairs via FIRST (backtracking on the WORD_BLAST operand
   close), so a bad greedy pick self-corrects.
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
let _, GMULT8_FULL_CORRECT_BA = build_GMULTn_fast 8;;
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
  (* === GHASH bridge at s341 (pc+4548, post eor v19,v19,v18) === *)
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
  (* 344 = st1 {v19.16b},[x3] (tag store); exit at pc+4560 *)
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
  (* s348 = st1 {v12.16b},[x2] (block-1 PT store).  Plain VSTEPS (the FOLD variant's
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
  (* === GMULT2 bridge at s355 (pc+4548, post eor v19,v19,v18) === *)
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
  (* 358 = st1 {v19.16b},[x3] (tag store); exit at pc+4560 *)
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
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN (* AUTO_MERGE below subsumes MERGE_ANY *)
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
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN (* AUTO_MERGE below subsumes MERGE_ANY *)
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
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN (* AUTO_MERGE below subsumes MERGE_ANY *)
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
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN (* AUTO_MERGE below subsumes MERGE_ANY *)
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
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN (* AUTO_MERGE below subsumes MERGE_ANY *)
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
     drain (.L256_dec_exact8_drain @0x11e8), NOT the shared 8-way cascade
     (which only the remainders r=1..7 reach).  The drain is the cascade's
     more_than_7 fall-through without its 14 no-ops (7x movi v16,#0 + 7x
     eor v8,v8,v16, all dead when every block feeds), plus one `b` rejoin to
     the common modulo at 0x1198: 13 fewer simulated steps than the cascade.
     The drain also eor3-FUSES the accumulate chains: 3 block-pairs
     (final-6,final-5)(final-4,final-3)(final-2,final-1) each defer the 1st
     block's 3 high/low/mid products to free regs v13/v14/v15, drop its 3
     pairwise accumulate eors, and fold them into the 2nd block's 3 accumulate
     eors via `eor3 acc,acc,prodB,prodA`: 9 fewer simulated steps again, all
     in the accumulate window.  XOR is assoc/comm, so the folded Q18/Q19 at
     the 0x1198 rejoin are byte-identical to the cascade's and the same
     byteform close applies.  RESOLVE (266--270) resolves the b.gt into the
     drain. *)
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
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN (* AUTO_MERGE below subsumes MERGE_ANY *)
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

let AND_MASK_16NBLK = prove
 (`!nblk. 1 <= nblk /\ nblk <= 8
        ==> word_and (word_sub (word (16 * nblk)) (word 1))
                     (word 18446744073709551488):int64 = word 0`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= n /\ n <= 8 <=>
    n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* ---- input-lane bridge (only needs READ_BYTES_AND_BYTE128_MERGE from
        aes_xts_common) ---------------------------------------------------- *)
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

(* ---- WB_FRONT_BUF construction --------------------------------------------
   The postcondition is the simulated front's s273 state (wb_front_postcond
   below, with its 8 in-flight 13-round keystream towers folded to aes13), built
   with term builders, so the front is simulated once, in the proof. ---- *)

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

(* 5<=nblk: WB_FRONT_BUF (built from this hyp set) is consumed only by
   prove_band 5..8 (bands 1..4 take the small-message path via the step-8
   b.le and are proved by the fused-band theorems).  The concrete bands supply
   nblk in {5,6,7,8} so 5<=nblk discharges by NUM_REDUCE; and the union-front
   derivation (wbn_front_hyps_uni_tm) already prepends 5<=nblk. *)
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

(* The s273 postcondition wb_front_postcond (below) is stated in COMPACT FORM:
   the 8 in-flight keystream towers are folded to aes13 (gcm_ctr_inc^i ctr0)
   k0..k13 (GSYM aes13 + GSYM GCM_CTR_INCi_LANES), which makes the Q-register
   conjuncts readable.  The WB_FRONT_BUF proof applies the same fold to the
   simulated assumptions (wb_front_fold_tac) before final-state matching. *)
let wb_ctr_lanes_thms =
  [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES;
   GCM_CTR_INC5_LANES; GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES];;
(* fold the raw simulated assumptions onto the compact postcondition shapes *)
let wb_front_fold_tac =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM aes13]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE(map GSYM wb_ctr_lanes_thms));;
(* the RAW counter accumulator kept in v30 (defined here so that the Q30
   conjunct of wb_front_postcond below can reference it).  byte-grouped rep with top 32-bit
   lane incremented by w.  The body's first instr `rev32 v5,v30` reads it, so the
   Sec-4 invariant pins Q30 = gcm_ctr_raw (word (8*i+13)) ctr0.  Its algebra
   lemmas (SUBW_RAW_*, GCM_CTR_RAW_INCR, REV32_FOLD_TAC) are body-only, Sec 9b.
   rev32(gcm_ctr_raw w ctr0) = gcm_ctr_add w ctr0 (the AES input for block w);
   word_add (gcm_ctr_raw w ctr0) (word 2^96) = gcm_ctr_raw (word_add w 1) ctr0.
   Like gcm_ctr_inc and gcm_ctr_add it is machine-level vocabulary, the
   register value the simulation produces, so it stays private; no exported
   statement mentions it. *)
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

(* ---- term builders for the simulated postconditions ------------------------
   wb_front_postcond (below), wbn_front_prebranch_postcond,
   wbn_front_prefix_postcond, wbn_front_postcond_i0 and wbn_prepretail_post_raw
   each describe the final state of a simulation (of the front, the shared
   prefix or the prepretail): the aligned_bytes_loaded fact and every
   `read _ sN = _` assumption (folded by wb_front_fold_tac), with sN abstracted
   to s, in the order the simulator leaves them.  They are built from the term
   families below. *)

(* h-power towers: dot j = polyval_dot^(j-1) over byteswap128 h *)
let rec hdot j = if j = 1 then `byteswap128 h`
  else mk_comb(mk_comb(`polyval_dot:int128->int128->int128`, hdot (j-1)), `byteswap128 h`);;
(* counter i: gcm_ctr_inc^i ctr0 *)
let mk_ctr i =
  let rec go n = if n = 0 then `ctr0:int128`
    else mk_comb(`gcm_ctr_inc`, go (n-1)) in go i;;
(* input block i as the 128-bit lane the kernel loads *)
let mk_cph i = subst [mk_small_numeral(16*i),`nnn:num`]
  `bytes_to_int128 (SUB_LIST (nnn,16) (ibytes:byte list))`;;

(* the conjunct `read c s = v`, and the postcondition \s. c1 /\ ... /\ cn *)
let wbp_rd c v = mk_eq(list_mk_icomb "read" [c; `s:armstate`], v);;
let wbp_post cs = mk_abs(`s:armstate`, list_mk_conj cs);;
(* the 13-round keystream tower aes13 ctr k0 .. k13 *)
let wbp_aes13 ctr =
  list_mk_comb(`aes13`, ctr :: map (fun i -> mk_var("k"^string_of_int i,`:int128`)) (0--13));;
(* htable_mem_dec slot values: H^j (h itself for j = 1), and the packed
   karatsuba mids of H^(j+1) and H^j *)
let wbp_hpow j = if j = 1 then `h:int128` else mk_comb(`byteswap128`, hdot j);;
let wbp_hmid j = mk_comb(mk_comb(`word_join:int64->int64->int128`,
  mk_comb(`karatsuba_mid`, wbp_hpow (j+1))), mk_comb(`karatsuba_mid`, wbp_hpow j));;
(* read (memory :> bytes128 (base + 16 * i)) s *)
let wbp_mem128 base i =
  let addr = if i = 0 then base
    else subst [base,`bbb:int64`; mk_small_numeral(16*i),`nnn:num`] `word_add bbb (word nnn):int64` in
  subst [addr,`aaa:int64`] `read (memory :> bytes128 (aaa:int64)) s:int128`;;
(* the key schedule k0 .. k14 and the 12 htable_mem_dec slots, as read from memory *)
let wbp_key_reads =
  map (fun i -> mk_eq(wbp_mem128 `key_p:int64` i, mk_var("k"^string_of_int i,`:int128`))) (0--14);;
let wbp_htable_reads =
  conjuncts(rhs(concl((REWRITE_CONV[htable_mem_dec] THENC TOP_DEPTH_CONV let_CONV)
    `htable_mem_dec h htbl_p s`)));;
(* NZCV after cmp a, #n and after cmp a, b *)
let wbp_cmpi_flags a n = map (subst [a,`aaa:int64`; mk_small_numeral n,`nnn:num`])
  [`read NF s <=> ival (word_sub aaa (word nnn):int64) < &0`;
   `read ZF s <=> val (word_sub aaa (word nnn):int64) = 0`;
   `read CF s <=> nnn <= val (aaa:int64)`;
   `read VF s <=> ~(ival (aaa:int64) - &nnn = ival (word_sub aaa (word nnn):int64))`];;
let wbp_cmp_flags a b = map (subst [a,`aaa:int64`; b,`bbb:int64`])
  [`read NF s <=> ival (word_sub aaa bbb:int64) < &0`;
   `read ZF s <=> val (word_sub aaa bbb:int64) = 0`;
   `read CF s <=> val (bbb:int64) <= val (aaa:int64)`;
   `read VF s <=> ~(ival (aaa:int64) - ival (bbb:int64) = ival (word_sub aaa bbb:int64))`];;
(* the raw counter words: wbp_bytes4 x [a;b;c;d] joins the bytes of x at bit
   offsets a, b, c, d; wbp_lane b is the 32-bit lane of ctr0 at bit b grouped as
   gcm_ctr_raw groups it, wbp_revlane b the same bytes in the opposite order *)
let wbp_bytes4 x offs =
  let byte k = mk_comb(mk_icomb(`word_subword:A word->num#num->8 word`, x),
                       mk_pair(mk_small_numeral k, `8`)) in
  let j16 a b = mk_comb(mk_comb(`word_join:8 word->8 word->16 word`, a), b)
  and j32 a b = mk_comb(mk_comb(`word_join:16 word->16 word->32 word`, a), b) in
  match map byte offs with
    [a;b;c;d] -> j32 (j16 a b) (j16 c d)
  | _ -> failwith "wbp_bytes4";;
let wbp_lane b = wbp_bytes4 `ctr0:int128` [b; b+8; b+16; b+24];;
let wbp_revlane b = wbp_bytes4 `ctr0:int128` [b+24; b+16; b+8; b];;
let wbp_add32 x n = mk_comb(mk_comb(`word_add:32 word->32 word->32 word`, x),
                            mk_comb(`word:num->32 word`, mk_small_numeral n));;
let wbp_join128 a b c d =
  let j64 x y = mk_comb(mk_comb(`word_join:32 word->32 word->64 word`, x), y) in
  mk_comb(mk_comb(`word_join:64 word->64 word->128 word`, j64 a b), j64 c d);;
(* v30 after the front's add v30 steps: top lane + w, then + 1; the other lanes + 0 *)
let wbp_raw_acc w =
  wbp_join128 (wbp_add32 (wbp_add32 (wbp_lane 96) w) 1) (wbp_add32 (wbp_lane 64) 0)
              (wbp_add32 (wbp_lane 32) 0) (wbp_add32 (wbp_lane 0) 0);;
(* rev32 of the raw counter with top lane + w: the AES input block for counter w *)
let wbp_rev_ctr w =
  wbp_join128 (wbp_bytes4 (wbp_add32 (wbp_lane 96) w) [0; 8; 16; 24])
              (wbp_revlane 64) (wbp_revlane 32) (wbp_revlane 0);;
(* the registers the prologue sets up for the whole kernel (Q19 holds xi reversed) *)
let wbp_ctx xi =
  [`read X16 s = ivec_p`;
   `read X10 s = word_add stackpointer (word 64)`;
   `read X15 s = word 4294967296`;
   `read Q31 s = word 79228162514264337593543950336`;
   wbp_rd `Q19` (mk_comb(`word_bytereverse:int128->int128`, xi));
   `read X4 s = word_add in_p (word (16 * nblk))`;
   `read Q27 s = k13`;
   `read Q26 s = k12`;
   `read Q28 s = k14`];;
(* decrypted block i, word_xor (word_xor cph_i (aes13 ctr_i k0..k13)) k14, and its store *)
let wbp_pt i = mk_comb(mk_comb(`word_xor:int128->int128->int128`,
  mk_comb(mk_comb(`word_xor:int128->int128->int128`, mk_cph i), wbp_aes13 (mk_ctr i))), `k14:int128`);;
let wbp_out i = mk_eq(wbp_mem128 `out_p:int64` i, wbp_pt i);;

let wb_front_postcond = wbp_post
 ([`aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
   `read PC s = word (pc + 3828)`;
   wbp_rd `Q24` (wbp_hmid 7);
   wbp_rd `Q25` (wbp_hpow 8)] @
  wbp_cmpi_flags `word (16 * nblk):int64` 112 @
  [`read Q16 s = word_subword (word_join (word_bytereverse (xi:int128)) (word_bytereverse xi):256 word) (64,128)`;
   wbp_rd `Q7` (wbp_aes13 (mk_ctr 7));
   wbp_rd `Q6` (wbp_aes13 (mk_ctr 6));
   wbp_rd `Q0` (wbp_aes13 (mk_ctr 0));
   wbp_rd `Q1` (wbp_aes13 (mk_ctr 1));
   `read (memory :> bytes64 (word_add stackpointer (word 64))) s = word 13979173243358019584`;
   `read (memory :> bytes64 (word_add stackpointer (word 72))) s = word 0`;
   `read X11 s = key_p`;
   `read X9 s = word (16 * nblk)`;
   `read SP s = stackpointer`;
   `read X1 s = word (128 * nblk)`;
   `read X2 s = out_p`;
   `read X3 s = xi_p`;
   `read X6 s = htbl_p`;
   `read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes`;
   `read (memory :> bytes128 xi_p) s = xi`;
   `read (memory :> bytes128 ivec_p) s = ctr0`] @
  wbp_key_reads @ wbp_htable_reads @
  [mk_eq(wbp_mem128 `in_p:int64` 0, mk_cph 0)] @ wbp_ctx `xi:int128` @
  [wbp_rd `Q5` (wbp_aes13 (mk_ctr 5));
   wbp_rd `Q2` (wbp_aes13 (mk_ctr 2));
   wbp_rd `Q4` (wbp_aes13 (mk_ctr 4));
   wbp_rd `Q3` (wbp_aes13 (mk_ctr 3));
   `read X5 s = word (16 * nblk)`;
   `read X0 s = word_add in_p (word 16)`;
   wbp_rd `Q9` (mk_cph 0)]);;

(* The front postcondition also carries the advanced raw counter Q30, so the
   <=8 DISPATCH bands and the shared WB_TAIL_GEN2_r (which prove FROM
   q_at k = this postcond) see Q30 concretely and can fold the ivec store.
   The front sets v30 to the reversed counter base + 7 (CTR block 7) and later
   adds 1, so at the tail seam s273 (0x44c b.ge TAKEN for nblk<=8)
   Q30 = gcm_ctr_raw (word 8) ctr0: the simulated top lane is
   word_add (word_add (ctr0 top bytes) (word 7)) (word 1). *)
let wb_front_postcond = mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs wb_front_postcond),
            `read Q30 (s:armstate) = gcm_ctr_raw (word 8) ctr0`));;

(* ========================================================================= *)
(* The SHARED FRONT PREFIX (0x20 -> 0x44c),                                    *)
(* simulated ONCE across the <=8 front (WB_FRONT_BUF) AND the >=9 front        *)
(* (WBN_FRONT_PREFIX).  Extends the shared-prefix idiom by splitting at        *)
(* the EARLIER 0x44c b.ge (step 268) instead of 0x4bc (step 296): steps 1..267 *)
(* (entry 0x20 -> the 0x44c b.ge, straight-line for nblk >= 5 after resolving *)
(* the small-message branch, with only round-key/counter loads and NO          *)
(* input-block reads) is byte-identical work in BOTH bands, so we              *)
(* factor them into WBN_FRONT_PREBRANCH proved ONCE on the UNION band         *)
(* (5<=nblk /\ 128*nblk<2^64), keeping X5 general via the _ANY mask and KEEPING *)
(* the raw NF/VF/ZF/CF pre-branch flag facts.  Each consumer then chains a     *)
(* short post-branch leg via ENSURES_TRANS_SIMPLE (WB_FRONT_BUF: 0x44c TAKEN   *)
(* in the <=8 band -> 6 steps 268..273 to s273; WBN_FRONT_PREFIX: 0x44c FALLS  *)
(* THROUGH in the >=9 band -> 28 steps 268..295 to s295).  Both consumer       *)
(* STATEMENTS stay bit-identical.                                             *)
(* The helpers below (state_num_of_read_q30/DISCARD_STALE_Q30_TAC and the _ANY *)
(* mask lemmas) also serve the >=9/916 front code later in the file.           *)
(* ------------------------------------------------------------------------- *)

(* keep only the latest read Q30 fact *)
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

(* _ANY scalar rungs (nblk-general USHR/AND-mask; pure word/arith) *)
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

(* d = 128*((nblk-1)DIV8) = 0 for 1<=nblk<=8 (the <=8 band takes the 0x44c b.ge) *)
let D_ZERO_LE8 = prove
 (`!nblk. 1 <= nblk /\ nblk <= 8 ==> 128 * ((nblk - 1) DIV 8) = 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(nblk - 1) DIV 8 = 0` (fun th -> REWRITE_TAC[th; MULT_CLAUSES]) THEN
  MATCH_MP_TAC DIV_LT THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The early guard                                                          *)
(*   cmp x9,#0x40 ; b.le L256_dec_w5r_small                                    *)
(* at 0x38 (front-sim steps 7,8; x9 = word(16*nblk) from `lsr x9,x1,#3`).      *)
(* For the union front (nblk>=5) the b.le FALLS THROUGH (16*nblk>=80>64), so   *)
(* the small-message path is skipped.  The nblk<=4 case takes the b.le into    *)
(* the small-message region and is proved by the four fused-band theorems.    *)
(*                                                                             *)
(* GUARD_LE_FALLTHRU resolves the b.le for 5<=nblk (pure arithmetic on         *)
(* word(16*nblk); no pointer facts).  Usage in the steppers: discharge it     *)
(* into the assumptions BEFORE ARM_STEPS_TAC (7--8) so the stepper folds the  *)
(* branch.                                                                     *)
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
   (wbn_front_hyps_ge9_tm) PLUS 5<=nblk PLUS 128*nblk<2^64.  Both bands imply it.
   The guard b.le at step 8 falls through only for nblk>=5, so every consumer
   of the union front (readable bands 5..8 via WB_FRONT_BUF; the nblk>=9
   chain) is on the 5<=nblk side; nblk in {1,2,3,4} takes the small-message
   path and is proved by the fused bands.
   GUARD_LE_FALLTHRU discharges the guard from 5<=nblk (+ 16*nblk<2^63, which
   follows from the 128*nblk<2^64 conjunct here). *)
let wbn_front_hyps_uni_tm =
  let cs8 = conjuncts wb_front_hyps_tm in
  end_itlist (curry mk_conj)
    (`5 <= nblk`::`128 * nblk < 2 EXP 64`::
     (filter (fun c -> not(c = `5 <= nblk` || c = `1 <= nblk` || c = `nblk <= 8`)) cs8));;

(* The union hyps carry `5 <= nblk` and filter out `1 <= nblk`
   (wbn_front_hyps_uni_tm above), so `ASSUME `1 <= nblk`` would introduce a
   hypothesis absent from the goal, and the enclosing SUBGOAL_THEN's
   justification would fail with `Failure "ABS"`.  Use `5 <= nblk` (present):
   it implies every bound `1 <= nblk` supplied to USHR_128NBLK_ANY /
   AND_MASK_16NBLK_ANY / INPUT_BYTES_TO_BYTE128_LANES via ARITH. *)
let NBLK_ARITH_UNI_TAC =
  MP_TAC(ASSUME `5 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN
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

(* the shared prefix steps 1..267 (entry 0x20 -> the 0x44c b.ge at pc+1100);
   stops BEFORE the band-dependent 0x44c branch so X5 stays general.
   The counter setup uses the parallel depth-2 form (all counter SIMD first,
   then AES round-0/1), inside the per-step GCM_SIMD_SIMPLIFY loop 9--43.
   The guard `cmp x9,#0x40 ; b.le` is steps 7,8 (entry 0x20 = step 1;
   step 6 = add x10 @0x34; the first vector op ld1 @0x40 is step 9).  The
   b.le FALLS THROUGH for the union band nblk>=5 (16*nblk>=80>64), resolved
   by GUARD_LE_FALLTHRU discharged into the asms BEFORE stepping 7--8 so the
   stepper folds the branch to fall-through. *)
let WBN_FRONT_PREBRANCH_STEPS_TAC =
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
  (* 186-197 is the GHASH REV64 window (Q19 byte-tree fold).
     ARM_STEPS_FOLD_DISCARD_TAC folds Q19 BEFORE discarding old states each
     step, so the pile stays flat; no store read-back is needed in this
     window, so the per-step discard is safe. *)
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (186--197) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[Q19_BREVXI]) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (198--262) THEN
  DISCARD_STALE_Q30_TAC THEN GCM_SIMD_SIMPLIFY_TAC THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [263] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (264--267);;

let WBN_FRONT_PREBRANCH_TAC = wbn_init_uni_tac THEN WBN_FRONT_PREBRANCH_STEPS_TAC;;

(* prefix goal builder (union band, postcond @ PC 0x44c = pc+1100) *)
let mk_wbn_prebranch_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_uni_tm, ens));;

(* The pre-branch postcondition is the s267 state at the 0x44c b.ge, so the shared
   prefix simulates ONCE.  X5 is the general word_add(word(128*((nblk-1)DIV8)))in_p
   and ALL raw NF/VF/ZF/CF flag facts are KEPT (each consumer's post-branch leg
   resolves the branch in its band).  Built like wb_front_postcond above, as the
   final state of WBN_FRONT_PREBRANCH_TAC THEN wb_front_fold_tac. *)
let wbn_front_prebranch_postcond = wbp_post
 ([`aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
   `read PC s = word (pc + 1100)`;
   wbp_rd `Q7` (wbp_aes13 (mk_ctr 7));
   wbp_rd `Q6` (wbp_aes13 (mk_ctr 6));
   wbp_rd `Q0` (wbp_aes13 (mk_ctr 0));
   wbp_rd `Q1` (wbp_aes13 (mk_ctr 1))] @
  wbp_cmp_flags `in_p:int64` `word_add (word (128 * (nblk - 1) DIV 8)) in_p:int64` @
  [wbp_rd `Q30` (wbp_raw_acc 7);
   `read X5 s = word_add (word (128 * (nblk - 1) DIV 8)) in_p`;
   `read (memory :> bytes64 (word_add stackpointer (word 64))) s = word 13979173243358019584`;
   `read (memory :> bytes64 (word_add stackpointer (word 72))) s = word 0`;
   `read X11 s = key_p`;
   `read X9 s = word (16 * nblk)`;
   `read SP s = stackpointer`;
   `read X0 s = in_p`;
   `read X1 s = word (128 * nblk)`;
   `read X2 s = out_p`;
   `read X3 s = xi_p`;
   `read X6 s = htbl_p`;
   `read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes`;
   `read (memory :> bytes128 xi_p) s = xi`;
   `read (memory :> bytes128 ivec_p) s = ctr0`] @
  wbp_key_reads @ wbp_htable_reads @
  [mk_eq(wbp_mem128 `in_p:int64` 0, mk_cph 0)] @ wbp_ctx `xi:int128` @
  [wbp_rd `Q5` (wbp_aes13 (mk_ctr 5));
   wbp_rd `Q2` (wbp_aes13 (mk_ctr 2));
   wbp_rd `Q4` (wbp_aes13 (mk_ctr 4));
   wbp_rd `Q3` (wbp_aes13 (mk_ctr 3))]);;

(* THE SHARED PRE-BRANCH PREFIX LEMMA (proved ONCE; ~225s sim). *)
let WBN_FRONT_PREBRANCH = prove(mk_wbn_prebranch_goal wbn_front_prebranch_postcond,
  WBN_FRONT_PREBRANCH_TAC THEN wb_front_fold_tac THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC);;

(* ivec: the front sets v30 to the reversed counter base + 7 and later adds 1,
   so Q30's top lane is word_add(word_add(...)(word 7))(word 1); this folds the
   +7+1 to +8 so the raw tower matches the gcm_ctr_raw (word 8) ctr0 literal.
   A precomputed `let` value: inlining the WORD_RULE in the tactic fails with
   "RAND_CONV: Not a combination". *)
let WB_FRONT_Q30_TOPLANE = WORD_RULE
  `word_add (word_add (x:32 word) (word 7)) (word 1) = word_add x (word 8)`;;

(* THE SHARED FRONT LEMMA (5<=nblk<=8 band): chain WBN_FRONT_PREBRANCH
   (0x20->0x44c) via ENSURES_TRANS_SIMPLE, then the 0x44c b.ge TAKEN (d=0 for
   nblk<=8 => X5=in_p => reflexive compare) + 6 steps 268..273 to s273 (pc+3828).
   Consumed only by prove_band 5..8; nblk<=4 takes the small-message path. *)
let WB_FRONT_BUF = prove(mk_wb_front_goal wb_front_postcond,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_front_prebranch_postcond THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_PREBRANCH THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ENSURES_INIT_TAC "s267" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `nblk:num` D_ZERO_LE8)
       (CONJ (MATCH_MP (ARITH_RULE `5 <= nblk ==> 1 <= nblk`) (ASSUME `5 <= nblk`))
             (ASSUME `nblk <= 8`))]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
    SUBGOAL_THEN `ival (in_p:int64) - ival in_p = &0` ASSUME_TAC THENL
     [CONV_TAC INT_ARITH; ALL_TAC] THEN
    (* Split the batched (268--273) into (268--272)+(273--273): s273
       (=ldp q24,q25,[x6,#160]) forces a per-step normalization that batched
       ARM_STEPS_TAC defers, raising "RAND_CONV: Not a combination";
       single-stepping s273 avoids it. *)
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (268--272) THEN
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (273--273) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
      `word_sub (word_add in_p (word (16 * nblk))) in_p:int64 = word (16 * nblk)`]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WB_FRONT_Q30_TOPLANE] THEN REWRITE_TAC[gcm_ctr_raw_def] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]);;
(* --- mid-load heap compaction: bound GC cost across this large single-file *)
(*     load (after a front-BUF sim)). --- *)
Gc.compact();;

(* ---- buffer-form band statements ------------------------------------------ *)
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

(* The band-exit counter write-back conjunct, spine form
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
  let x9_post = subst [n16,`sss:num`] `read X9 s = word sss` in
  let outs = map mk_out_conj (0--(k-1)) in
  let xi_post = subst [mk_ghash_list k,`lll:int128 list`]
    `read (memory :> bytes128 xi_p) s =
     word_bytereverse
       (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi) (lll:int128 list))` in
  (* The counter write-back at band exit r.  Spine form
     gcm_ctr_inc_iter r ctr0 (= gcm_ctr_add (word r) ctr0); closed by
     WB_IVEC_CLOSE_TAC r in each WB_TAIL_r_TAC. *)
  let ivec_post = mk_ivec_conj k in
  let post = mk_abs(`s:armstate`,
    end_itlist (curry mk_conj) (pc_post :: x9_post :: outs @ [xi_post; ivec_post])) in
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
  CLEAR_KEEPGH_MEMO_TAC THEN  (* reset the KEEPGH normalizer fixpoint cache per tail body *)
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s265" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  lanes THEN cphs THEN habbrevs;;

(* ========================================================================= *)
(* The shared per-block back-leg, proved ONCE.                                *)
(*                                                                            *)
(* The back-leg sim `WB_PREP_TAC k THEN WB_TAIL_k_TAC` (init@s265 -> whole-   *)
(* function exit pc+4560) is proved once per k as WB_TAIL_GEN2_k, from a      *)
(* strictly WEAKER precond than prove_band's (q_at k minus 5 objdump-dead     *)
(* cells).  Both goals share IDENTICAL post + frame (both via mk_band_goal    *)
(* k), so the weak-precond back-leg implies the full-precond one by           *)
(* conjunct-drop weakening (ENSURES_PRECONDITION_THM, no re-simulation), and  *)
(* WB_TAIL_GEN2_k serves both prove_band (below) and the nblk>8               *)
(* recomposition (WBN_PREP_TO_END, later).                                     *)
(*                                                                            *)
(* The 5 dropped cells (sp+72, xi_p, ivec_p, in_p block-0, X1) are            *)
(* objdump-confirmed never read by the tail range [0xef4,0x11d0).  X9 is also *)
(* unread, but is retained generically as `return_value` so the proof records *)
(* that the byte count survives to the epilogue's `mov x0,x9`.  Each          *)
(* WB_TAIL_GEN2_k proving hyps=0 is the in-proof audit of both facts.          *)
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

(* Replace the fixed per-band X9 count with a generic value.  The residual    *)
(* tail is shared by fixed bands (return_value = 16*r) and shifted whole-call *)
(* tails (return_value = 16*nblk), and it does not write X9.                  *)
let wbn_replace_x9 value pred =
  let sv, body = dest_abs pred in
  let x9lhs = subst [sv,`s:armstate`] `read X9 s` in
  let cs = conjuncts body in
  let cs' = map (fun c ->
    if is_eq c && lhs c = x9lhs then mk_eq(x9lhs,value) else c) cs in
  mk_abs(sv, end_itlist (curry mk_conj) cs');;

(* 5-cell drop: the 4 memory cells plus dead X1; X9 stays in the contract.    *)
let wbn_tail_drop_lhs5 = wbn_tail_drop_lhs @ [`read X1 (s:armstate)`];;
let wbn_weak_q_at5_return k return_value =
  let cs = conjuncts (snd(dest_abs (q_at k))) in
  let kept = filter (fun c -> not (is_eq c && mem (lhs c) wbn_tail_drop_lhs5)) cs in
  wbn_replace_x9 return_value
    (mk_abs(`s:armstate`, end_itlist (curry mk_conj) kept));;
let wbn_band_return k =
  subst [mk_small_numeral(16*k),`sss:num`] `word sss:int64`;;
let wbn_weak_q_at5 k = wbn_weak_q_at5_return k (wbn_band_return k);;
let wbn_tail_backleg_goal5_return r =
  let (vars, hyps, pre0, post, frame) = wbn_dissect_band r in
  ignore pre0;
  let return_value = `return_value:int64` in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_weak_q_at5_return r return_value;
     wbn_replace_x9 return_value post;
     frame]) in
  list_mk_forall(vars @ [return_value], mk_imp(hyps, ens));;
(* ======================================================================= *)
(* The counter algebra (gcm_ctr_add, GCM_CTR_ADD_LANES, GCM_CTR_INC_ITER_AS_ADD, *)
(* the SUBW_RAW lemmas) comes here so that WB_IVEC_CLOSE_TAC's deps are in     *)
(* scope for the band tail ivec close below; gcm_ctr_raw_def is defined        *)
(* before wb_front_postcond.                                                   *)
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
   GCM_CTR_INC_LANES with `w` for `word 1` (exactly the Q-lane shape the
   front simulation produces); proof is pure rewriting *)
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
let GCM_CTR_INC_ITER_AS_ADD = prove
 (`!k x:int128. gcm_ctr_inc_iter k x = gcm_ctr_add (word k) x`,
  INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[gcm_ctr_inc_iter; GCM_CTR_ADD_0];
    ASM_REWRITE_TAC[gcm_ctr_inc_iter] THEN
    REWRITE_TAC[GSYM GCM_CTR_ADD_1; GCM_CTR_ADD_COMPOSE] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[ADD1; GSYM WORD_ADD] THEN
    CONV_TAC WORD_RULE]);;

(* the 4 lane-extraction lemmas (used to prove GCM_CTR_RAW_INCR without a
   symbolic-w WORD_BLAST, which OOMs -- see the Sec 2 OOM WARNING).  Each proves fast
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
(* The band-tail ivec write-back closer.                                      *)
(*                                                                            *)
(* Each band r stores rev32(v30) to [ivec_p] (str q30,[x16] at                *)
(* L256_dec_blocks_less_than_1 in the cascade, or in L256_dec_exact8_drain).  *)
(* With Q30 = gcm_ctr_raw (word 8) ctr0 carried in from the                   *)
(* front postcond, the store value is Q30 after (8-r) `sub v30`               *)
(* decrements -- gcm_ctr_raw (word 8) minus (8-r) = gcm_ctr_raw (word r), and *)
(* rev32 of that = gcm_ctr_add (word r) = gcm_ctr_inc_iter r ctr0.  The close  *)
(* runs entirely in 32-bit-lane algebra (SUBW_RAW_* pins the sub cascade to   *)
(* the top lane; GCM_CTR_ADD_LANES gives the rev target) so no 128-bit blast  *)
(* meets the symbolic counter.                                               *)
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
  REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD] THEN
  REWRITE_TAC[sub_chain 1 (8-r); sub_chain 0 (8-r)] THEN
  REWRITE_TAC[gcm_ctr_raw_def; SUBW_RAW_96; SUBW_RAW_64; SUBW_RAW_32; SUBW_RAW_0] THEN
  REWRITE_TAC[SUBW_NORM r; WORD_SUB_0] THEN
  GEN_REWRITE_TAC RAND_CONV [GCM_CTR_ADD_LANES] THEN
  W(fun (_,gw) ->
     let atom = find_term (fun t -> match t with
       | Comb(Comb(Const("word_add",_),_),Comb(Const("word",_),_)) -> true | _ -> false) gw in
     SPEC_TAC(atom, `aa:32 word`)) THEN
  GEN_TAC THEN CONV_TAC WORD_BLAST;;

(* The 8 shared back-legs -- the ONLY per-block tail sims in the file.        *)
(* Each ~130-315s; each hyps=0 audits dead X1 and generic X9 preservation.    *)
let WB_TAIL_GEN2_1 = prove(wbn_tail_backleg_goal5_return 1,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 1 THEN WB_TAIL_1_TAC (WB_IVEC_CLOSE_TAC 1));;
let WB_TAIL_GEN2_2 = prove(wbn_tail_backleg_goal5_return 2,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 2 THEN WB_TAIL_2_TAC (WB_IVEC_CLOSE_TAC 2));;
let WB_TAIL_GEN2_3 = prove(wbn_tail_backleg_goal5_return 3,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 3 THEN WB_TAIL_3_TAC (WB_IVEC_CLOSE_TAC 3));;
let WB_TAIL_GEN2_4 = prove(wbn_tail_backleg_goal5_return 4,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 4 THEN WB_TAIL_4_TAC (WB_IVEC_CLOSE_TAC 4));;
let WB_TAIL_GEN2_5 = prove(wbn_tail_backleg_goal5_return 5,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 5 THEN WB_TAIL_5_TAC (WB_IVEC_CLOSE_TAC 5));;
let WB_TAIL_GEN2_6 = prove(wbn_tail_backleg_goal5_return 6,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 6 THEN WB_TAIL_6_TAC (WB_IVEC_CLOSE_TAC 6));;
let WB_TAIL_GEN2_7 = prove(wbn_tail_backleg_goal5_return 7,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 7 THEN WB_TAIL_7_TAC (WB_IVEC_CLOSE_TAC 7));;
let WB_TAIL_GEN2_8 = prove(wbn_tail_backleg_goal5_return 8,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 8 THEN WB_TAIL_8_TAC (WB_IVEC_CLOSE_TAC 8));;
(* --- mid-load heap compaction: bound GC cost after the 8 shared back-leg    *)
(*     sims (the file's heaviest per-block work). *)
Gc.compact();;

(* The band prover: split at pc+3828 via FRAME_SUBSUMED + TRANS
   (ENSURES_SEQUENCE_TAC throws MAYCHANGE_IDEMPOT on this frame), discharge
   the front leg with WB_FRONT_BUF; the back leg is then DISCHARGED (not
   re-simulated) from the pre-proved WB_TAIL_GEN2_k by precondition-weakening
   (q_at k ==> the 5-cell-dropped weak precond), the same ENSURES_PRECONDITION
   idiom used for the shifted tail feed later in the file. *)

(* >>> SMALL-MESSAGE (FUSED) ARC BEGIN <<< *)
(* ========================================================================= *)
(* The small-message path (nblk <= 4, entered by the step-8 b.le into         *)
(* L256_dec_w5r_small): the 4 fused block proofs WB_FUSED_kBLOCK (k=1..4)     *)
(* and the raw->band bridge.  BUF_{1..4}BLOCK are derived from them via       *)
(* ENSURES_PRECONDITION_THM (no re-sim), giving exactly mk_band_goal k for    *)
(* bands 1..4 (the prove_band route needs 5<=nblk).                           *)
(* ========================================================================= *)

(* ---- shared tactic library for the fused small-path arc:
     DISCARD_OLDSTATE_KEEPGHALL_TAC, ARM_STEPS_FOLD_KEEPGHALL_TAC,
     JOIN_IS_CTR0, INLINE_SELFCONTAINED, POLYVAL_DOT_SYM. ---- *)

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

(* ---- Q-scoped, FIXPOINT-MEMOIZED per-step SIMD normalizer ----
   Same three rewrite passes as the shared GCM_SIMD_SIMPLIFY_CORE_TAC (lemmas.ml),
   but applied ONLY to `read Qn s = ...` assumptions.  In the KEEPGHALL windows
   the discard KEEPS the full multi-block GHASH accumulator history, so the pile
   grows to ~400-1000 assumptions of which ~215 are memory reads, ~22
   nonoverlapping and the rest non-Q / flags -- none of which the SIMD rules (REV64 lanes
   / WORD_SWAP_HALVES / EXT8_LANE0 / REV32_LANE_SUBWORD) can EVER rewrite.  The Q-scope
   skips those, and the surviving Q-reads are mostly already at a fixpoint of the
   normalizer F.  F's action on an assumption is a PURE function of its conclusion,
   so if F once left a conclusion unchanged it always will.  Memoize the set of concl
   terms already proven to be F-fixpoints (`gcm_simd_fixpt_tbl`): for each Q-read asm,
   if its concl is a known fixpoint skip it (GUARANTEED no-op); else apply F and, if F
   leaves it unchanged, record the fixpoint.  This is BIT-IDENTICAL to always applying
   the Q-scoped F (skipping a proven fixpoint yields exactly F's output) -- it satisfies
   the soundness invariant WITHOUT any current-state approximation.  The table
   accumulates across the 4 fused bodies (CLEAR_KEEPGHALL_MEMO_TAC resets it at each
   body start so every WB_FUSED_kBLOCK `prove` is hermetic); a stale fixpoint could only
   ever be a genuine no-op anyway, so carryover would also be bit-identical.
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

(* DISCARD_STALE_TAC, used by the stepper below, is the shared one in
   arm/proofs/utils/aes_gcm_common.ml. *)

(* ---- per-window symbolic-execution stepper ----
   MAP_EVERY over the step range: verbose-step, single-pass Q-scoped GCM_SIMD
   normalizer (a second CORE pass is a no-op except on block-boundary REV64
   folds, which the bridge re-does downstream via RF8_SUBWORD), keep-GHALL
   discard, clarify. *)
let ARM_STEPS_FOLD_KEEPGHALL_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_CORE_QSCOPED_TAC THEN
              DISCARD_OLDSTATE_KEEPGHALL_TAC s THEN DISCARD_STALE_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;

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

(* ---- DEC_BRIDGE_ROUTEB_TAC: the parameterised bridge close for k>=2 ----
   For k>=2 the per-k bridge closes (BRIDGE_CLOSE_{2,3,4}_CPH*_TAC, thin wrappers
   below) share one prelude + finisher and differ ONLY in the spec-equation `spec_eq` and the
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

(* ==== k=1 fused body ==== *)
(* WB_FUSED_1BLOCK (nblk=1 small-message path).  Store tail = split bytes128
   readbacks to bytes64 halves before ENSURES_FINAL, then per-half
   AP_THM_TAC;AP_TERM_TAC + closer (out=JOIN_IS_CTR0+aes+WORD_RULE,
   xi=polyval_dot-def SUBST+GHASH_1BLOCK_CORRECT, ivec=GCM_CTR_INC_LANES,
   MAYCHANGE=MONOTONE). *)

(* ---- prelude: the folds + bridge close ---- *)
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

(* Lane-split close for the k=1 fused bridge (a monolithic 128-bit WORD_BLAST
   over the word_pmul goal is far slower).  Same shape the k>=2 bridges close via
   DEC_BRIDGE_ROUTEB_TAC's LANE_FINISH_TAC / JOIN_EQ_SPLIT: unify the two `word_pmul`
   towers (PMUL_CONG_128 on their 128-bit operands), then split the residual 128-bit
   word_join equality into two 64-bit lanes (QQ0SPLIT + JOIN_EQ_SPLIT) and blast each
   lane at 64-bit width. *)
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
          read X9 s = word 16 /\
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
  CLEAR_KEEPGHALL_MEMO_TAC THEN  (* reset the fused normalizer fixpoint cache *)
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
     assumption. gval is LIVE and stays live through ENSURES_FINAL. *)
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

(* ==== k=2 fused body ==== *)
(* WB_FUSED_2BLOCK (k=2).  Two sim details:
     (1) address normalization after the hk UNSPLIT so the block-0 x H^2 folded-key load
         `ldr d25,[x6,#24]` (spelled word_add htbl_p (word 24)) resolves against the UNSPLIT
         high-half fact (spelled word_add (word_add htbl_p (word 16)) (word 8)); without it
         the Q18 accumulator dangles on read(bytes64 htbl_p+24) and DISCARD drops it
         (k=1 never needs +24; k>=2 block0 x H^2 does);
     (2) INLINE_SELFCONTAINED Q17/Q18/Q19 at s81 (iterated REWRITE_RULE picks) BEFORE
         DISCARD_OLDSTATE "s81" -- collapses the block-0 accumulator chain so DISCARD keeps it.
   The bridge (BRIDGE_CLOSE_2_CPH1_TAC) also needs the block-0 (H^2) karatsuba-mid
   distribution qq8 = qq1 XOR qq5 (one machine pmul = XOR of two spec pmuls that
   MERGE_2BLK does not combine), passed to DEC_BRIDGE_ROUTEB_TAC below. *)

(* GMULT2_FULL_CORRECT_BA comes from aesv8_gcm_8x_dec_256_lemmas.ml. *)
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

(* BRIDGE_CLOSE_2_CPH1_TAC: nblk=2, cph1 specl.  Thin wrapper over the
   shared DEC_BRIDGE_ROUTEB_TAC; builds spec_eq from the k=2-local
   spec_to_byteform_2 / dec_bridge_specl_2_cph1 / GMULT2_FULL_CORRECT_BA, and passes the k=2
   block-0 (H^2) karatsuba-mid distributions: qq8=qq1(+)qq5 (hi), qq7=qq0(+)qq4 (lo),
   qq12=qq9(+)qq10 (mid). *)
let BRIDGE_CLOSE_2_CPH1_TAC sN : tactic = fun (asl,w) ->
  let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
  let gmult_dec = REWRITE_RULE[LET_DEF;LET_END_DEF] (SPECL dec_bridge_specl_2_cph1 GMULT2_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform_2 h2asm) (GSYM gmult_dec) in
  DEC_BRIDGE_ROUTEB_TAC sN spec_eq
    (("qq8","qq1","qq5"),("qq7","qq0","qq4"),("qq12","qq9","qq10")) (asl,w);;

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
          read X9 s = word 32 /\
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
  CLEAR_KEEPGHALL_MEMO_TAC THEN  (* reset the fused normalizer fixpoint cache *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 16))) s0`
        with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN
          STRIP_TAC)
    else NO_TAC) THEN
  (* sim detail (1): normalize hk-high address so ldr d25,[x6,#24] resolves *)
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
  (* sim detail (2): collapse the block-0 accumulator chain self-contained at s81 *)
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
  [BRIDGE_CLOSE_2_CPH1_TAC 128;   (* bridge: needs the block-0 mid distribution (see header) *)
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
     (out_p+16)+8 = out_p+24 (the same address-spelling issue as the k=2 hk+24 load). *)
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

(* ==== k=3 fused body ==== *)
(* WB_FUSED_3BLOCK (k=3).  Same route as k=2; the bridge uses the same three
   block-0 (H^3) mid distributions as k=2, index-shifted (qq11=qq1 XOR qq7,
   qq10=qq0 XOR qq6, qq16=qq12 XOR qq13); ABBREV_INNER_PMULS folds the
   block1 x H^2 mid combined.

   htable: htbl+0=h,+16=hk,+32=h2,+48=h3,+64=h3k.
   hk=[fold(h)@16, fold(h2)@24]; h3k=[fold(h3)@64, fold(h4)@72]. k=3 reads fold(h)@16,
   fold(h2)@24 (needs +24 norm), fold(h3)@64. UNSPLIT hk@16 AND h3k@64.
   SIM windows: (1--30); g3/blk0 KEEPGHALL (31--80),pt0@s80; g2/blk1 (81--123),pt1@s123;
   g1/blk2+reduce (124--170), bridge s170. Tail s170->s183: xi@s177,ivec@s180,pt2@s182. *)

(* The MAYCHANGE goal after the full fused SIM: the accumulated k=3 frame is
   aconv-identical to a term whose `frame subsumed goal` closes in seconds in a
   clean environment, but SUBSUMED_MAYCHANGE_TAC is very slow after the SIM.
   So prove the exact subsumption as a lemma here, BEFORE the SIM, and at the
   MAYCHANGE goal apply it via the pre-computed direct implication
   WB3_FRAME_IMP (MATCH_MP + ETA + ACCEPT), never re-running SUBSUMED post-SIM.
   Pure frame algebra, no fused-arc dependencies. *)

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

(* Pre-compute the DIRECT implication `frame s0 s183 ==> goal s0 s183` (before the SIM):
   REWRITE_RULE[subsumed] turns `frame subsumed goal` into `!x y. frame x y ==> goal x y`, then
   SPECL to the real states s0/s183.  RHS has NO eta-redex (goal applied directly), so the fused
   proof closes with a single MATCH_MP+ACCEPT -- no REWRITE[ETA_AX] traversal (slow post-SIM). *)
let WB3_FRAME_IMP =
  SPECL [`s0:armstate`; `s183:armstate`] (REWRITE_RULE[subsumed] WB3_FRAME_SUBSUMED);;

(* spec_to_byteform_wb3 is the one defined earlier in this file. *)

(* cph2 last-block specl (mirror k=2's dec_bridge_specl_2_cph1) *)
let dec_bridge_specl_3_cph2 =
  [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h3:int128`;
   `word_bytereverse cph1:int128`; `byteswap128 h2:int128`;
   `word_bytereverse cph2:int128`; `byteswap128 h:int128`];;

(* BRIDGE_CLOSE_3_CPH2_TAC: nblk=3, last block cph2.  Thin wrapper over the
   shared DEC_BRIDGE_ROUTEB_TAC; the 3 block-0(H^3) mid distributions:
   qq11=qq1(+)qq7 (hi), qq10=qq0(+)qq6 (lo), qq16=qq12(+)qq13 (mid). *)
let BRIDGE_CLOSE_3_CPH2_TAC sN : tactic = fun (asl,w) ->
  let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
  let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
  let gmult_dec = REWRITE_RULE[LET_DEF;LET_END_DEF] (SPECL dec_bridge_specl_3_cph2 GMULT3_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform_wb3 (CONJ h2asm h3asm)) (GSYM gmult_dec) in
  DEC_BRIDGE_ROUTEB_TAC sN spec_eq
    (("qq11","qq1","qq7"),("qq10","qq0","qq6"),("qq16","qq12","qq13")) (asl,w);;

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
          read X9 s = word 48 /\
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
  CLEAR_KEEPGHALL_MEMO_TAC THEN  (* reset the fused normalizer fixpoint cache *)
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
  (* After ASM_REWRITE the block-1 (out_p+16, captured pt1@s123) and xi halves
     already close.  The remaining conjuncts are: block-0 lo/hi (RHS
     aes256_encrypt ctr0), block-2 lo/hi (RHS aes256_encrypt
     (gcm_ctr_inc(gcm_ctr_inc ctr0))), ivec lo/hi (gcm_ctr_inc_iter 3), and
     MAYCHANGE.  Each closer is guarded to its own RHS counter (bare ctr0 vs
     gcm_ctr_inc(gcm_ctr_inc)) so it never touches the wrong conjunct: the
     block-0 closer (JOIN_IS_CTR0 + WORD_RULE) does not terminate on the
     un-normalized +2 tower. *)
  REPEAT CONJ_TAC THEN
  (* The guards are POSITIVE and mutually exclusive, and XI runs first: xi's
     goal (word_bytereverse gval = word_bytereverse GPA) has no gcm_ctr_inc, so
     a negative block-0 guard ("fail if gcm_ctr_inc") would accept it and run
     WORD_BLAST into the ghash_polyval_acc poly.  Block-0 is guarded
     positively on aes256_encrypt. *)
  (* XI (RHS = word_bytereverse of ghash_polyval_acc / gval): strip word_bytereverse, then fold the
     goal's GPA back to gval via a TARGETED check-based SUBST of the gval ABBREV assumption --
     NEVER EXPAND_TAC "gval" (it FIRST_X_ASSUM-scans, may hit read-Q19=gval asms
     over the 1242-asm context). *)
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
         REFL_TAC) (asl,w))
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
  (* out block-2 (out_p+32): RHS = aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0)).
     WORD_XOR_ASSOC+WORD_BLAST closer. *)
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
     so it fires ONLY on the two block-0 halves.  WORD_XOR_ASSOC+WORD_BLAST closer. *)
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
  (* MAYCHANGE: SUBSUMED_MAYCHANGE_TAC's SUBSUMED_SEQ_LEFT/RIGHT recursion is far
     too slow on the accumulated frame (~52 single-component `,,` chain) after
     the SIM, so close via the pre-computed direct implication WB3_FRAME_IMP
     (built before the SIM: `frame s0 s183 ==> goal s0 s183`, no eta-redex):
     discard to the MAYCHANGE assumption, then one MATCH_MP+ACCEPT. *)
  DISCARD_ASSUMPTIONS_TAC (fun th -> not(maychange_term(concl th))) THEN
  FIRST_X_ASSUM(fun th -> ACCEPT_TAC(MATCH_MP WB3_FRAME_IMP th)));;

(* ==== k=4 fused body ==== *)
(* WB_FUSED_4BLOCK (k=4): the k=3 structure extended to 4 windows.
     plain (1--30); w0 blk0xH^4 KEEPGHALL (31--81) pt0@s81; w1 blk1xH^3 (82--124) pt1@s124;
     w2 blk2xH^2 (125--167) pt2@s167; w3 blk3xH+reduce (168--214) bridge@s214;
     brev@s218; tail VSTEPS (215--227): xi@s221, ivec@s224, blk3 store@s226, b@s227.
   Bridge: qq14=qq9(+)qq1 (hi), qq13=qq8(+)qq0 (lo), qq20=qq15(+)qq16 (mid).
   Closers THEN-chained (apply to ALL post-conjuncts): xi, ivec(iter4), blk3(inc^3), blk2(inc^2),
     blk1(inc^1), blk0(bare ctr0). MAYCHANGE via WB4_FRAME_IMP (built before the SIM). *)

(* ---- MAYCHANGE frame lemma (proved before the SIM; frame algebra only) ---- *)

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

(* GCM_CTR_INC4_LANES and spec_to_byteform_wb4 are the ones defined earlier
   in this file. *)

let dec_bridge_specl_4_cph3 =
  [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h4:int128`;
   `word_bytereverse cph1:int128`; `byteswap128 h3:int128`;
   `word_bytereverse cph2:int128`; `byteswap128 h2:int128`;
   `word_bytereverse cph3:int128`; `byteswap128 h:int128`];;

(* BRIDGE_CLOSE_4_CPH3_TAC: nblk=4, last block cph3.  Thin wrapper over the shared
   DEC_BRIDGE_ROUTEB_TAC; the 3 block-0(H^4) mid distributions:
   qq14=qq9(+)qq1 (hi), qq13=qq8(+)qq0 (lo), qq20=qq15(+)qq16 (mid). *)
let BRIDGE_CLOSE_4_CPH3_TAC sN : tactic = fun (asl,w) ->
  let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
  let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
  let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
  let gmult_dec = REWRITE_RULE[LET_DEF;LET_END_DEF] (SPECL dec_bridge_specl_4_cph3 GMULT4_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform_wb4 (CONJ h2asm (CONJ h3asm h4asm))) (GSYM gmult_dec) in
  DEC_BRIDGE_ROUTEB_TAC sN spec_eq
    (("qq14","qq9","qq1"),("qq13","qq8","qq0"),("qq20","qq15","qq16")) (asl,w);;

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
          read X9 s = word 64 /\
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
  CLEAR_KEEPGHALL_MEMO_TAC THEN  (* reset the fused normalizer fixpoint cache *)
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
  (* MAYCHANGE: discard non-maychange to nasl=1, then MATCH_MP the pre-computed WB4_FRAME_IMP. *)
  DISCARD_ASSUMPTIONS_TAC (fun th -> not(maychange_term(concl th))) THEN
  FIRST_X_ASSUM(fun th -> ACCEPT_TAC(MATCH_MP WB4_FRAME_IMP th)));;

(* ========================================================================= *)
(* FUSED->BAND bridge: derive mk_band_goal k from WB_FUSED_kBLOCK             *)
(* via ENSURES_PRECONDITION_THM (no re-simulation).  The fused POST + frame   *)
(* already equal the band's under cph_i := bytes_to_int128(SUB_LIST(16i,16)    *)
(* ibytes); only the PRE differs (whole-buffer read vs per-lane; htable_mem_dec*)
(* vs explicit slots), bridged by INPUT_BYTES_TO_BYTE128_LANES + htable unfold.*)
(* The fused hk/h2../side-hyps discharge via HK_LOW/HI_IS_KARA + karatsuba_mid *)
(* + BYTESWAP128_INVOLUTION.                                                 *)
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

(* >>> SMALL-MESSAGE (FUSED) ARC END <<< *)

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
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC (wbn_weak_q_at5 k) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC (el (k-1) wbn_backlegs) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;

(* ---- the 8 recomposed bands (sim-free: reuse the WB_TAIL_GEN2_k back-leg) - *)
(* Bands 1..4 take the small-message path: derived from the proven
   WB_FUSED_kBLOCK via mk_band_from_fused (above), NOT prove_band (which routes
   the front through WB_FRONT_BUF and requires 5<=nblk, unprovable for k<5). *)
let AESV8_GCM_8X_DEC_256_BUF_1BLOCK = mk_band_from_fused 1 WB_FUSED_1BLOCK;;
let AESV8_GCM_8X_DEC_256_BUF_2BLOCK = mk_band_from_fused 2 WB_FUSED_2BLOCK;;
let AESV8_GCM_8X_DEC_256_BUF_3BLOCK = mk_band_from_fused 3 WB_FUSED_3BLOCK;;
let AESV8_GCM_8X_DEC_256_BUF_4BLOCK = mk_band_from_fused 4 WB_FUSED_4BLOCK;;
let AESV8_GCM_8X_DEC_256_BUF_5BLOCK = prove_band 5;;
let AESV8_GCM_8X_DEC_256_BUF_6BLOCK = prove_band 6;;
let AESV8_GCM_8X_DEC_256_BUF_7BLOCK = prove_band 7;;
let AESV8_GCM_8X_DEC_256_BUF_8BLOCK = prove_band 8;;
(* --- mid-load heap compaction: bound GC cost across this large single-file *)
(*     load (after the sim-free BUF series)). --- *)
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
(*      nist_input_block_bytes): twisted-key POLYVAL objects -> SP 800-38D  *)
(*      nist_ghash under the free NIST hash key H with                       *)
(*      byteswap128 h = ghash_twist H.                                       *)
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
   Byte i of the output is byte i MOD 16 of block i DIV 16
   (EL_INT128_LIST_TO_BYTES), read off that block's bytes128 store
   (BYTE8_OF_BYTES128); the input-side mirror is WBN_INPUT_ASSEMBLE. *)
let BYTE_LIST_AT_WHOLE_CTR = prove
 (`!ctr0 pts keys n out_p (len:int64) s.
    1 <= n /\ n = LENGTH pts /\ val len = 16 * n /\
    (!j. j < n ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                   EL j (aes_ctr ctr0 pts keys))
    ==> byte_list_at (aes_ctr_bytes ctr0 pts keys) out_p len s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[byte_list_at; aes_ctr_bytes] THEN
  X_GEN_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `i DIV 16 < n` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`aes_ctr ctr0 pts keys`; `i:num`] EL_INT128_LIST_TO_BYTES) THEN
  REWRITE_TAC[LENGTH_AES_CTR] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
    `word_add out_p (word i):int64 =
     word_add (word_add out_p (word (16 * (i DIV 16)))) (word (i MOD 16))`
    SUBST1_TAC THENL
   [SUBGOAL_THEN `i = 16 * (i DIV 16) + i MOD 16`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
     [MESON_TAC[DIVISION_SIMP]; ALL_TAC] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  MP_TAC(SPECL [`word_add out_p (word (16 * (i DIV 16))):int64`; `s:armstate`;
                `i MOD 16`] BYTE8_OF_BYTES128) THEN
  ANTS_TAC THENL [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]);;

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
  let x9c = el 1 (conjuncts post_body) in
  let outpost = subst [n16,`nnn:num`; wb_keys_tm,`kl:int128 list`]
    `byte_list_at (gcm_dec_pt_bytes nnn ibytes ctr0 (kl:int128 list)) out_p (word nnn) s` in
  let xipost = subst [n16,`nnn:num`]
    `read (memory :> bytes128 xi_p) s = gcm_dec_final_xi nnn ibytes xi h` in
  (* ivec: carry the band's counter write-back conjunct through
     the wrapper unchanged (spine form; not part of the byte-list vocab lift). *)
  let ivecpost = mk_ivec_conj k in
  let post' = mk_abs(sv, list_mk_conj [pcc; x9c; outpost; xipost; ivecpost]) in
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
(*  - nist_input_block_bytes: the NIST (big-endian) view of input block i of *)
(*    a byte list, with the LIST_OF_SEQ_NIST_INPUT bridges to                 *)
(*    gcm_dec_ghash_blocks.                                                   *)
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
(* htable_mem_8 hk ptr s is the shared predicate of aes_gcm_spec.ml, and
   HTABLE_MEM_8_FLAT (aes_gcm_common.ml) states it as 12 flat conjuncts.
   hk is the POLYVAL-side key (byteswap128 of the memory h slot); with
   hk = ghash_twist H this is the exact analogue of the x4 kernels'
   htable_mem_4 (ghash_twist ...) hypothesis, extended to 8 powers /
   12 slots (aws-lc layout with packed karatsuba mids). *)
let HTABLE_MEM_DEC_IS_HTABLE_MEM_8 = prove
 (`!(h:int128) (ptr:int64) (s:armstate).
     htable_mem_dec h ptr s <=> htable_mem_8 (byteswap128 h) ptr s`,
  REWRITE_TAC[HTABLE_MEM_DEC_H_POWER; HTABLE_MEM_8_FLAT]);;

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
let nist_input_block_bytes = new_definition
 `nist_input_block_bytes (x:byte list) (i:num) : int128 =
    word_reversefields 8 (bytes_to_int128 (SUB_LIST (16 * i, 16) x))`;;

(* list_of_seq (nist_input_block_bytes x) N =
   MAP word_bytereverse (gcm_dec_ghash_blocks (16*N) x) *)
let build_list_of_seq_nist n =
  let goal = list_mk_forall([`x:byte list`],
    mk_eq(list_mk_comb(`list_of_seq:(num->int128)->num->int128 list`,
            [mk_comb(`nist_input_block_bytes`,`x:byte list`); mk_small_numeral n]),
          mk_comb(`MAP (word_bytereverse:int128->int128)`,
            list_mk_comb(`gcm_dec_ghash_blocks`, [mk_small_numeral(16*n);`x:byte list`])))) in
  prove(goal,
    GEN_TAC THEN REWRITE_TAC[el (n-1) ghash_wholes; MAP] THEN
    REWRITE_TAC(map num_CONV (map mk_small_numeral (rev(1--n)))) THEN
    REWRITE_TAC[LIST_OF_SEQ; o_DEF; nist_input_block_bytes; BREV_RF8_128] THEN
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
               read X9 s = word 16 /\
               byte_list_at (gcm_dec_pt_bytes 16 ibytes ctr0 rk) out_p (word 16) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 1))
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
               read X9 s = word 32 /\
               byte_list_at (gcm_dec_pt_bytes 32 ibytes ctr0 rk) out_p (word 32) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 2))
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
               read X9 s = word 48 /\
               byte_list_at (gcm_dec_pt_bytes 48 ibytes ctr0 rk) out_p (word 48) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 3))
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
               read X9 s = word 64 /\
               byte_list_at (gcm_dec_pt_bytes 64 ibytes ctr0 rk) out_p (word 64) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 4))
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
               read X9 s = word 80 /\
               byte_list_at (gcm_dec_pt_bytes 80 ibytes ctr0 rk) out_p (word 80) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 5))
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
               read X9 s = word 96 /\
               byte_list_at (gcm_dec_pt_bytes 96 ibytes ctr0 rk) out_p (word 96) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 6))
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
               read X9 s = word 112 /\
               byte_list_at (gcm_dec_pt_bytes 112 ibytes ctr0 rk) out_p (word 112) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 7))
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
               read X9 s = word 128 /\
               byte_list_at (gcm_dec_pt_bytes 128 ibytes ctr0 rk) out_p (word 128) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 8))
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
               read X9 s = word (16 * nblk) /\
               byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p (word (16 * nblk)) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) nblk))
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

(* ====================================================================== *)
(* END inlined <=8-block chain; below: the nblk>8 main-loop proof.          *)
(* --- mid-load heap compaction: bound GC cost across this large single-file *)
(*     load). ---                                                         *)
Gc.compact();;
(* ====================================================================== *)

(* aes_xts_common: IVAL_WORD_LT.  gcm_ctr_helpers: gcm_ctr_inc / _iter, the
   GCM_CTR_INC*_LANES lemmas.  Both are no-ops if the <=8-block chain already pulled them. *)
needs "arm/proofs/utils/aes_xts_common.ml";;
needs "arm/proofs/utils/gcm_ctr_helpers.ml";;

(* ------------------------------------------------------------------------- *)
(* 1. Scalar rung lemmas (nblk > 8 generalizations of the <=8-block         *)
(*    scalar rungs).  All pure word/arith, no sim.                            *)
(*                                                                           *)
(* NOTE (signed pointer compares): the 0x44c/0x4bc/0xa04 cmp x0,x5 feed      *)
(* b.ge/b.lt = SIGNED conditions on pointers.  For nblk <= 8 x5 = in_p so    *)
(* the compare was reflexive; for nblk > 8 the exactness of                  *)
(* ival(x0) - ival(x5) needs the buffer to not straddle the 2^63 signed     *)
(* boundary: hypothesis WB_PTR_OK below (satisfied by all userspace bufs).   *)
(* ------------------------------------------------------------------------- *)

(* exact ival of an in-range pointer offset (for the signed pointer compares
   cmp x0,x5 at 0x400/0x460/0xa04 feeding b.ge/b.lt) *)
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

(* d = 128*((nblk-1) DIV 8) > 128 iff nblk >= 17 (drives the 0x4bc skip) *)
let D_GT_128 = prove
 (`!nblk. 17 <= nblk ==> (128 < 128 * (nblk - 1) DIV 8 <=> T)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `2 <= q ==> 128 < 128 * q`) THEN
  SUBGOAL_THEN `16 <= nblk - 1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN ASM_ARITH_TAC);;

(* gcm_ctr_raw_def is defined above wb_front_postcond, whose ivec conjunct
   `read Q30 s = gcm_ctr_raw (word 8) ctr0` (Sec 3, earlier in the file)
   references it.  Its body-only algebra lemmas (SUBW_RAW_*,
   GCM_CTR_RAW_INCR, REV32_FOLD_TAC) are in Sec 9b. *)

(* ivec: the raw counter accumulator ABSORBS a prior gcm_ctr_add
   into its own offset.  gcm_ctr_raw v (gcm_ctr_add u x) = gcm_ctr_raw (word_add u v) x.
   Needed by INNER_TAIL_FEED_TAC to discharge the SHIFTED tail's Q30 (the shift sets
   ctr0 := gcm_ctr_add (word 8*(q+1)) ctr0) against the EXT2 seam's Q30, and by the
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
(* 3. FRONT-N: capture the nblk>8 front (entry 0x20 -> loop head 0x4c0) as    *)
(*    WBN_FRONT_BUF.  Its simulated postcondition (state s288 at the loop     *)
(*    head) IS the i=0 instance of the ENSURES_WHILE loop invariant.          *)
(*                                                                            *)
(* Deltas vs the <=8-block WB_FRONT_BUF (entry 0x20 -> 0x44c tail):                         *)
(*  - hyps: 1<=nblk /\ nblk<=8  becomes  17<=nblk /\ 128*nblk<2^64 /\         *)
(*    val in_p + 16*nblk < 2^63 (the signed pointer-compare no-2^63-straddle).*)
(*  - prep uses the _ANY scalar rungs (X5 = word(128*((nblk-1)DIV8)) not 0).  *)
(*  - the front steps STOP before the 0x44c branch (no <=8 INT_SUB_REFL /    *)
(*    WORD_RULE collapse, since X5 != in_p here), discarding stale Q30 facts   *)
(*    with DISCARD_STALE_Q30_TAC.                                              *)
(*  - the 0x44c b.ge FALLS THROUGH via WB_LOOPENTER_FLAGS_GE9; then         *)
(*    bulk-8 segment 269..295; the 0x4bc b.ge (step 296) FALLS THROUGH to     *)
(*    the loop head via WB_PTRCMP_FLAGS + D_GT_128.                           *)
(*                                                                            *)
(* As for the <=8-block WB_FRONT_BUF, the s288 postcondition is the final    *)
(* state of the front sim (folded to aes13 + gcm_ctr_inc^k lanes by          *)
(* wb_front_fold_tac), built below with the term builders.                    *)
(* ------------------------------------------------------------------------- *)

(* nblk>8 front hypotheses: swap the (1<=nblk /\ nblk<=8) prefix of the <=8-block chain's
   wb_front_hyps_tm for the nblk>=17 regime, KEEP every nonoverlapping/aligned/
   length conjunct.
   : ALSO add nonoverlapping (out_p) (stackpointer,80).  the <=8-block chain's
   wb_front_hyps_tm omits it, but the nblk>8 front's FRONT-0 group (0x450..0x4b8)
   does four `stp q,q,[x2],#32` stores to out_p BEFORE the loop head 0x4c0.
   Without out_p-vs-stack disjointness the stepper cannot prove those stores miss
   [sp+64], so it DROPS the reduction-constant fact
   read (memory :> bytes64 (sp+64)) s = word 0xc200000000000000 (needed by the
   body GHASH reduce; see the invariant [sp+64] conjunct).
   With this conjunct the fact survives the full front sim to s288 (= loop
   head 0x4c0). *)
let wbn_front_hyps_tm =
  let _,rest1 = dest_conj wb_front_hyps_tm in
  let _,rest = dest_conj rest1 in
  mk_conj(`17 <= nblk /\ 128 * nblk < 2 EXP 64 /\ val (in_p:int64) + 16 * nblk < 2 EXP 63`,
          mk_conj(`nonoverlapping (out_p:int64,16 * nblk) (stackpointer:int64,80)`,
                  rest));;

let mk_wbn_front_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_tm, ens));;

(* pure-arith closer for the nblk>=17 side conditions *)
let NBLK_ARITH_TAC =
  MP_TAC(ASSUME `17 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

(* 0x4bc b.ge (step 296): X0=in_p+128, X5=in_p+d, 128<d for nblk>=17 => NF=T
   VF=F, FALLS THROUGH to loop head 0x4c0 *)
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

(* ------------------------------------------------------------------------- *)
(* The SHARED FRONT PREFIX, simulated ONCE.                                  *)
(*                                                                            *)
(* WBN_FRONT_BUF (band 17<=nblk, -> loop head 0x4c0) and WBN_FRONT_TO_PREP_916 *)
(* (band 9<=nblk<=16, -> prepretail 0xa10) share the front sim (entry 0x20 -> *)
(* the 0x4bc b.ge), diverging ONLY at that branch (>=17 falls through to       *)
(* 0x4c0; 9..16 is taken to 0xa10).  The 0x44c b.ge falls through in BOTH     *)
(* bands, so all earlier steps are identical work.                            *)
(*                                                                            *)
(* So prove the prefix (0x20 -> 0x4bc) ONCE on the union band 9<=nblk        *)
(* (WBN_FRONT_PREFIX), capturing the raw s295 state (incl. the NF/VF/ZF/CF    *)
(* facts the 0x4bc b.ge reads).  Each consumer then chains a single-step      *)
(* leg via ENSURES_TRANS_SIMPLE: init from the prefix postcond, resolve the   *)
(* branch IN ITS BAND, step to its exit, close.                              *)
(* ------------------------------------------------------------------------- *)

(* union band: wbn_front_hyps_tm with 17<=nblk relaxed to 9<=nblk *)
let wbn_front_hyps_ge9_tm =
  let rec repl t = match t with
    | Comb(Comb(Const("/\\",_),a),b) -> mk_conj(repl a, repl b)
    | _ -> if t = `17 <= nblk` then `9 <= nblk` else t in
  repl wbn_front_hyps_tm;;

(* 0x44c b.ge falls through whenever d=128*((nblk-1)DIV8) >= 1, i.e. nblk>=9.
   (covers both the 17<= and the 9..16 bands). *)
let WB_LOOPENTER_FLAGS_GE9 = prove
 (`!(in_p:int64) nblk. 9 <= nblk /\ 128 * nblk < 2 EXP 64 /\
        val in_p + 16 * nblk < 2 EXP 63
    ==> (ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) < &0 <=> T) /\
        (ival in_p - ival (word_add (word (128 * (nblk - 1) DIV 8)) in_p) =
         ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) <=> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `d = 128 * (nblk - 1) DIV 8` THEN
  SUBGOAL_THEN `1 <= d /\ d <= 16 * nblk /\ d <= 2 EXP 63` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
    MP_TAC(ASSUME `9 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN
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
  MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

(* 0x44c resolve (fall-through) via WB_LOOPENTER_FLAGS_GE9. *)
let WBN_RESOLVE_42C_GE9_TAC : tactic =
  MP_TAC(SPECL [`in_p:int64`; `nblk:num`] WB_LOOPENTER_FLAGS_GE9) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]));;

(* prefix goal builder (union band, postcond at PC 0x4bc) *)
let mk_wbn_prefix_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_ge9_tm, ens));;

(* The s287 prefix postcondition (state at the 0x4bc b.ge, pre-branch), so the
   shared front simulates ONCE.  Keeps ALL raw `read _ s287 = _` facts INCLUDING
   the NF/VF/ZF/CF flag facts the 0x4bc b.ge reads (so each consumer's step-296
   leg can resolve the branch in its band).  Built like wb_front_postcond, as the
   final state of the prefix sim (WBN_FRONT_PREFIX's tactic up to the 0x4bc
   b.ge, THEN wb_front_fold_tac). *)
let wbn_front_prefix_postcond = wbp_post
 ([`aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
   `read PC s = word (pc + 1212)`;
   wbp_rd `Q30` (wbp_raw_acc 12);
   wbp_out 6; wbp_out 7;
   `read X2 s = word_add out_p (word 128)`;
   wbp_out 4; wbp_out 5;
   wbp_rd `Q3` (wbp_rev_ctr 11);
   wbp_out 2; wbp_out 3;
   wbp_rd `Q0` (wbp_rev_ctr 8)] @
  wbp_cmp_flags `word_add in_p (word 128):int64`
                `word_add (word (128 * (nblk - 1) DIV 8)) in_p:int64` @
  [wbp_rd `Q12` (mk_cph 4); wbp_rd `Q13` (mk_cph 5);
   wbp_rd `Q8` (mk_cph 0); wbp_rd `Q9` (mk_cph 1);
   `read X5 s = word_add (word (128 * (nblk - 1) DIV 8)) in_p`;
   `read (memory :> bytes64 (word_add stackpointer (word 64))) s = word 13979173243358019584`;
   `read (memory :> bytes64 (word_add stackpointer (word 72))) s = word 0`;
   `read X11 s = key_p`;
   `read X9 s = word (16 * nblk)`;
   `read SP s = stackpointer`;
   `read X1 s = word (128 * nblk)`;
   `read X3 s = xi_p`;
   `read X6 s = htbl_p`] @
  wbp_ctx `xi:int128` @
  [wbp_rd `Q11` (mk_cph 3); wbp_rd `Q10` (mk_cph 2);
   `read X0 s = word_add in_p (word 128)`;
   wbp_rd `Q15` (mk_cph 7); wbp_rd `Q14` (mk_cph 6);
   wbp_out 1; wbp_out 0;
   wbp_rd `Q5` (wbp_pt 5);
   wbp_rd `Q1` (wbp_rev_ctr 9); wbp_rd `Q2` (wbp_rev_ctr 10);
   wbp_rd `Q6` (wbp_pt 6); wbp_rd `Q7` (wbp_pt 7);
   wbp_rd `Q4` (wbp_rev_ctr 12)]);;

(* input lanes 0..7 established at s267 (the >=9 post-branch leg reads blocks
   0..7 via the ldp q8-q15 at 0x448+); follows from the s267 input-memory fact.
   The consumer WBN_FRONT_PREFIX does ENSURES_INIT_TAC "s267"; the SPECL state MUST
   match it or ASM_REWRITE_TAC cannot discharge INPUT_BYTES_TO_BYTE128_LANES's
   input-memory antecedent, leaving `lth` an implication -> SPEC raises. *)
let WBN_LANES_PREBRANCH_GE9_TAC =
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

(* FRONT-PREFIX (>=9 band): chain the shared WBN_FRONT_PREBRANCH (0x20->0x44c)
   via ENSURES_TRANS_SIMPLE, then the 0x44c b.ge FALLS THROUGH (nblk>=9, via
   WB_LOOPENTER_FLAGS_GE9) + steps 268..295 to s295 (pc+1212). *)
let WBN_FRONT_PREFIX = prove(mk_wbn_prefix_goal wbn_front_prefix_postcond,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_front_prebranch_postcond THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_PREBRANCH THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ENSURES_INIT_TAC "s267" THEN RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
    WBN_LANES_PREBRANCH_GE9_TAC THEN WBN_RESOLVE_42C_GE9_TAC THEN
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (268--268) THEN
    EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (i--i) THEN
               GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC) (269--295)) THEN
    wb_front_fold_tac THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]);;

(* The s288 postcondition (the i=0 loop invariant), so the front simulates ONCE
   (in the WBN_FRONT_BUF proof below), as for the <=8-block chain's
   wb_front_postcond: the final state of the front sim at the loop head (THEN
   wb_front_fold_tac).  It holds the facts of wbn_front_prefix_postcond one step
   later, after the 0x4bc b.ge: in reverse order, with PC = pc+1216 and without
   the NF and VF facts. *)
let wbn_front_postcond_i0 =
  let cs = conjuncts(snd(dest_abs wbn_front_prefix_postcond)) in
  let nf_vf c = try mem (rand(rator(lhs c))) [`NF`; `VF`] with Failure _ -> false in
  wbp_post (hd cs :: `read PC s = word (pc + 1216)` ::
            filter (not o nf_vf) (rev (tl (tl cs))));;

(* WBN_FRONT_BUF: the FRONT-N theorem.  Its postcond = the i=0 loop invariant
   (two-stream pipelined form): q8..q15 = RAW ct blocks 0..7 pending fold,
   Q19 = word_bytereverse xi (GHASH acc over blocks 0..-1 = tag only), stores
   done for blocks 0..7, counters at 8..12, X0=in_p+128, X2=out_p+128.
   It reuses the shared WBN_FRONT_PREFIX (0x20->0x4b8) via
   ENSURES_TRANS_SIMPLE, then step 296 (0x4bc b.ge FALLS THROUGH for
   17<=nblk, via WBN_RESOLVE_49C_TAC) lands at the loop head 0x4c0 = pc+1216
   (fall-through target).  Close = ASM_REWRITE + WORD_ADD_0. *)
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
(*     load (after a front-BUF sim)). --- *)
Gc.compact();;

(* ------------------------------------------------------------------------- *)
(* 4. The TWO-STREAM ENSURES_WHILE loop invariant.                            *)
(*                                                                            *)
(* Derived by generalizing WBN_FRONT_BUF's simulated s288                     *)
(* postcond to symbolic block index i.  The i=0 instance was checked to      *)
(* follow from WBN_FRONT_BUF: 44 of 47 conjuncts (all registers, counters,    *)
(* keystreams, GHASH acc, stores, pointers) close by                          *)
(*   CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN                                  *)
(*   RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN                *)
(*   REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD; GCM_CTR_ADD_1; GSYM GCM_CTR_ADD_LANES] *)
(*     THEN REWRITE_TAC[list_of_seq; MAP; ghash_polyval_acc] THEN             *)
(*   RULE_ASSUM_TAC(REWRITE_RULE[GCM_CTR_INC_LANES;..;GCM_CTR_INC7_LANES])    *)
(*     THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN         *)
(*   REWRITE_TAC[GCM_CTR_ADD_0] THEN CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_   *)
(*     CONV) THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN                     *)
(*   REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[].                          *)
(*                                                                            *)
(* The remaining 3 conjuncts                                                  *)
(*   read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes       *)
(*   read (memory :> bytes128 key_p) s = k0                                   *)
(*   htable_mem_dec h htbl_p s                                                *)
(* are loop-CONSTANTS that hold at the loop head (they are in wb_front_pre_tm *)
(* and NOT in the front MAYCHANGE frame -> preserved) but are NOT in          *)
(* WBN_FRONT_BUF's simulated postcond (which keeps only                       *)
(* `read _ s = _` + aligned_bytes_loaded, so htable_mem_dec is dropped, and   *)
(* the in_p/key_p reads were s0 facts not re-stated at s288).  So the front   *)
(* postcond is extended to re-assert these 3 by a strengthening step;         *)
(* WBN_FRONT_BUF then closes them from the                                    *)
(* precond (they are in the MAYCHANGE-preserved set).  With that the          *)
(* ENSURES_WHILE_UP_TAC entry subgoal (i=0) closes by MATCH_MP_TAC            *)
(* WBN_FRONT_BUF_EXT (Sec 7, the strengthened front) + the tactic above.      *)
(*                                                                            *)
(* Two-stream reading of the invariant (checked against the i=0 goal):        *)
(*  - store/counter stream AHEAD at 8(i+1): X0=in_p+128(i+1), X2=out_p+128(i+1)*)
(*    Q0..Q4 = gcm_ctr_add (word (8i+8..12)) ctr0 (next group's counters),    *)
(*    Q5..Q7 = plaintext blocks at 8i+5..7 (in-flight keystream XOR),         *)
(*    stores done for all j < 8(i+1).                                         *)
(*  - GHASH stream LAGS at 8i: Q19 = ghash_polyval_acc (byteswap128 h)        *)
(*    (word_bytereverse xi) over reversed raw ct blocks 0..8i-1;              *)
(*    q8..q15 = RAW ct blocks 8i..8i+7 pending fold (the bridge).             *)
(*                                                                            *)
(* The +8*i offset on the Q5..Q7 keystream indices (5,6,7 at i=0, all < 8)   *)
(* is read off the loop-body sim goal, not trusted from this generalization. *)
(* loop control flow (objdump): head pc1=pc+0x4c0; back-edge cmp x0,x5 @0xa04 *)
(* + b.lt 0x4c0 @0xa0c (SIGNED, so a P-variant / WB_PTRCMP_FLAGS handles it); *)
(* exit fall-through @0xa10.  count q = (nblk-9) DIV 8.                        *)
(*                                                                            *)
(* Q26/Q27/Q28 (=k12/k13/k14) DROPPED from the invariant below                *)
(* -- objdump-verified dead live-ins (loop-head ldp q26,q27,[x11] @0x4c4 +     *)
(* 0x538 ldp q28,q26,[x11,#32]; prepretail seam 0xa10 ldp q26,q27,[x11] -- all *)
(* reload before first aese v_,v26/28 uses at 0x4f8/0x590).                   *)
(* CAUTION: do NOT put (* *) comments or backticks INSIDE the term backquote   *)
(* below -- HOL's in-term comment token is //, and (* *) / ` break the parse. *)
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

(* ---- Entry-subgoal recipe ------------------------------------------------
   The ENSURES_WHILE_UP_TAC entry subgoal is  pre ==> (PC=pc1 /\ inv 0 s).
   Given WBN_FRONT_BUF establishes pre ==> (PC=pc+0x4b8 /\ <postcond s>), the
   i=0 invariant  (wbn_loop_invariant_raw ... 0 s)  follows from <postcond s> PLUS
   the 3 loop-constants (in_p read-only, key_p=k0, htable_mem_dec) once those
   are added to WBN_FRONT_BUF's postcondition.  The closing tactic (proves 44/47
   directly from the postcond hyps; the 3 come from the extended front):

     GEN_TAC THEN REWRITE_TAC[wbn_loop_invariant_raw] THEN
     CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
     CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
     REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD; GCM_CTR_ADD_1; GSYM GCM_CTR_ADD_LANES] THEN
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
   the antecedent, before STRIP_TAC) -- a naive `(\s.P) s /\ (\s.Q) s ==> ...`
   left unreduced makes STRIP_TAC give conjunct hyps still wrapped.

   For a clean entry (no extra hyps), WBN_FRONT_BUF_EXT strengthens
   WBN_FRONT_BUF with the 3 loop-constants (they hold in wb_front_pre_tm and
   survive the frame) via a framing/ENSURES_TRANS wrapper, with no re-sim.
   The entry subgoal of ENSURES_WHILE_UP_TAC then closes by MATCH_MP_TAC
   WBN_FRONT_BUF_EXT + the tactic above (see Sec 7). *)

(* ------------------------------------------------------------------------- *)
(* 5. GHASH 8-block extension algebra (pure list/field, no sim).              *)
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

(* The main lemma of Sec 5: extend the invariant's GHASH fold by one 8-block  *)
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
(* the <=8-block chain's (STRIP; GHASH_POLYVAL_ACC_8; ASM_REWRITE; AP_TERM; WORD_RULE) --      *)
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
(* reduce window (asm 0x944..0x9d4) reads three separable 128-bit accumulators  *)
(* at s289                                                                      *)
(*   PL = Q17 = Sum_k karatsuba_block_pl,  PH = Q19 = Sum_k karatsuba_block_ph,  *)
(*   PM = Q18 = Sum_k karatsuba_block_pm,  Barrett modulus raw in Q16,          *)
(* then runs the shared Barrett W-reduction, landing read Q19 s326 in EXACTLY   *)
(* the byteform LHS below (over OPAQUE PL/PH/PM -- the sim keeps them abbreviated *)
(* so the reduce window stays small).  This lemma says that byteform is         *)
(* polyval_reduce_prop3 (pack_corrected PL PH PM) -- the pre-byte-reversal prop3 *)
(* on the Karatsuba-corrected packed value.  The s326 OUTPUT is byteform, while *)
(* the INPUT triple lives at s289; the OUTPUT is prop3 o pack_corrected of the  *)
(* INPUT triple, with no outer word_reversefields -- exactly matching           *)
(* BODY_Q19_CLOSE_ALGEBRA's prop3 RHS.                                           *)
(*                                                                             *)
(* It is derived from the shared statement of this reduction pattern,          *)
(* POLYVAL_REDUCE_G2 (aes_gcm_common.ml): pack_corrected (the zx/shl packing   *)
(* the N-block Karatsuba layer of common/ghash_nblock_karatsuba.ml is stated   *)
(* in) is karatsuba_join, so the RHS is polyval_reduce_g2 PL PH PM, and the    *)
(* byteform is the same xor of the same two pmuls up to rearrangement.  The    *)
(* statement keeps pack_corrected because KARA_ACC_PACK_HELPER, which packs    *)
(* the eight per-block triples in the Q19 close below, is stated with it.      *)
(* --------------------------------------------------------------------------- *)
let PACK_CORRECTED_KARATSUBA_JOIN = prove
 (`!pl ph pm:int128. pack_corrected pl ph pm = karatsuba_join pl ph pm`,
  REWRITE_TAC[pack_corrected; karatsuba_join] THEN BITBLAST_TAC);;

let POLYVAL_REDUCE_G2_KARATSUBA_JOIN = prove
 (`!p1 p2 p3:int128.
     polyval_reduce_g2 p1 p2 p3 = polyval_reduce_prop3 (karatsuba_join p1 p2 p3)`,
  REWRITE_TAC[karatsuba_join; POLYVAL_REDUCE_G2]);;

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
  REWRITE_TAC[PACK_CORRECTED_KARATSUBA_JOIN;
              GSYM POLYVAL_REDUCE_G2_KARATSUBA_JOIN] THEN
  REWRITE_TAC[polyval_reduce_g2; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `w1:int128 = word_pmul (word_subword (PL:int128) (0,64):64 word)
                                    (word 13979173243358019584:64 word)` THEN
  SUBGOAL_THEN
   `word_subword
      (word_xor (word_xor (word_xor (word_xor PM PL) PH) (w1:int128))
                (word_subword (word_join (PL:int128) PL :256 word) (64,128)))
      (0,64) :64 word =
    word_xor (word_xor (word_subword w1 (0,64)) (word_subword PL (64,64)))
             (word_subword (word_xor (word_xor PL PH) PM) (0,64))`
   SUBST1_TAC THENL [BITBLAST_TAC; ALL_TAC] THEN
  ABBREV_TAC `w2:int128 = word_pmul
     (word_xor (word_xor (word_subword (w1:int128) (0,64):64 word)
                         (word_subword (PL:int128) (64,64)))
               (word_subword (word_xor (word_xor PL PH) PM) (0,64)))
     (word 13979173243358019584:64 word)` THEN
  BITBLAST_TAC);;

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
(* swapped-RHS PM_LANE_HI'/LO' variants below are consumed (by                  *)
(* build_q19_reduce_clean and build_q19_reduce_clean_idx): they spell the       *)
(* extracted mid-input in the (0,64)^(64,64) lane order that karatsuba_block_pm *)
(* produces (word_pmul's first arg is atomic to WORD_RULE, so the lane XOR must *)
(* match SYNTACTICALLY, not up to comm).                                        *)
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
(* Compose the value-equality into the Q19 close.                             *)
(*                                                                             *)
(* build_q19_reduce_clean pl_t ph_t pm_t : given the three s289 accumulator     *)
(* terms (= read Q17/Q19/Q18 s289, over h/xi/ibytes/i), produces the CLEAN      *)
(* theorem  |- <machine reduce byteform> = ghash_polyval_acc (byteswap128 h)    *)
(*   (word_bytereverse xi) (MAP word_bytereverse (list_of_seq blk (8*(i+1))))   *)
(* hyps=0 -- the invariant's Q19-at-(i+1) fold.  It chains:                     *)
(*   reduce_id  : byteform = polyval_reduce_prop3 (pack_corrected PL PH PM)     *)
(*                                        [WBN_MACHINE_REDUCE_IS_PROP3_PACK]     *)
(*   KARA_PACK_EQ (kqok): pack_corrected PL PH PM = SPEC_TOWERS                  *)
(*   body_ready2 : ghash..(8(i+1)) = polyval_reduce_prop3 SPEC_TOWERS           *)
(*                                        [BODY_Q19_CLOSE_ALGEBRA + involution]  *)
(* The 8 kqok side-conditions (subword hk_j (0,64) = karatsuba_mid ..) are      *)
(* discharged by choosing hk_j := word_join (word 0)(karatsuba_mid ..) so kqok  *)
(* holds unconditionally (KMID_BYTESWAP_INV) -- a hyps-free                   *)
(* lemma.  PROJ_PM is kept CONDITIONAL on kqok (hk free) then INST'd+MP'd -- the *)
(* bake-hk-upfront variant fails PROJ_PM (subword(join 0 kmid) not plain kmid). *)

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
(* 6. Strengthen an ensures postcondition with a frame-PRESERVED fact,        *)
(*    with NO re-simulation.  Pure ensures/eventually logic.                  *)
(*                                                                            *)
(* This is the combinator for WBN_FRONT_BUF_EXT (also used in the Sec 12      *)
(* recomposition): given `ensures step P Q C` and that the frame C, from      *)
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
(* 7. WBN_FRONT_BUF_EXT: the front with the 3 loop-constants re-asserted.     *)
(*                                                                            *)
(* The i=0 invariant instance needs 3 loop-CONSTANTS at the loop head that    *)
(* WBN_FRONT_BUF's simulated postcond drops (see Sec 4):                      *)
(*   read (memory :> bytes (in_p,16*nblk)) s = num_of_bytelist ibytes         *)
(*   read (memory :> bytes128 key_p) s = k0                                   *)
(*   htable_mem_dec h htbl_p s                                                *)
(* These are preserved by the front MAYCHANGE frame (which writes only        *)
(* out_p/xi_p/ivec_p/stack + Q-regs), PROVIDED out_p is disjoint from in_p/   *)
(* key_p/htbl_p.  wbn_front_hyps_tm does not include those 3 out_p            *)
(* disjointness conjuncts (the <=8-block band hyps do), so they are added     *)
(* in wbn_front_hyps_wide_tm below.                                           *)
(*                                                                            *)
(* Proof: ENSURES_ADD_PRESERVED, so the front is NOT re-simulated under the   *)
(* widened hyps: WBN_FRONT_BUF is kept verbatim and its postcond is           *)
(* STRENGTHENED with the 3 constants: leg1 = WBN_FRONT_BUF (narrow hyps <=    *)
(* wide hyps, closed by MATCH_MP_TAC + ASM_REWRITE), leg2 = the pure          *)
(* frame-preservation obligation (no sim).  Whole thing proves in ~4s.        *)
(* ------------------------------------------------------------------------- *)

(* widened front hyps = wbn_front_hyps_tm + the 3 out_p disjointness conjuncts *)
let wbn_front_hyps_wide_tm =
  mk_conj(wbn_front_hyps_tm,
    `nonoverlapping (out_p:int64,16 * nblk) (in_p:int64,16 * nblk) /\
     nonoverlapping (out_p:int64,16 * nblk) (key_p:int64,240) /\
     nonoverlapping (out_p:int64,16 * nblk) (htbl_p:int64,192)`);;

(* the WBN_FRONT_BUF pieces (P = precond, Q0 = simulated postcond, C = frame) *)
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
(* 8. WBN_LOOP_INVARIANT_ENTRY_RAW: the front establishes the i=0 invariant.  *)
(*                                                                            *)
(* THE entry subgoal that ENSURES_WHILE_UP_TAC produces for the main loop:    *)
(*   ensures arm (\s. decodes /\ PC = pc+0x20 /\ precondition s)              *)
(*               (\s. decodes /\ PC = pc+0x4c0 /\ wbn_loop_invariant_raw ... 0 s) *)
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

(* post = \s. decodes /\ PC = pc+0x4c0 /\ inv 0 s *)
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
    REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD; GCM_CTR_ADD_1; GSYM GCM_CTR_ADD_LANES] THEN
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
    (* Q30 residual: the only conjunct the closer leaves open.  The i=0 raw
       tower (top lane += 12 then += 1) collapses to gcm_ctr_raw (word 13) ctr0
       = the invariant's 8*0+13 value. *)
    REWRITE_TAC[gcm_ctr_raw_def;
      WORD_RULE `word_add (word_add (x:32 word) (word 12)) (word 1) =
                 word_add x (word 13)`;
      WORD_ADD_0];
    (* the ensures = WBN_FRONT_BUF_EXT *)
    MATCH_MP_TAC WBN_FRONT_BUF_EXT THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 9. The PC/decode-free CORE invariant and its split.                        *)
(*                                                                            *)
(* wbn_loop_invariant_raw bakes in two conjuncts the ENSURES_WHILE tactics MUST   *)
(* own themselves:                                                            *)
(*   C1  aligned_bytes_loaded s (word pc) ...mc   (program_decodes)           *)
(*   C2  read PC s = word (pc + 1216)             (the loop-head PC)          *)
(* Every ENSURES_WHILE_* template threads `program_decodes` and `read PC =    *)
(* word pcX` around its OWN `loopinv i s`, applying loopinv at BOTH pc1 (head)*)
(* and pc2 (back-edge/exit).  A PC baked into the invariant is therefore      *)
(* redundant at pc1 and *contradictory* at pc2 (it would force PC=0x4c0 in a  *)
(* state whose PC is 0xa0c/0xa10).  Standard s2n invariants (keccak,          *)
(* emontredc) are PC/decode-free for exactly this reason.                     *)
(*                                                                            *)
(* wbn_loop_inv_core_raw = wbn_loop_invariant_raw with C1,C2 removed (built by        *)
(* dropping the first two conjuncts, so it stays in sync with that            *)
(* definition automatically).  WBN_INV_RAW_SPLIT is the bridge                    *)
(*   wbn_loop_invariant_raw ... i s <=>                                           *)
(*     aligned_bytes_loaded s (word pc) mc /\ read PC s = word (pc+1216) /\   *)
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
  (* C1 = aligned_bytes_loaded, C2 = read PC = word(pc+1216); drop both *)
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
(* 9b. The RAW counter accumulator Q30 in the loop invariant.                 *)
(*                                                                            *)
(* The body's FIRST instruction                                               *)
(*   0x4c0  rev32 v5, v30                                                     *)
(* reads Q30 -- the running CTR-block counter in its rev32-pending "raw"      *)
(* form -- so the invariant must pin Q30, or Q5 goes symbolic in              *)
(* `read Q30 s0` and the body cannot close.  Static live-in analysis of the   *)
(* whole body (0x4c0..0xa0c) shows that every other vector register the       *)
(* body reads before writing it is pinned by the other conjuncts.             *)
(*                                                                            *)
(* WBN_FRONT_BUF's postcondition carries Q30 as its last conjunct, a raw      *)
(* bit-tower.  At the loop head of iteration i the value is                   *)
(* gcm_ctr_raw (word (8*i+13)) ctr0; at i=0 the front's tower equals          *)
(* gcm_ctr_raw (word 13) ctr0 (via gcm_ctr_raw_def + WORD_RULE add-merge +    *)
(* WORD_ADD_0).                                                               *)
(*                                                                            *)
(* gcm_ctr_raw w ctr0 is the counter in the "byte-grouped, top-lane += w"      *)
(* representation the hardware keeps in v30: its top 32-bit lane is            *)
(* word_add (<brev of ctr0[96:128] bytes>) w, the low 96 bits are ctr0's low   *)
(* lanes byte-grouped.  The body does rev32(v30) -> AES keystream input for    *)
(* block 8i+13, then add v30,v30,v31 (v31 = word 2^96) to advance to 8i+14.    *)
(*                                                                            *)
(* So wbn_loop_invariant_raw has the conjunct                                 *)
(*   read Q30 s = gcm_ctr_raw (word (8 * i + 13)) ctr0                        *)
(* (and wbn_loop_inv_core_raw inherits it).  WBN_LOOP_INVARIANT_ENTRY_RAW     *)
(* establishes it at i=0 (from conjunct 46 via the gcm_ctr_raw (word 13)      *)
(* identity), and the step case advances it 8i+13 -> 8(i+1)+13 = 8i+21        *)
(* over the 8 in-body increments.                                             *)
(* ------------------------------------------------------------------------- *)

(* gcm_ctr_raw_def is defined in Sec 2: the Sec-4 invariant pins
   Q30 = gcm_ctr_raw (word (8*i+13)) ctr0, so the definition must precede Sec 4.
   Its body-only algebra lemmas are here. *)


(* REV32 fold: `rev32 v_,v30` (esize=32) applied to gcm_ctr_raw w ctr0 yields
   gcm_ctr_add w ctr0 -- the proper AES keystream input for CTR block w.  The
   arm_REV32_VEC tower is auto-generated by the stepper (~8k chars, deterministic),
   so the reusable form is a TACTIC that folds `read Qd sN` after a rev32-of-v30 step.
   Recipe:
     <capture the rev32 tower T = rhs of `read Qd sN`>, then prove `T = gcm_ctr_add w ctr0` by
       REWRITE_TAC[gcm_ctr_raw_def] THEN
       GEN_REWRITE_TAC RAND_CONV [GCM_CTR_ADD_LANES] THEN
       <SPEC_TAC the `word_add <topbytes> w` atom to a fresh 32-word> THEN
       GEN_TAC THEN CONV_TAC WORD_BLAST
   CRUCIAL: unfold gcm_ctr_raw EVERYWHERE (plain REWRITE_TAC[gcm_ctr_raw_def], NOT ONCE_DEPTH)
   and unfold the RHS via GCM_CTR_ADD_LANES so BOTH sides carry only the shared symbolic-add
   atom; THEN SPEC_TAC that atom away before WORD_BLAST (WORD_BLAST on a live symbolic
   `word_add _ w` OOMs -- see the Sec 2 OOM WARNING).  The GCM_SIMD_SIMPLIFY_TAC used per body step may
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
   After `add v30,v30,v31` @0x4c8/0x4dc/... + GCM_SIMD_SIMPLIFY_TAC, the assumption
   `read Qd sn = <single-add tower over gcm_ctr_raw wtm ctr0>` (top lane
   word_add (word_subword (gcm_ctr_raw wtm ctr0)(96,32))(word 1), others +0) folds
   to `read Qd sn = gcm_ctr_raw (word_add wtm (word 1)) ctr0` via GCM_CTR_RAW_INCR
   instantiated at w:=wtm.  Fold ONCE PER add (before the next add re-nests the
   +1s) so only the single-+1 GCM_CTR_RAW_INCR LHS is ever matched.
   (MATCH_ACCEPT on the exact simplified single-add shape.) *)
let CTR_RAW_INCR_FOLD_TAC (qd:string) (sn:string) (wtm:term) : tactic =
  let incr_spec = INST [wtm,`w:32 word`] GCM_CTR_RAW_INCR in
  RULE_ASSUM_TAC(fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),st)),_)
        when string_of_term c = qd && (try fst(dest_var st)=sn with _ -> false) ->
        REWRITE_RULE[incr_spec] th
    | _ -> th);;

(* ------------------------------------------------------------------------- *)
(* 10. The ENSURES_WHILE skeleton for WBN_MAIN_LOOP_raw.                      *)
(*                                                                            *)
(* The back-edge of .L256_dec_main_loop is                                    *)
(*   cmp x0,x5 @0xa04 ; stp q6,q7,[x2],#32 @0xa08 ; b.lt 0x4c0 @0xa0c         *)
(* i.e. the SIGNED conditional branch b.lt is the LAST body instruction and   *)
(* its flag-setting cmp is two instructions earlier -- BOTH inside the body.  *)
(* That is the ENSURES_WHILE_UP2_TAC shape (branch folded into the body): the *)
(* body postcondition PC is word(if i+1<k then pc1 else pc2), the flag never  *)
(* crosses a frame boundary, and the exit lands at the fall-through pc2.       *)
(* Count k = (nblk-9) DIV 8; pc1 = pc+0x4c0 (head); pc2 = pc+0xa10 (exit).     *)
(*                                                                            *)
(* ENSURES_WHILE_UP2_TAC discharges its internal `C ,, C = C` conjunct by     *)
(* MAYCHANGE_IDEMPOT_TAC, which fails in ASSIGNS_SEQ_ABSORB_CONV on this      *)
(* 4-memory-region frame (the MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI       *)
(* macro doesn't canonicalize into the ASSIGNS sequence ABSORB expects).      *)
(* With the ABI macro expanded FIRST, MAYCHANGE_IDEMPOT_TAC succeeds (~2s).   *)
(* up2_pth re-proves the internal pth of ENSURES_WHILE_UP2_TAC (in            *)
(* common/relational.ml), and UP2_ABI_TAC is that tactic's up-count closure   *)
(* with the ABI expand spliced into the idempotence CONJ_TAC leg.             *)
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

(* ENSURES_WHILE_UP2_TAC's internal `pth` (common/relational.ml), re-proved
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
(* (ldp q8,q9,[x0],#32 @0x830 etc, x0 = in_p+128(i+1)).  The sim discards       *)
(* these read-facts, but they are RE-DERIVABLE at any                           *)
(* body state from the surviving in_p loop-constant (read (memory :> bytes       *)
(* (in_p,16*nblk)) s = num_of_bytelist ibytes), which is preserved (in_p is      *)
(* read-only, out_p disjoint).  WBN_RAWCT_BOUND: the step-case bound i<(nblk-9)   *)
(* DIV 8 gives 8(i+1)+m < nblk for m<8.  WBN_RAWCT_READ: INPUT_BYTES_TO_BYTE128_ *)
(* LANES (from the <=8-block chain) specialized so each block reads at in_p+16*(8(i+1)+m) =     *)
(* bytes_to_int128(SUB_LIST(16*(8(i+1)+m),16) ibytes) -- exactly the invariant's *)
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
(* 10a. Loop-body simulation machinery.                                       *)
(*                                                                            *)
(* The loop body 0x4c0..0xa0c (340 instrs) is a software-pipelined 8-block     *)
(* group: 8 AES-256 keystreams (aese/aesmc towers), 8 GHASH Horner folds,      *)
(* the CTR-block counter advancing 8i+13 -> 8i+21 = 8(i+1)+13, 4 stp stores,   *)
(* next-group ldp loads, and the signed b.lt back-edge.  The sim is driven     *)
(* per-region (s0..s340, terms kept flat):                                   *)
(*   - counter-input rev32 v_,v30 folds:  REV32_FOLD_TAC "Qd" "sN" `word(8i+c)`*)
(*   - counter-increment add v30 folds:   CTR_INCR_NORM_TAC "sN" c  (fold once *)
(*       per add, THEN normalize word_add(word(8i+c))(word 1) -> word(8i+c+1)) *)
(*   - AES/GHASH bulk 14..317:  ARM_STEPS_FOLD_Q18LATEST_TAC (keeps only the    *)
(*       latest Q18 GHASH partial) + DISCARD_STALE_Q19_TAC + GCM_SIMD_SIMPLIFY  *)
(*       (folds the rev64 ct byte-trees); pile stays ~5-6k chars.              *)
(*   - store window 318..340:  Q18LATEST stepper (store read-backs self-        *)
(*       propagate; do NOT blanket-VSTEPS - a 781-hyp pile makes the stepper    *)
(*       throw `mk_comb: types do not agree` on the stp).                       *)
(*   - back-edge b.lt @0xa0c:  resolve NF/VF via WB_PTRCMP_FLAGS (a=128*(i+2),  *)
(*       d=128*((nblk-1)DIV8)) as STANDALONE flag theorems rewritten into the   *)
(*       assumptions (NOT MP_TAC'd into the goal - that pollution breaks the    *)
(*       stp step).  PC lands at if 128*(i+2)<128*((nblk-1)DIV8) then 0x4c0     *)
(*       else 0xa10, bridged to if i+1<(nblk-9)DIV8 ... by WBN_PC_BRIDGE.       *)
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

(* ---- body-close reduce-window infrastructure --------
   The final GHASH reduce (0x944..0x9d4) reloads Q16 = the [sp+64] modulus (carried by
   the invariant) and feeds the pmull/eor3 chain via Q16/Q17/Q21/Q29.
   DISCARD_STALE_QREG_TAC qn keeps only the LATEST read of register qn (the
   generalization of DISCARD_STALE_Q19_TAC used by the KEEPDATA steppers). *)
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
(* WBN_NBLK_GE_9 precedes RAWCT_LEMMA_AT (Sec 10b), which references it. *)
let WBN_NBLK_GE_9 = prove
 (`0 < (nblk - 9) DIV 8 ==> 9 <= nblk`,
  MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 10b. Loop-body postcondition-MATCH machinery.                              *)
(*                                                                            *)
(* The orthogonal postcond conjuncts close once these sub-problems are       *)
(* solved:                                                                    *)
(*                                                                            *)
(* (A) Q8..Q15 raw-ct [3-10]:                                                 *)
(*   right after each ldp (steps 221 src s220, 273 src s272, 306 src s305,     *)
(*   309 src s308), the machine gives read Qk sN = read(mem:>bytes128 ADDR)    *)
(*   s(N-1) -- an OLD-STATE read that is un-closeable once s(N-1) is discarded. *)
(*   RAWCT_LEMMA_AT "s(N-1)" registers the WBN_RAWCT_READ !m form at the    *)
(*   source state, and RESOLVE_LDP2_TAC (RESOLVE_QREG_C, Sec 10c) rewrites   *)
(*   read Qk sN into the SPEC form bytes_to_int128 (SUB_LIST                 *)
(*   (16*(8*(i+1)+m),16) ibytes).  The stepper then PROPAGATES this          *)
(*   state-independent RHS forward at the current state, so it survives     *)
(*   every later discard.  m = 0..7 for Q8..Q15 in load order.               *)
(*                                                                            *)
(* (B) Store window 310..340 + counter folds: the counter regs Q0..Q4 must be *)
(*   REV32_FOLD/CTR_INCR_NORM-folded DURING the store window (REV32_FOLD     *)
(*   "Q25" s326, CTR_INCR_NORM s335): compound raw counter towers with many  *)
(*   un-folded nested adds are out of reach of WORD_BLAST.                    *)
(*                                                                            *)
(* (C) Trivial closers: pointer advances = CONV_TAC WORD_RULE; Q5-Q7          *)
(*   plaintext = GSYM AES256_XOR_ENCRYPT_RECONSTRUCT + GCM_CTR_INC*_LANES +   *)
(*   WORD_RULE (tail closer, <=8-block chain); [store-forall] ASM_CASES       *)
(*   j<8*(i+1); [htable] REWRITE htable_mem_dec + let_CONV + ASM_REWRITE;     *)
(*   [MAYCHANGE] MONOTONE_MAYCHANGE_TAC.                                       *)
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

(* ------------------------------------------------------------------------- *)
(* 10c. Loop-body close machinery.                                            *)
(*                                                                            *)
(* The full body sim + postcondition close.  The sim (below) uses a          *)
(* KEEPDATA stepper that keeps Q0..Q19 latest (incl. the AES keystream        *)
(* Q0-Q7, which the store read-backs need).  Resolve-at-load for Q8-Q15 uses  *)
(* RESOLVE_LDP2_TAC: the ldp leaves  read Qk s(N) = read(mem@ADDR) s(N-1)     *)
(* (memory read at the LOAD-INPUT state s(N-1)), so the raw !m lemma must be  *)
(* matched AT s(N-1), not s(N).  RESOLVE_QREG_C matches the raw lemma at the *)
(* register-read's own memory-state and uses PURE_ONCE_REWRITE (plain REWRITE *)
(* collapses 8*(i+1)+0 -> 8*(i+1), breaking the m=0 ACCEPT).                  *)
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
(* The per-step fold here uses ONE pass of GCM_SIMD_SIMPLIFY_CORE_TAC, not
   the shared double-pass GCM_SIMD_SIMPLIFY_TAC.  The second pass exists (in the
   lemmas file) to reach a REV64 fixpoint that a single pass can miss on a few
   steps -- but under KEEPDATA (which discards stale old-state reads after every
   step) the body sim reaches its self-contained cut-points without that extra
   fold: WBN_MAIN_LOOP_raw and WBN_PREPRETAIL_EXT2 (the ONLY two KEEPDATA-SIMP
   users) both close with a single core pass.  KEEPGH (tails/fronts) and every
   other consumer keep the double-pass GCM_SIMD_SIMPLIFY_TAC.
   The pass is also Q-scoped and fixpoint-memoized, as gcm_simd_fixpt_tbl and
   gcm_simd_kgh_tbl are for the other steppers: its rules (REV64 lanes /
   WORD_SWAP_HALVES / EXT8_LANE0 / REV32_LANE_SUBWORD) can ONLY fire on a
   `read Qn s = <tower>` assumption, so the O(1) `read Qn` head is guarded
   before the rewrites, and a Q-read whose concl is a known F-fixpoint (table
   gcm_simd_kd_tbl) is skipped.  apply_F = the SAME 3 passes as
   GCM_SIMD_SIMPLIFY_CORE_TAC, so this is BIT-IDENTICAL by construction.  The
   cache is reset per body via CLEAR_KEEPDATA_MEMO_TAC (after each
   ENSURES_INIT in the 2 consumers) so each `prove` is hermetic. *)
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
(* outright drop reads of the listed regs at ANY state (the GHASH cluster and
   dead scratch regs, dropped before the store-forall close to shrink the
   pile). *)
let DISCARD_QREGS_TAC qns : tactic =
  DISCARD_ASSUMPTIONS_TAC(fun th -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(n,_)),Var(_,_))),_) -> List.mem n qns
    | _ -> false);;

(* RESOLVE_QREG_C qreg scur m: matches the raw !m lemma AT
   the state of the register-read's embedded memory read (sload = s(N-1) for an
   ldp), not any state; and PURE_ONCE_REWRITE (not REWRITE) so the m=0 index
   8*(i+1)+0 is not collapsed to 8*(i+1) before ACCEPT. *)
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
   (GSYM aes13 + GCM_CTR_INC_ITER_AS_ADD) and bridge the SUB_LIST index. *)
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
  (* Fire the store-readback hyp (ASM_REWRITE) BEFORE folding the raw
     aese/aesmc tower: with GSYM aes13 first, the goal LHS is still
     `read(mem) s340` (tower not yet substituted), so the fold has nothing to
     match and REFL_TAC fails on the 8 new-block legs. *)
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM aes13] THEN REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD] THEN
  REWRITE_TAC (canon @ subbr) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM aes13] THEN REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD] THEN
  REWRITE_TAC (canon @ subbr) THEN REFL_TAC;;
(* fold the machine keystream tower to aes13 + bridge gcm_ctr_add/inc_iter, for
   the plaintext register conjuncts [0-2] (Q5,Q6,Q7). *)
let PLAINTEXT_CLOSE_TAC =
  REWRITE_TAC[GSYM aes13] THEN REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(8*i+8)+5 = 8*i+13`; ARITH_RULE `(8*i+8)+6 = 8*i+14`;
              ARITH_RULE `(8*i+8)+7 = 8*i+15`] THEN
  REFL_TAC;;

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

(* WBN_NBLK_GE_9, also used by the loop body below, is proved before Sec 10b. *)

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

(* the LOOP theorem: PC=0x4c0 /\ core 0  ==>  PC=0xa10 /\ core k, over the front
   MAYCHANGE frame.  Entry/exit are trivial reflexive ensures (pre=post at the
   respective PC); count<>0 is DIVISION arithmetic (17<=nblk => (nblk-9)DIV8>=1).
   Body = the loop step case, proved inline in WBN_MAIN_LOOP_raw below. *)
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
    (* 2. entry: PC=0x4c0 /\ core 0 -> same (0-step reflexive ensures) *)
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC;
    (* 3. ======================== LOOP BODY ======================== *)
    (* After `REPEAT STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core_raw] THEN    *)
    (* CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0"`, state   *)
    (* s0 is at 0x4c0, iteration i, with:                                       *)
    (*   X0=in_p+128(i+1) X2=out_p+128(i+1) X4=in_p+16nblk                     *)
    (*   X5=128*((nblk-1)DIV8)+in_p X1=128nblk X9=16nblk X10=sp+64 X11=key_p   *)
    (*   X3=xi_p X6=htbl_p X16=ivec_p X15=word 4294967296 SP=stackpointer      *)
    (*   Q0..Q4 = gcm_ctr_add(8i+8..8i+12) ctr0   (store/counter stream ahead) *)
    (*   Q5,Q6,Q7 = plaintext(8i+5,8i+6,8i+7)                                  *)
    (*   Q8..Q15 = raw ct blocks 8i+0..8i+7        (GHASH stream lags)         *)
    (*   Q19 = ghash_polyval_acc over blocks 0..8i-1                           *)
    (*   Q26=k12 Q27=k13 Q28=k14 Q31=word 79228162514264337593543950336        *)
    (*   Q30 = gcm_ctr_raw (word (8i+13)) ctr0  (read by the body's first      *)
    (*         instr rev32 v5,v30; advances 8i+13 -> 8i+21).                    *)
    (* 340 instrs, body 0x4c0..0xa0c.  Target: core(i+1) at                     *)
    (* PC = if i+1<k then 0x4c0 else 0xa10.                                     *)
    (*                                                                          *)
    (*  TWO per-instruction folds keep the counter terms flat:                 *)
    (*  (a) COUNTER-INPUT rev32 v_,v30:  REV32_FOLD_TAC "Q<d>" "s<n>"           *)
    (*        `word (8*i+13+j):32 word`  (j=0,1,2,... per rev32).               *)
    (*  (b) COUNTER INCREMENT add v30,v30,v31: fold Q30 back to gcm_ctr_raw     *)
    (*        ONCE PER add (before the next add re-nests the +1s), so only     *)
    (*        the single-+1 GCM_CTR_RAW_INCR fires (CTR_INCR_NORM_TAC).        *)
    (*                                                                          *)
    (* GHASH close via GHASH_ACC_8BLOCK_EXTEND (blk := \k. bytes_to_int128     *)
    (* (SUB_LIST(16*k,16) ibytes)).  Counter compose: GCM_CTR_ADD_COMPOSE /    *)
    (* GCM_CTR_INC_ITER_AS_ADD.  Signed back-edge b.lt @0xa0c resolved inside the *)
    (* body by WB_PTRCMP_FLAGS (x0 vs x5) + WBN_PC_BRIDGE: PC lands EXACTLY at  *)
    (* if i+1<(nblk-9)DIV8 then pc+1216 else pc+2576.                           *)
    (* ===================================================================== *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core_raw] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0" THEN
    CLEAR_KEEPDATA_MEMO_TAC THEN  (* reset the KEEPDATA normalizer fixpoint cache *)
    RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
    (* htable unfold+split @s0: resolve the 13 H-power memory cells *)
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
    FIRST_X_ASSUM(fun th ->
      let c = concl th in
      if can (find_term (fun t->match t with Const("byteswap128",_)->true|_->false)) c &&
         can (find_term (fun t->match t with Const("karatsuba_mid",_)->true|_->false)) c
      then STRIP_ASSUME_TAC th else NO_TAC) THEN
    (* ===================================================================== *)
    (* full body sim (KEEPDATA -- keeps Q0..Q19 incl keystream) + postcond     *)
    (* close, driven end-to-end (s0..s340, PC exact).  Resolve-at-load via     *)
    (* RESOLVE_LDP2_TAC (the ldp memory read stays at the LOAD-INPUT state).   *)
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
    (* --- Q19 WIRE-IN: instead of DISCARDing the GHASH cluster,                  *)
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
       the plaintext + Q8-Q15 (already resolved) + Q19 + store-forall. *)
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
       (* [3] Q19 GHASH acc -- wire-in close: the goal is
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
    (* 4. exit: PC=0xa10 /\ core k -> same (0-step reflexive ensures) *)
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]);;
(* --- mid-load heap compaction after WBN_MAIN_LOOP_raw (loop-body induction). --- *)
Gc.compact();;

(* ========================================================================= *)
(* Section 11. PREPRETAIL (0xa10..0xef4 straight-line sim).                   *)
(*                                                                            *)
(* The loop-exit state (WBN_MAIN_LOOP_raw postcond: PC=pc+0xa10, wbn_loop_inv_core_raw *)
(* at k=(nblk-9)DIV8, GHASH lagging one 8-block group) is driven through the   *)
(* prepretail code (0xa10..0xef4, 313 instrs) to the SHARED TAIL SEAM at       *)
(* pc+3828 (=0xef4), the exact state every <=8-block WB_TAIL_r_TAC consumes  *)
(* (ENSURES_INIT_TAC "s265" on q_at r = the <=8-block chain's                 *)
(* wb_front_postcond[nblk:=r]).                                               *)
(*                                                                            *)
(* SEAM CONTRACT:                                                             *)
(*  - The tail seam is at pc+3828 (0xef4), NOT 0xee0.  The prepretail sims     *)
(*    THROUGH 0xee0..0xef0 (ext v16; sub x5,x4,x0; cmp; ldr q9,[x0],#16; ldp   *)
(*    q24,q25,[x6,#160]) to set up the tail's Q9/Q24/Q25/X0/X5 registers.      *)
(*  - In the <=8 band the FRONT folds 0 GHASH blocks (Q19=word_bytereverse xi) *)
(*    and the TAIL folds all r.  The prepretail is the pipelined analogue: it  *)
(*    folds the FINAL in-flight 8-block group (blocks 8k..8k+7) into Q19       *)
(*    (catching the lagging GHASH stream up), and computes AES keystreams for  *)
(*    the tail's Q0..Q7.                                                       *)
(*  - RECOMPOSE SUBSTITUTION (fully determined by the s313 state): the        *)
(*    prepretail postcond = wb_front_postcond instantiated with                *)
(*      ctr0'   := gcm_ctr_add (word (8*(k+1))) ctr0   (tail's shifted counter) *)
(*      in_p'   := word_add in_p  (word (128*(k+1)))                            *)
(*      out_p'  := word_add out_p (word (128*(k+1)))                            *)
(*      nblk'   := r = nblk - 8*(k+1)   (1..8)                                  *)
(*      xi'     := the caught-up ghash acc over all 8*(k+1) processed blocks    *)
(*      ibytes' := the last r blocks of ibytes                                 *)
(*    Q0..Q7 reconcile via GCM_CTR_ADD_COMPOSE:                                 *)
(*      gcm_ctr_add(8k+8+i) ctr0 = gcm_ctr_inc^i (gcm_ctr_add(8(k+1)) ctr0).    *)
(*                                                                            *)
(* The sim itself is WBN_PREPRETAIL_EXT2_TAC (below).                         *)
(*                                                                            *)
(* s313 register facts (k=(nblk-9)DIV8):                                     *)
(*   PC = pc+3828                                        [matches seam]         *)
(*   Q0..Q7 = aes13(gcm_ctr_add(8k+8..8k+15) ctr0) k0..k13   [ctr shift]        *)
(*   Q24 = karatsuba_mid h8 || karatsuba_mid h7 ; Q25 = h8   [reloaded @0xef0]  *)
(*   Q16/Q19 = GHASH acc staging   (caught up: see wbn_caught_up)            *)
(*   X0 = in_p+128(k+1)+16 ; X2 = out_p+128(k+1) ; X4 = in_p+16nblk             *)
(*   X5 = (in_p+16nblk)-(in_p+128(k+1)) = word(16*r)                            *)
(*   X1=128nblk X9=16nblk X10=sp+64 X11=key_p X3=xi_p X6=htbl_p X16=ivec_p      *)
(*   X15=2^32 Q31=2^96 SP=stackpointer ; [sp+64]=0xC2..; keys k0..k14; htable;  *)
(*   store-forall j<8*(k+1); input buffer -- all preserved.                    *)
(*   NF/ZF/CF/VF on word_sub(in_p+16nblk)(in_p+128(k+1)) vs 112 [-> r=... calc] *)
(* ========================================================================= *)

(* The s313 state of the prepretail sim, built like wb_front_postcond.  This raw
   postcondition states Q16/Q19 at a FRESH unconstrained xi'
   (read Q19 s = word_bytereverse xi', Q16 = its staging).  As written that is
   FALSE (word_bytereverse is a bijection + the ARM model is deterministic, so
   `!xi'. hyps ==> ensures ... Q19 = word_bytereverse xi'` cannot hold).  It is
   kept as `_raw` only as the substitution source; the SOUND post
   `wbn_prepretail_post` below pins xi' to the real caught-up accumulator. *)
let wbn_prepretail_post_raw =
  let ctr j = subst [mk_small_numeral j,`jjj:num`]
    `gcm_ctr_add (word (8 * (nblk - 9) DIV 8 + jjj)) ctr0` in
  wbp_post
  ([`aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
    `read PC s = word (pc + 3828)`;
    wbp_rd `Q24` (wbp_hmid 7);
    wbp_rd `Q25` (wbp_hpow 8)] @
   wbp_cmpi_flags `word_sub (word_add in_p (word (16 * nblk)))
                            (word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1)))):int64` 112 @
   [`read Q16 s = word_subword (word_join (word_bytereverse (xi':int128)) (word_bytereverse xi'):256 word) (64,128)`;
    wbp_rd `Q7` (wbp_aes13 (ctr 15));
    wbp_rd `Q6` (wbp_aes13 (ctr 14));
    wbp_rd `Q0` (wbp_aes13 (ctr 8));
    wbp_rd `Q1` (wbp_aes13 (ctr 9));
    `read (memory :> bytes64 (word_add stackpointer (word 64))) s = word 13979173243358019584`;
    `read X11 s = key_p`;
    `read X9 s = word (16 * nblk)`;
    `read SP s = stackpointer`;
    `read X1 s = word (128 * nblk)`;
    `read X2 s = word_add out_p (word (128 * ((nblk - 9) DIV 8 + 1)))`;
    `read X3 s = xi_p`;
    `read X6 s = htbl_p`;
    `read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes`] @
   wbp_key_reads @ wbp_htable_reads @ wbp_ctx `xi':int128` @
   [wbp_rd `Q5` (wbp_aes13 (ctr 13));
    wbp_rd `Q2` (wbp_aes13 (ctr 10));
    wbp_rd `Q4` (wbp_aes13 (ctr 12));
    wbp_rd `Q3` (wbp_aes13 (ctr 11));
    `read X5 s = word_sub (word_add in_p (word (16 * nblk)))
                          (word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1))))`;
    `read X0 s = word_add (word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1)))) (word 16)`]);;

(* The caught-up GHASH tag: the loop invariant's Q19 shape at index
   i := k+1 = (nblk-9)DIV8 + 1, i.e. the fold over ALL 8*(k+1) processed blocks.
   This IS the true machine value of Q19 at the prepretail seam (the loop exits
   with the GHASH stream lagging 8 blocks; the prepretail folds the final
   in-flight 8-block group, catching it up to 8*(k+1)).  It is a FUNCTION of
   the pinned inputs (xi/h/ibytes/nblk from wb_front_vars), NOT a fresh
   unconstrained var. *)
let wbn_caught_up = `ghash_polyval_acc (byteswap128 (h:int128)) (word_bytereverse (xi:int128))
    (MAP word_bytereverse
    (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) (ibytes:byte list)))
                 (8 * (((nblk:num) - 9) DIV 8 + 1))))`;;

(* Replace the raw postcondition's fresh `word_bytereverse xi'` (which occurs ONLY in the Q16
   staging and Q19 conjuncts) with the caught-up accumulator.  This drops
   xi' entirely (so the post's frees are exactly wb_front_vars) and turns:
     Q19 = word_bytereverse xi'  -->  Q19 = wbn_caught_up   (matches the i:=k+1 invariant shape)
     Q16 = word_subword(word_join (word_bytereverse xi')(word_bytereverse xi'))(64,128)
        -->  Q16 = word_subword(word_join wbn_caught_up wbn_caught_up)(64,128)  (staging of Q19) *)
let wbn_prepretail_post =
  subst [wbn_caught_up, `word_bytereverse (xi':int128)`] wbn_prepretail_post_raw;;

(* the shifted-front prepretail postcondition.
   Built from the s313 state after the 313-instr sim + wb_front_fold_tac, with the
   loop-un-tracked memory cells DROPPED (sound; see below) and the two GHASH
   staging regs Q16/Q19 stated at the caught-up tag.
   Deltas vs a naive vsubst of the <=8-block chain's wb_front_postcond:
    - Q0..Q7 = aes13 (gcm_ctr_add (word (8*k+8+i)) ctr0) k0..k13 (i=0..7, k=(nblk-9)DIV8);
      the shifted-front form is aes13 (gcm_ctr_inc^i ctr0') with
      ctr0'=gcm_ctr_add(8(k+1))ctr0.
    - X0=in_p+128(k+1)+16, X2=out_p+128(k+1), X5/flags on word_sub(in_p+16nblk)(in_p+128(k+1)).
    - DROPPED (loop invariant does not track them; objdump 0xf0c..0x11e8 shows the tail
      only STORES ivec_p (str q30,[x16]@0x1164) and xi_p (st1 v19,[x3]@0x11cc) at the very
      end and never READS their pre-values):
        read (memory :> bytes128 xi_p) s = xi     (front seed; tail uses Q19, not this)
        read (memory :> bytes128 ivec_p) s = ctr0
        read (memory :> bytes64 (sp+72)) s = word 0   (only [sp+64] is the reduce const)
        read (memory :> bytes128 in_p) s = <block0>   (Q9; the tail re-loads via ldr q9,[x0])
      Also DROPPED Q9 = <first tail block> (tail reloads it).  The tail leg
      (WB_TAIL_r) is proved from this weaker post -- WB_TAIL_r_TAC never consumes
      the dropped facts (no xi_p/ivec_p reads, and it re-loads Q9).
    - Q16/Q19 caught-up tag: pinned to `wbn_caught_up` (the i:=k+1 invariant
      Q19 shape, a function of the pinned inputs), not a fresh variable.
      Q19 = wbn_caught_up, Q16 = its staging. *)

(* index bound for the first-tail-block lane, 9<= variant (8*k+8 < nblk).
   Consumed by the unified prepretail sim WBN_PREPRETAIL_EXT2_UNIFIED and by
   the FRONT-916 / PREP_TO_END_916 chain below. *)
let WBN_Q9_INDEX_LT_9 = prove
 (`!nblk. 9 <= nblk /\ 128 * nblk < 2 EXP 64 ==> 8 * ((nblk - 9) DIV 8) + 8 < nblk`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL[`nblk - 9`;`8`] DIVISION) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = (nblk - 9) DIV 8` THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Section 12. Recompose the nblk>8 chain.                                    *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*  -- the OUTPUT-STORE-FORALL augmentation of the prepretail post.            *)
(*                                                                            *)
(* wbn_prepretail_post (64 conjuncts) DROPS the loop                          *)
(* invariant's quantified output-store conjunct                               *)
(*   !j. j < 8*((nblk-9)DIV8 + 1) ==>                                         *)
(*       read (memory :> bytes128 (word_add out_p (word (16*j)))) s =         *)
(*       word_xor (word_xor (bytes_to_int128 (SUB_LIST (16*j,16) ibytes))     *)
(*                (aes13 (gcm_ctr_inc_iter j ctr0) k0..k13)) k14              *)
(* Those are the first 8*(k+1) DECRYPTED output blocks.                     *)
(* The final per-block output post needs stores for ALL nblk blocks;          *)
(* the tail leg (WB_TAIL_r) produces only the last r = nblk-8*(k+1),          *)
(* so the first 8*(k+1) MUST be carried through the seam.  The prepretail      *)
(* region (0xa10..0xef4) does ZERO output stores (objdump), so the forall      *)
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

(* ------------------------------------------------------------------------- *)
(*  -- WBN_Q9_SPEC: the first-tail-block resolver for the seam.                *)
(*                                                                            *)
(* At the prepretail seam (pc+3828) the code has just executed                 *)
(*   eec:  ldr q9, [x0], #16     (x0 = in_p + 128*(k+1) pre-increment)         *)
(* so the sim carries  read Q9 s313 = read (memory :> bytes128                 *)
(*   (word_add in_p (word (128*(k+1))))) s311  -- a RAW memory read.            *)
(* The first tail instruction to read Q9, eor3 v12,v9,v0,v29 @0xefc, reads      *)
(* this Q9 (objdump-confirmed: incoming Q9 is consumed BEFORE any tail reload   *)
(* at 0xfc4), so it MUST reach the tail seam in spec form.  This lemma resolves  *)
(* that raw read to bytes_to_int128 (SUB_LIST (16*8*(k+1),16) ibytes) = the      *)
(* first tail block (global block 8*(k+1)) via INPUT_BYTES_TO_BYTE128_LANES at    *)
(* lane 8*(k+1), given 8*(k+1) < nblk (WBN_Q9_INDEX_LT_9) and the preserved      *)
(* whole-buffer input-bytes fact.  hyps=0.                                       *)
(* USE: add read Q9 = <this RHS> to the prepretail post, resolve                 *)
(* it in the sim right before ENSURES_FINAL_STATE via                           *)
(*   MP_TAC(SPECL[...] WBN_Q9_SPEC) using the s313 input-bytes fact + the raw    *)
(*   Q9 read (bridge s311->s313 memory equality: no stores 0xeec..0xef4).         *)
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
(* Besides the output forall (carried by EXT), the tail's                     *)
(* first instruction to read Q9, eor3 v12,v9,v0,v29 @0xefc, consumes the        *)
(* INCOMING Q9 before any tail reload (WBN_Q9_SPEC comment) -- so Q9 must reach *)
(* the seam in spec                                                              *)
(* form.  wbn_prepretail_post_ext2 = wbn_prepretail_post_ext /\ the Q9 conjunct *)
(* (read Q9 s = bytes_to_int128 (SUB_LIST (16 * 8 * ((nblk-9) DIV 8 + 1),16)    *)
(* ibytes), aconv WBN_Q9_SPEC at k := (nblk-9) DIV 8).                          *)
(*                                                                            *)
(* Proof route:                                                               *)
(* the ldr q9,[x0],#16 @0xeec (step 312) carries a RAW s311 memory read; the    *)
(* s311->s313 memory-equality bridge is awkward (no s311 MAYCHANGE -- the frame *)
(* is s0->s313 only).  Instead SPLIT the sim at s311 and resolve Q9 THERE: the  *)
(* whole-buffer input-bytes fact is live at s311 under KEEPDATA, x0@s311 =      *)
(* in_p+128*(k+1) confirmed, so MP_TAC'ing WBN_Q9_SPEC (ANTS by WBN_Q9_INDEX_LT_9 *)
(* + ARITH) plants read(mem:>bytes128(in_p+128*(k+1))) s311 = <spec>; the ldr    *)
(* q9 then auto-resolves Q9 to that spec form via ASM_REWRITE.  The rest of   *)
(* the sim is as for EXT.                                                     *)
(* ------------------------------------------------------------------------- *)

(*  (ivec write-back): the prepretail post also
   carries the advanced CTR-block counter register Q30, so the ivec write-back
   conjunct `read (memory :> bytes128 ivec_p) s = word_bytereverse (ctr_block
   nonce (c + nblk))` can be threaded to the exported theorems downstream.
   At the seam the counter has been incremented 3x past the loop-head value
   gcm_ctr_raw (word (8*k+13)) ctr0 (adds at 0xa18/0xa30/0xed4, k=(nblk-9)DIV8),
   landing at gcm_ctr_raw (word (8*k+16)) ctr0.  The third add is un-normalized in
   the NOSIMP reduce window; WBN_PREPRETAIL_EXT2_TAC folds it (CTR_RAW_INCR_FOLD at
   s311 + a WORD_RULE 8k+15+1->8k+16) before ENSURES_FINAL.  Downstream,
   INNER_TAIL_FEED_TAC discharges the shifted tail's Q30 precondition from
   this conjunct (GCM_CTR_RAW_ABSORB_NUM). *)
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
   (idx_lt_thm : `... ==> 8 * ((nblk-9) DIV 8) + 8 < nblk`), run once on the
   unified 9<=nblk band with idx_lt_thm = WBN_Q9_INDEX_LT_9 (see below).
   Recipe: init at the loop invariant (i:=k), counter folds 1..14, KEEPDATA bulk
   15..240; Q19 wire-in (step to s242 where PL/PH/PM=Q17/Q19/Q18
   are complete -- PM's final eor3@0xdd4 is instr 242 -- ABBREV them opaque, then
   the reduce KEEPING Q16-Q19 so the byteform stays small); resolve the incoming
   Q9 at s311 (before ldr q9 @0xeec=step 312) to spec form via WBN_Q9_SPEC +
   idx_lt_thm; ENSURES_FINAL + ASM_REWRITE for the preserved/shifted conjuncts;
   the 2 GHASH conjuncts close via WBN_Q19_PREPRETAIL_CLOSE_TAC. *)
let WBN_PREPRETAIL_EXT2_TAC idx_lt_thm =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core_raw] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0" THEN
  CLEAR_KEEPDATA_MEMO_TAC THEN  (* reset the KEEPDATA normalizer fixpoint cache *)
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

(* One prepretail EXT2 sim serves both bands (17<=nblk and
   WBN_PREPRETAIL_EXT2_916 for 9..16): pre/post/sim are IDENTICAL, and the
   only band-dependent side condition, 8*((nblk-9)DIV8)+8 < nblk for the
   WBN_Q9_SPEC ANTS, follows from the WEAKER 9<=nblk band
   (WBN_Q9_INDEX_LT_9), so a single sim on the unified 9<=nblk band is
   sound and covers both; each band theorem then follows by pure
   hyp-strengthening (MATCH_MP + ASM_ARITH).  The unified band term is built
   with the file's own recursive-replace idiom (17<=nblk -> 9<=nblk), matching
   how wbn_front_hyps_916_tm is built. *)
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

(* 17<=nblk band: a no-sim hyp-strengthening of the unified theorem. *)
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
(*  -- The tail leg (WBN_PREP_TO_END).                                       *)
(*                                                                           *)
(* KEY STRUCTURAL FACT: the <=8-block chain's WB_TAIL_r_TAC tail proofs                    *)
(* already START at pc+3828 -- EXACTLY the EXT2 seam PC -- and drive to      *)
(* pc+4560 (the whole-function exit) (they discharge the r-block             *)
(* GHASH via GMULT{r}_FULL_CORRECT_BA).  The shared per-block back-leg       *)
(* WB_TAIL_GEN2_r -- `ensures arm (weak q_at r) (band_post r) (band_frame r)`*)
(* -- is proved ONCE up front (at the prove_band site)                       *)
(* and reused both by prove_band and here by the nblk>8 recomposition, which *)
(* feeds it by precondition-weakening (no re-simulation).  wbn_dissect_band, *)
(* wbn_tail_drop_lhs5, wbn_weak_q_at5_return and                              *)
(* wbn_tail_backleg_goal5_return plus the                                    *)
(* WB_TAIL_GEN2_1..8 theorems are all defined at that earlier site.          *)
(* ------------------------------------------------------------------------- *)

(* ========================================================================= *)
(*  -- WBN_PREP_TO_END assembly infrastructure.                              *)
(*                                                                           *)
(* Why the shifted tail cannot be fed from wbn_prepretail_post_ext2 with the *)
(* X1/X9 conjuncts of the <=8-block tails: 2 of the non-aconv conjuncts are   *)
(* UNDERIVABLE, not ARITH:                                                    *)
(*    ext2 delivers  read X1 s = word (128 * nblk),  read X9 s = word (16*nblk) *)
(*    but a SPECL'd tail (in_p:=in_p+128(k+1), nblk-role:=r) wants           *)
(*                    read X1 s = word (128 * r),    read X9 s = word (16*r).  *)
(* For nblk = 8*(k+1)+r >= 17 these differ, so ext2_post cannot feed a tail   *)
(* theorem whose X9 is fixed to 16*r.  objdump confirms X1 and X9 are unread  *)
(* in [0xef4,0x11d0); the sound contract drops X1 but retains X9 generically. *)
(* The shifted tail instantiates return_value := word(16*nblk), while a fixed *)
(* band instantiates return_value := word(16*r).                              *)
(* ------------------------------------------------------------------------- *)

(* num_of_bytelist = num_of_wordlist on byte lists (needed by WBN_INPUT_SLICE_GEN). *)
let NUM_OF_BYTELIST_EQ_WORDLIST = prove
 (`!l:byte list. num_of_bytelist l = num_of_wordlist l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[num_of_bytelist; num_of_wordlist; DIMINDEX_8] THEN ARITH_TAC);;

(* Input-read restriction to a slice of length m (= 16*r) at 128*(k+1): the  *)
(* r-block shifted tail reads 16*r input bytes there, m kept symbolic under   *)
(* 128*(k+1)+m <= 16*nblk.  hyps=0.                                           *)
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

(* The 5-cell-drop/generic-X9 weak-precond builders (wbn_tail_drop_lhs5,      *)
(* wbn_weak_q_at5_return, wbn_tail_backleg_goal5_return) and the eight        *)
(* WB_TAIL_GEN2_1..8 back-leg theorems are defined ONCE at the prove_band     *)
(* site; the nblk>8 recomposition below (INNER_TAIL_FEED_TAC / wbn_tail_gen2) *)
(* references the same theorems.                                              *)
(* ------------------------------------------------------------------------- *)
(* WBN_PREP_TO_END_r recipe (the                                              *)
(* reconciliation tactic below takes ext2_post ==>                            *)
(* shifted generic-X9 weak precondition to its trivial residuals -- flags +   *)
(* input-read -- all discharged by the helpers above + a per-subgoal           *)
(* WORD_RULE).                                                                *)
(*                                                                           *)
(* shift_vals r (SPECL order = wb_front_vars minus nblk, then return_value,   *)
(* 28 terms):                                                                *)
(*   [pc; stackpointer;                                                        *)
(*    word_add out_p (word (128*((nblk-9) DIV 8+1)));  xi_p; ivec_p;           *)
(*    word_add in_p (word (128*((nblk-9) DIV 8+1)));   key_p; htbl_p;          *)
(*    SUB_LIST (128*((nblk-9) DIV 8+1), 16*r) ibytes;             (:byte list) *)
(*    word_bytereverse wbn_caught_up;                             (:int128)    *)
(*    gcm_ctr_add (word (8*((nblk-9) DIV 8+1))) ctr0;             (:int128)    *)
(*    k0..k14; h; word(16*nblk)] -- final term is the whole-call X9 count.    *)
(*                                                                           *)
(* WBN_PREP_TO_END_r : ensures arm wbn_prepretail_post_ext2                    *)
(*                       (shifted band_post r) wbn_front_C_tm                   *)
(*   under hyp  nblk = 8*((nblk-9) DIV 8 + 1) + r.  Build via:                  *)
(*   MATCH_MP_TAC ENSURES_FRAME_SUBSUMED (narrow tail frame -> wide ext2 frame  *)
(*     wbn_front_C_tm; SUBSUMED via SUBSUMED_ASSIGNS_BYTES on out_p sub-region  *)
(*     bytes(out_p+128(k+1),16) subsumed bytes(out_p,16*nblk))                  *)
(*   THEN MATCH_MP_TAC ENSURES_PRECONDITION_THM                                 *)
(*     EXISTS_TAC (shifted generic-X9 weak precondition) THEN CONJ_TAC THENL     *)
(*     [ <the pre-implication, tactic below>;                                    *)
(*       MP_TAC(SPECL (shift_vals r) WB_TAIL_GEN2_r) THEN ANTS (nonoverlapping/  *)
(*         LENGTH from ext2 wide hyps; SUB_LIST_LENGTH + 16*r<=remaining) ].      *)
(*                                                                           *)
(* PRE-IMPLICATION tactic  (!s. ext2_post s ==> shifted generic-X9 pre), for     *)
(* r=1, with the helpers:                                                       *)
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
(*   (for the input-read conjunct) MP_TAC(SPECL[...] WBN_INPUT_SLICE_GEN) + ANTS THEN *)
(*   UNDISCH `16*nblk=...` THEN DISCH_THEN(fun th->REWRITE_TAC[th]) THEN          *)
(*   ABBREV_TAC `q=(nblk-9) DIV 8` THEN                                          *)
(*   REWRITE_TAC[the `8*q+N=8*(q+1)+(N-8)` (N=8..15) + `((a+1)+..)=a+j` rules] THEN *)
(*   ASM_REWRITE_TAC[] THEN                                                       *)
(*   REPEAT CONJ_TAC THEN                                                         *)
(*   TRY(AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC) THEN      *)
(*   TRY(CONV_TAC WORD_RULE).                                                     *)
(*                                                                           *)
(* Then WBN_PREP_TO_END = 8-way case split on r = 1+(nblk-9) MOD 8 (r in 1..8 *)
(* for nblk>=17); POST combines the shifted band_post (last r stores +          *)
(* xi_p tag) with ext2's carried output forall [conjunct 64] and folds the tag   *)
(* caught_up ++ [last r blocks] = full-nblk GHASH via GHASH_ACC_APPEND           *)
(* (common/polyval_ghash.ml:62) -- the one genuinely NEW algebra step.  THEN     *)
(* chain onto WBN_FRONT_TO_PREP_EXT2 by ENSURES_TRANS_SIMPLE (EXISTS_TAC          *)
(* wbn_prepretail_post_ext2).                                                     *)
(* ------------------------------------------------------------------------- *)

(* ========================================================================= *)
(*  -- WBN_PREP_TO_END_r: the seam post feeds the shifted r-block tail.      *)
(*                                                                           *)
(* The seam post `wbn_prepretail_post_ext2` (the loop/prepretail EXT2 exit    *)
(* at pc+3828) feeds the shifted r-block tail WB_TAIL_GEN2_r by precondition- *)
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
(* -- like the in_p/out_p clauses of Sec 7 and the (out_p)(sp,80) clause.  In *)
(* the real band contract q_at r, xi_p (out_p,16*r) ivec_p at the size-16     *)
(* (=16*nblk when nblk=1) granularity are present; at the whole-length        *)
(* 16*nblk granularity dissect_band 1 shows only xi_p (ivec_p,16) literally,  *)
(* so all 3 are threaded as SIDE-CONDITIONS on WBN_PREP_TO_END_r              *)
(* (rather than widening wbn_front_hyps_wide_tm, which would mean re-proving  *)
(* the chain).  They flow up to the final theorem's precond and are           *)
(* supplied by the guard/subroutine wrapper (the band contract has them).     *)
(* ------------------------------------------------------------------------- *)

(* SPECL order = wb_front_vars minus nblk, then return_value (28 terms);      *)
(* splices the OCaml value wbn_caught_up (NOT a backtick literal -- that      *)
(* would introduce a free variable).                                         *)
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
    `k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;`k12:int128`;`k13:int128`;`k14:int128`;`h:int128`;
    `word (16 * nblk):int64`];;

(* the 3 side-condition clauses (whole-length granularity). *)
let wbn_prep_to_end_extra_clauses =
  [`nonoverlapping (out_p:int64,16 * nblk) (xi_p:int64,16)`;
   `nonoverlapping (out_p:int64,16 * nblk) (ivec_p:int64,16)`;
   `nonoverlapping (xi_p:int64,16) (ivec_p:int64,16)`];;

(* ========================================================================= *)
(*  -- Tag-fold + output-forall algebra.                                     *)
(*                                                                           *)
(* The per-r seam feed (INNER_TAIL_FEED_TAC + WB_TAIL_GEN2_r) lands a          *)
(* SHIFTED-band post:                                                          *)
(*   - PC = pc+4560 (whole-function exit)                                     *)
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
(* wbn_end_post: PC=pc+4560, the nblk-uniform output forall (aes13 XOR k14      *)
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

(* the nblk-uniform end post (PC + byte count in X9 + output/tag/counter). *)
let wbn_end_post =
  let end_forall = `forall j. j < nblk
    ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
        word_xor (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16) ibytes))
        (aes13 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13)) k14` in
  let tag = `read (memory :> bytes128 xi_p) s =
    word_bytereverse (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      (MAP word_bytereverse
        (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) nblk)))` in
  (* ivec: the whole-buffer counter write-back, spine form
     gcm_ctr_inc_iter nblk ctr0.  FULL_r reconciles the shifted band's
     gcm_ctr_inc_iter r (gcm_ctr_add (word 8(q+1)) ctr0) to this via
     GCM_CTR_INC_ITER_AS_ADD + GCM_CTR_ADD_COMPOSE (8(q+1)+r = nblk). *)
  let ivec = `read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter nblk ctr0` in
  mk_abs(`s:armstate`,
    list_mk_conj [`read PC s = word (pc + 4560)`;
                  `read X9 s = word (16 * nblk)`;
                  end_forall; tag; ivec]);;

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
  (* ivec: with the Q30 conjunct carried in wbn_weak_q_at5_return r,
     the shifted tail precond demands read Q30 = gcm_ctr_raw (word 8)
     (gcm_ctr_add (word (8*(q+1))) ctr0); the EXT2 seam (ext2post, ASM_REWRITE'd in
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

(* r=1 full-post. *)
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
        REWRITE_TAC[ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`; GCM_CTR_INC_ITER_AS_ADD] THEN
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
        (* ivec: shifted band ivec = gcm_ctr_inc_iter 1
           (gcm_ctr_add (word (8*(q+1))) ctr0); reconcile to gcm_ctr_inc_iter nblk
           ctr0 via ITER_ADD + ADD_COMPOSE + nblk = 8*(q+1)+1. *)
        REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD; GCM_CTR_ADD_COMPOSE] THEN
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
(* below and driven by WBN_PREP_TO_END_FULL_r_TAC.                            *)
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
  let common = REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD] THEN
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
        (* ivec: shifted band ivec = gcm_ctr_inc_iter r
           (gcm_ctr_add (word (8*(q+1))) ctr0) -> gcm_ctr_inc_iter nblk ctr0
           via ITER_ADD + ADD_COMPOSE + nblk = 8*(q+1)+r. *)
        REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD; GCM_CTR_ADD_COMPOSE] THEN
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
(* The r=2..8 suffix sim is BAND-AGNOSTIC                                     *)
(* (WBN_PREP_TO_END_FULL_r_TAC uses no `17<=nblk`/`9<=nblk` literal and no      *)
(* band-specific lemma; it only ABBREVs q=(nblk-9)DIV 8 symbolically), and it   *)
(* serves two consumer families (FULL_r on `17<=nblk`, FULL_916_r on            *)
(* `9<=nblk/\ nblk<=16`).  So prove it ONCE on the strictly-weaker UNIFIED      *)
(* band `9<=nblk` (WBN_PREP_TO_END_FREE_r), then derive both consumers by pure  *)
(* hyp-strengthening (the dispatchers wbn_full_thm/wbn_full_916_thm see the     *)
(* same statements).  ens is byte-identical across all three bands (only the    *)
(* front-hyps band conjunct differs), so MATCH_MP_TAC + ASM_ARITH closes.       *)
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
(* --- Gc.compact after the 7 FREE suffix sims (this region's heavy sim cluster;
       each serves both bands); mirrors the file's post-sim
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
(* chain, pc+0x20 -> pc+4560.  WBN_FRONT_TO_PREP_EXT2 ; WBN_PREP_TO_END via     *)
(* ENSURES_TRANS_SIMPLE (both share frame wbn_front_C_tm, and the seam post      *)
(* wbn_prepretail_post_ext2 is aconv between them).  Precond = wbn_front_P_tm    *)
(* (the PC-free front core), post = wbn_end_post (nblk-uniform output forall +   *)
(* GHASH_ACC_APPEND-folded tag over list_of_seq cph nblk).  The 3 side-conds     *)
(* ride the antecedent outward (WBN_PREP_TO_END needs them; the front leg does   *)
(* not); 9<=nblk from 17<=nblk by ARITH.  hyps=0.                               *)
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
(* skip branch 0x4bc (b.ge 0xa10) we have X0 = in_p+128 == X5 = in_p+128, so *)
(* the b.ge is TAKEN -> control goes STRAIGHT to prepretail 0xa10; the main   *)
(* loop body is never executed.  (For nblk>=17, d>=256 so X0<X5 and the b.ge  *)
(* falls through into the loop head 0x4c0 -- that is WBN_FRONT_TO_END's path.) *)
(*                                                                           *)
(* The 9..16 leg is therefore a pure straight-line chain:                     *)
(*   FRONT (0x20 -> 0xa10, b.ge@0x4bc TAKEN)  [WBN_FRONT_TO_PREP_916]          *)
(*   ; PREPRETAIL (0xa10 -> pc+3828, k:=0)    [WBN_PREPRETAIL_EXT2_916]        *)
(*   ; PREP_TO_END (pc+3828 -> pc+4560)       [WBN_PREP_TO_END_916]            *)
(* The FRONT and PREPRETAIL sims are the SAME code as the >=17 versions, only  *)
(* the hyp band (17<=nblk -> 9<=nblk /\ nblk<=16) and the 0x4bc branch         *)
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

(* 0x4bc resolve (b.ge TAKEN, d=128): substitute (nblk-1)DIV8=1, then WB_PTRCMP_FLAGS
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

(* invariant-establishment closer at s288 (mirror of WBN_LOOP_INVARIANT_ENTRY_RAW branch 1). *)
let ENTRY_CLOSER_916 =
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[wbn_loop_inv_core_raw] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
  REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD; GCM_CTR_ADD_1; GSYM GCM_CTR_ADD_LANES] THEN
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

(* postcond target for the front-916 leg = wbn_core_applied 0 at PC 0xa10. *)
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
   wbn_core_applied 0.  Close = ENTRY_CLOSER_916 + WB_PTRCMP tail.  htable is
   UNFOLDED into its reads right after init so they propagate through step 296 (the
   folded htable_mem_dec predicate is not tracked across steps by the stepper). *)
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

(* PREPRETAIL-916 (9..16 band), derived (no sim) from
   WBN_PREPRETAIL_EXT2_UNIFIED by hyp-strengthening (see the note at
   WBN_PREPRETAIL_EXT2_UNIFIED): the shared sim ran on the 9<=nblk band that
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

(* FRONT-916 ; PREPRETAIL-916 composed to the ext2 seam (pc+0x20 -> pc+3828).       *)
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

(* WBN_PREP_TO_END_916: pc+3828 -> pc+4560 for the 9..16 band.  Same 8-way r split *)
(* as WBN_PREP_TO_END but with the 9..16 hyp band; dispatches to the FULL_916_r     *)
(* legs (r-block seam->band reconciliation, symbolic in q, q=0 here).               *)
(*                                                                                  *)
(* WBN_PREP_TO_END_FULL_r_TAC does NOT handle r=1 (case-2/tag close          *)
(* specialise to r>=2 store re-indexing), which is why the >=17 build          *)
(* hand-writes WBN_PREP_TO_END_FULL_1 and only applies the parametric tactic   *)
(* for r=2..8.  The 916 legs mirror that structure:                            *)
(*   FULL_916_1 = the hand-written FULL_1 tactic body (band-agnostic: it works from  *)
(*     the nblk=8*(q+1)+1 equation + the ext2 seam post, not the 17<=/9<= band),      *)
(*   FULL_916_2..8 = WBN_PREP_TO_END_FULL_r_TAC r (the band change is confined to the *)
(*     goal hyps that STRIP_TAC consumes).                                           *)
(* The dispatcher is the WBN_PREP_TO_END 8-way rr=(nblk-9)MOD 8 split over the      *)
(* FULL_916 array.                                                                   *)

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

(* the r=1 leg tactic = body of WBN_PREP_TO_END_FULL_1, as a named           *)
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
        REWRITE_TAC[ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`; GCM_CTR_INC_ITER_AS_ADD] THEN
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
        (* ivec: shifted band ivec = gcm_ctr_inc_iter 1
           (gcm_ctr_add (word (8*(q+1))) ctr0); reconcile to gcm_ctr_inc_iter nblk
           ctr0 via ITER_ADD + ADD_COMPOSE + nblk = 8*(q+1)+1. *)
        REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD; GCM_CTR_ADD_COMPOSE] THEN
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
   once above, with no re-simulation. *)
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

(* WBN_FRONT_TO_END_916: the full 9..16 front->exit chain, pc+0x20 -> pc+4560. *)
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
(* The whole nblk>8 chain is complete: WBN_FRONT_TO_END for >=17 and          *)
(* WBN_FRONT_TO_END_916 for 9..16.  The Q19/Q16 GHASH identity at the loop    *)
(* body and the prepretail sites is closed by the Q19 wire-in                 *)
(* (WBN_MACHINE_REDUCE_IS_PROP3_PACK + WBN_BODY_Q19_REDUCE_CLEAN).            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Tag-side bridge lemmas (sim-free, symbolic nblk).                          *)
(* These reconcile wbn_end_post's tag conjunct to the NIST nist_ghash form at   *)
(* symbolic nblk (the fixed-N LIST_OF_SEQ_NIST_INPUT in the <=8-block chain does not cover a   *)
(* symbolic count).  WBN_TAG_NIST_BRIDGE is the drop-in tag rewrite for the      *)
(* spine postcondition reconcile under the band identifications               *)
(* byteswap128 h = ghash_twist H and xi = word_reversefields 8 tag0.            *)
let MAP_LIST_OF_SEQ = prove
 (`!(g:A->B) f n. MAP g (list_of_seq f n) = list_of_seq (g o f) n`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN GEN_TAC THEN
  ASM_REWRITE_TAC[LIST_OF_SEQ; MAP; o_THM] THEN REWRITE_TAC[o_ASSOC]);;

let LIST_OF_SEQ_NIST_INPUT_SYM = prove
 (`!ibytes N.
     list_of_seq (nist_input_block_bytes ibytes) N =
     MAP word_bytereverse
       (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAP_LIST_OF_SEQ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; nist_input_block_bytes; BREV_RF8_128]);;

let WBN_TAG_NIST_BRIDGE = prove
 (`!(H:int128) h xi tag0 ibytes nblk.
     byteswap128 h = ghash_twist H /\ xi = word_reversefields 8 tag0
     ==> word_bytereverse
           (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
             (MAP word_bytereverse
               (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) nblk))) =
         word_reversefields 8
           (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) nblk))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[NIST_GHASH_IS_POLYVAL; LIST_OF_SEQ_NIST_INPUT_SYM; BREV_RF8_128] THEN
  REWRITE_TAC[GSYM BREV_RF8_128; WORD_BYTEREVERSE_BYTEREVERSE]);;

(* ------------------------------------------------------------------------- *)
(* Output-side bridge lemmas (sim-free, symbolic nblk).                       *)
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

(* gcm_dec_pt_bytes at symbolic nblk: (16 * nblk) DIV 16 = nblk whole blocks.  *)
let GCM_DEC_PT_BYTES_WHOLE_SYM = prove
 (`!nblk ibytes ctr0 rk. 1 <= nblk
     ==> gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk =
         aes_ctr_bytes ctr0 (gcm_dec_blocks_from 0 nblk ibytes) rk`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_dec_pt_bytes] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* POINTWISE data-output support.                                              *)
(*                                                                             *)
(* WHY these exist: the spine's data postcondition is the whole-buffer        *)
(* byte-list form byte_list_at(gcm_dec_pt_bytes(16*nblk)..), which reads as    *)
(* though arbitrary byte lengths were accepted.  The pointwise form           *)
(*   !j. j<nblk ==> read(memory:>bytes128(out_p+16j)) s = EL j (aes_ctr ...)    *)
(* says the routine handles whole blocks and matches the sibling AES-GCM      *)
(* proofs' shape, which the exported theorems use.  Do NOT "simplify" it away *)
(* by folding it back into the byte-list form.                                *)

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
   16 * nblk bytes gcm_dec_pt_bytes is the flattened counter-mode stream over
   the nblk input blocks (GCM_DEC_PT_BYTES_WHOLE_SYM), so each 16-byte slice is
   exactly EL j of it.  The reverse direction:
   BYTE_LIST_AT_1BLOCKS gives byte_list_at -> per-block bytes128, and the repack
   lemma above closes the 16-byte slice back to EL j. *)
let WBN_OUTPUT_POINTWISE = prove
 (`!nblk ibytes ctr0 rk out_p s.
     1 <= nblk /\ 128 * nblk < 2 EXP 64 /\
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
    MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN ARITH_TAC;
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
(* ensures context) -- analogue of the <=8-block chain build_aes_ctr_el, at symbolic j.       *)
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
(* 128*nblk < 2 EXP 64 (from the chain hyps) gives val(word(16*nblk))=16*nblk.  *)
let WBN_END_OUTPUT_BYTE_LIST = prove
 (`!nblk ibytes ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 out_p s.
     1 <= nblk /\ 128 * nblk < 2 EXP 64 /\
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
(* GCM_CTR_INC_ITER_CTR_BLOCK is what lets the exported _CORRECT and         *)
(* _SUBROUTINE_CORRECT name the nonce (via WBN_OUTPUT_POINTWISE_NONCE and    *)
(* GCM_CTR_INC_ITER_NIST_IVEC below).  ctr_block is the shared NIST counter  *)
(* block of arm/proofs/utils/aes_gcm_spec.ml (loaded first, through          *)
(* aes_gcm_common.ml).                                                       *)
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

(* ========================================================================= *)
(* ROADMAP -- how to read the theorems below top-down.                         *)
(*                                                                             *)
(* The TWO EXPORTED contracts (in the shared AES-GCM vocabulary of           *)
(* aes_gcm_spec.ml, at the file END) are                                     *)
(*   AESV8_GCM_8X_DEC_256_WB_SUBROUTINE_CORRECT  (ABI wrapper)                    *)
(*   AESV8_GCM_8X_DEC_256_WB_CORRECT             (after-prologue core it wraps)   *)
(* plus AESV8_GCM_8X_DEC_256_GUARD (reject path, the <=8-block chain).  The     *)
(* two exported contracts are DERIVED, without re-running any sim, from the  *)
(* internal H-free byte-list SPINES, by instantiating the key words, the     *)
(* GHASH key H and the counter block to the shared FIPS-197 convention and    *)
(* restating the input and output per block.  The two spines are:            *)
(*   WBN_DEC_CORE_BYTELIST        (byte_list output, pc+0x20..pc+4560)          *)
(*   WBN_DEC_SUBROUTINE_BYTELIST  (byte_list output, ABI wrapper)               *)
(* The spines carry the full sim/chain proof; everything on top is pure          *)
(* vocabulary lifts, so nothing large propagates and the sims are never re-run.  *)
(*                                                                             *)
(*   _SUBROUTINE_CORRECT / WBN_DEC_SUBROUTINE_BYTELIST  (below)               *)
(*     = prologue (guard fall-through + d8-d15 spills)                          *)
(*       ; WBN_DEC_CORE_BYTELIST                 <- the core, pc+0x20..pc+4560  *)
(*       ; epilogue (restore d8-d15 + ret)                                      *)
(*                                                                             *)
(*   WBN_DEC_CORE_BYTELIST   (below)  -- one core contract for ALL            *)
(*   nblk>=1, by a 3-way split on the block count (3 control-flow paths):       *)
(*     nblk <= 8   : AESV8_GCM_8X_DEC_256_DISPATCH   (the <=8-block chain; loop skipped)    *)
(*     9 <= nblk<=16: WBN_FRONT_TO_END_916             (loop entered 0 times)   *)
(*     nblk >= 17  : WBN_FRONT_TO_END                  (loop entered >=1 time)  *)
(*   WBN_CHAIN_TO_NIST_TAC bridges the two >8 chains (raw per-block vocab) to    *)
(*   the NIST DISPATCH vocab (see the WBN_DEC_CORE_BYTELIST note below).      *)
(*                                                                             *)
(*   Each >8 chain factors, via ENSURES_TRANS_SIMPLE, into the four segments    *)
(*   the binary runs in sequence (entry pc+0x20 -> exit pc+4560):               *)
(*     FRONT       WBN_FRONT_BUF / _EXT / _EXT2      pc+0x20  -> loop head 0x4c0 *)
(*     LOOP        WBN_MAIN_LOOP_raw (ENSURES_WHILE)     0x4c0    -> 0x4c0 (per iter)*)
(*     PREPRETAIL  WBN_PREPRETAIL / _EXT / _EXT2     0xa10    -> tail entry 3796 *)
(*     TAIL        WBN_PREP_TO_END(_FULL) / _916     3796     -> 4528            *)
(*   Composed as:  WBN_FRONT_TO_PREP(_EXT2)          = FRONT ; LOOP ; PREPRETAIL *)
(*                 WBN_FRONT_TO_END(_916)            = FRONT_TO_PREP ; TAIL      *)
(*   (the _916 spelling is the 9..16 leg where LOOP runs 0 times; the _EXT/     *)
(*    _EXT2 spellings widen the carried invariant/output vocab across seams).    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* WBN_DEC_CORE_BYTELIST -- all nblk >= 1 (H free,                            *)
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
(* DROPPED (just 1<=nblk) and the two size bounds 128*nblk<2 EXP 64 /            *)
(* val in_p+16*nblk<2 EXP 63 ADDED to the antecedent (genuine preconditions the  *)
(* subroutine wrapper/guard supplies -- for nblk<=8 they follow from small    *)
(* nblk; for symbolic large nblk they must be assumed to avoid pointer/length *)
(* overflow).                                                                 *)

(* The statement is spelled out literally (XTS style) so the
   reader sees the full pre/post/frame contract first.  It is the DISPATCH
   ensures-body verbatim, with the `nblk<=8` bound replaced by `1<=nblk` plus the
   two size bounds the subroutine wrapper/guard supplies (128*nblk<2 EXP 64 and
   val in_p+16*nblk<2 EXP 63 -- for nblk<=8 they follow from small nblk; for
   symbolic large nblk they rule out pointer/length overflow).  This spine keeps
   H free and the output as the whole-buffer byte list; the exported _CORRECT
   below pins H and restates the output pointwise.  The load-time soundness gate
   re-derives this spine statement from the _DISPATCH statement by term surgery and
   asserts aconv-equality, so any drift of this literal fails the load (see the
   `let () = ...` gate at end of file). *)

let WBN_DEC_CORE_BYTELIST = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk ibytes rk H
    tag0 ctr0.
    1 <= nblk /\
    128 * nblk < 2 EXP 64 /\
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
              read X9 s = word (16 * nblk) /\
              byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p
              (word (16 * nblk)) s /\
              read (memory :> bytes128 xi_p) s =
              word_reversefields 8
              (nist_ghash H tag0
              (list_of_seq (nist_input_block_bytes ibytes) nblk)) /\
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
     vocab; these helper lets are local to the proof. *)
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
          (* ivec: the spine ivec conjunct is IDENTICAL raw
             vs NIST (idsub touches neither ctr0 nor gcm_ctr_inc_iter), so the
             outer ASM_REWRITE_TAC[] already discharged it -- this leg is the tag
             ALONE, a single conjunct (so no CONJ_TAC here). *)
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
(* WBN_DEC_SUBROUTINE_BYTELIST -- the ABI subroutine                          *)
(* wrapper spine (H free, byte_list output; the exported _SUBROUTINE_CORRECT   *)
(* is lifted from it below).                                                   *)
(* The ABI subroutine wrapper for the whole-blocks path (bit_len = 128*nblk,   *)
(* any nblk >= 0).  The nblk = 0 leg is folded in (the entry cbz x1            *)
(* is TAKEN, returns 0, empty output, tag unchanged) so this single theorem is  *)
(* the external whole-blocks contract.  The nblk >= 1 leg (below) runs the    *)
(* guard fall-through, the prologue, the core and the epilogue.               *)
(* Binary                                                                       *)
(* layout (objdump): the entry GUARD (bti c;cbz x1;tst x1,#127;b.ne, offs      *)
(* 0x0..0xc) precedes the d8-d15 callee-save spills (stp d8,d9,[sp,#-80]!;      *)
(* stp d10,d11;d12,d13;d14,d15, offs 0x10..0x1c); the core runs pc+0x20..pc+   *)
(* 0x11cc (= the core); the epilogue (mov x0,x9; ldp d10..d15; ldp d8,d9,[sp], *)
(* #80; ret, offs 0x11d0..0x11e4) restores.  X30 is NOT saved (returns via LR).*)
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
(*    16*nblk (from 128*nblk<2 EXP 64) so ARM_STEPS carries the quantified      *)
(*    input byte read past the disjoint stack stores (else it drops it);        *)
(*  - WB_GUARD_FALLTHROUGH_TAC injects the guard fall-through facts             *)
(*    (val(word(128*nblk))=128*nblk; ~(128*nblk=0); val(word_and .. 127)=0) so  *)
(*    the prologue steps clean; then ARM_STEPS 1--8 (guard+saves), ARM_BIGSTEP  *)
(*    s9 (crosses the core), ARM_STEPS 10--15 (epilogue), ENSURES_FINAL.        *)
(* The d8-d15 preservation closes because the core's stack frame              *)
(* bytes(sp+64,16) is DISJOINT from the [sp,64) spill area.                     *)
(* ------------------------------------------------------------------------- *)

let WBN_DEC_SUBROUTINE_BYTELIST = prove
   (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk ibytes rk H
      tag0 ctr0 returnaddress.
      128 * nblk < 2 EXP 64 /\
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
               C_RETURN s = word (16 * nblk) /\
               byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p
               (word (16 * nblk)) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
               (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) nblk)) /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter nblk ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE
           [memory :> bytes (out_p,16 * nblk); memory :> bytes (xi_p,16);
            memory :> bytes (ivec_p,16);
            memory :> bytes (word_sub stackpointer (word 80),80)])`,
  (* The wrapper is hand-rolled (see the note above); these helper lets
     are local to the proof. *)
  let EXEC = AESV8_GCM_8X_DEC_256_WB_EXEC in
  (* the core, SP set to the post-prologue in-frame value *)
  let WB_CORE_INST =
    SPECL [`pc:num`; `word_sub stackpointer (word 80):int64`;
           `in_p:int64`; `out_p:int64`; `xi_p:int64`; `ivec_p:int64`;
           `key_p:int64`; `htbl_p:int64`; `nblk:num`; `ibytes:byte list`;
           `rk:int128 list`; `H:int128`; `tag0:int128`; `ctr0:int128`]
          WBN_DEC_CORE_BYTELIST in
  (* val(word(16*nblk))=16*nblk from 128*nblk<2 EXP 64 (so 16*nblk<2 EXP 64) *)
  let VAL16EQ = prove
   (`128 * nblk < 2 EXP 64 ==> val (word (16 * nblk):int64) = 16 * nblk`,
    DISCH_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    ASM_ARITH_TAC) in
  (* unfold folded input mem preds + concretize the byte bound in the core *)
  let WB_CORE_INST_UF2 =
    REWRITE_RULE[byte_list_at; wordlist_from_memory; HTABLE_MEM_8_FLAT; DIMINDEX_128;
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
  REWRITE_TAC[byte_list_at; wordlist_from_memory; HTABLE_MEM_8_FLAT; DIMINDEX_128;
                fst EXEC] THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; PAIRWISE; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    (* nblk = 0: the entry cbz x1 (0x4) is TAKEN before the prologue, so the
       function returns 0 in X0 touching no memory (mov w0,#0; ret @0x1740);
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
(* c.  Combines WBN_OUTPUT_POINTWISE (byte_list -> EL j of aes_ctr),             *)
(* EL_AES_CTR (element = pt XOR E_K(counter)) and GCM_CTR_INC_ITER_CTR_BLOCK    *)
(* (our gcm_ctr_inc_iter counter = the byte-reversed NIST nonce||(c+j) block).  *)
(* ------------------------------------------------------------------------- *)
let WBN_OUTPUT_POINTWISE_NONCE = prove
 (`!nblk ibytes ctr0 rk out_p s nonce c.
     1 <= nblk /\ 128 * nblk < 2 EXP 64 /\
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
(* its EL/nist_input_block_bytes byte-list vocabulary back to `inblock`.        *)
(* Sim-free.                                                                    *)
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
     128 * nblk < 2 EXP 64 /\
     (!j. j < nblk
          ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
              inblock j)
     ==> byte_list_at (int128_list_to_bytes (list_of_seq inblock nblk)) in_p
                      (word (16 * nblk)) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[byte_list_at] THEN
  SUBGOAL_THEN `val (word (16 * nblk):int64) = 16 * nblk` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN ARITH_TAC; ALL_TAC] THEN
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

(* identity B: the GHASH input list over the assembled ibytes IS the shared  *)
(* NIST (big-endian) view of inblock.  For decrypt, GHASH runs over the      *)
(* ciphertext, which is the input, so the spines' byte-list view             *)
(* nist_input_block_bytes becomes nist_input_block (aes_gcm_spec.ml).        *)
let NIST_INPUT_OF_ASSEMBLED = prove
 (`!inblock nblk.
     list_of_seq
       (nist_input_block_bytes (int128_list_to_bytes (list_of_seq inblock nblk))) nblk =
     list_of_seq (nist_input_block inblock) nblk`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ_PTWISE THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[nist_input_block_bytes; nist_input_block] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC INBLOCK_OF_ASSEMBLED THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The house AES-256 against the FIPS-197 cipher, and the keystream and the  *)
(* counter write-back in the shared vocabulary (aes_gcm_spec.ml).            *)
(*                                                                           *)
(* The spines state the keystream with the house aes256_encrypt              *)
(* (aes_encrypt_spec.ml) over the round keys as they sit in memory.  The     *)
(* exported theorems use the shared key convention: rk is the FIPS-197        *)
(* schedule, and memory holds MAP (word_reversefields 8) rk.  Both ciphers   *)
(* are the kernel's aese/aesmc tower: AES256_XOR_ENCRYPT_RECONSTRUCT         *)
(* (aes_gcm_reconstruct.ml) folds the tower to aes256_encrypt, and           *)
(* XOR_AES256_CIPHER_RECONSTRUCT (aes_gcm_common.ml) folds it to             *)
(* aes256_cipher, so the two lemmas at a zero data block give the relation.  *)
(* ========================================================================= *)

let AES256_ENCRYPT_AS_CIPHER = prove
 (`!x (rk:int128 list).
     LENGTH rk = 15
     ==> aes256_encrypt x (MAP (word_reversefields 8) rk) =
         word_reversefields 8 (aes256_cipher (word_reversefields 8 x) rk)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP RK_ETA_15) THEN REWRITE_TAC[MAP] THEN
  MP_TAC(SPECL
   (`x:int128` :: `word 0:int128` ::
    map (fun i -> mk_comb(`word_reversefields 8:int128->int128`,
                    mk_comb(mk_comb(`EL:num->int128 list->int128`,
                                    mk_small_numeral i), `rk:int128 list`)))
        (0--14))
   (REWRITE_RULE[aes13] AES256_XOR_ENCRYPT_RECONSTRUCT)) THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  REWRITE_TAC[WORD_BITWISE_RULE `word_xor (word 0) (x:int128) = x`;
              WORD_BITWISE_RULE `word_xor (x:int128) (word 0) = x`;
              MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  DISCH_THEN(ACCEPT_TAC o SYM));;

(* Block j's keystream, as WBN_OUTPUT_POINTWISE_NONCE states it at the       *)
(* exported instantiation, is the shared aes_ctr_block.                      *)
let AES256_ENCRYPT_CTR_AS_AES_CTR_BLOCK = prove
 (`!(nonce:96 word) c j (rk:int128 list).
     LENGTH rk = 15
     ==> aes256_encrypt (word_bytereverse (ctr_block nonce (c + j)))
                        (MAP (word_reversefields 8) rk) =
         aes_ctr_block aes256_cipher c nonce rk j`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[AES256_ENCRYPT_AS_CIPHER] THEN
  REWRITE_TAC[aes_ctr_block; BREV_RF8_128; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[ADD_SYM]);;

(* The counter write-back: the spines' gcm_ctr_inc_iter n, started from the  *)
(* shared ivec value for counter c, is the shared ivec value for n + c.      *)
let GCM_CTR_INC_ITER_NIST_IVEC = prove
 (`!n (nonce:96 word) c.
     gcm_ctr_inc_iter n (word_reversefields 8 (ctr_block nonce c)) =
     word_reversefields 8 (ctr_block nonce (n + c))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `nonce:96 word`; `c:num`;
                `word_reversefields 8 (ctr_block nonce c)`]
    GCM_CTR_INC_ITER_CTR_BLOCK) THEN
  REWRITE_TAC[BREV_RF8_INV_128] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[BREV_RF8_128; ADD_SYM]);;

(* ========================================================================= *)
(* THE EXPORTED CONTRACTS, in the shared AES-GCM vocabulary.                 *)
(*                                                                           *)
(* Both are derived from the H-generic byte-list spines, without re-running  *)
(* any simulation, by the instantiation                                      *)
(*   rk     := MAP (word_reversefields 8) rk  (the memory image of the       *)
(*                                            FIPS-197 schedule rk)          *)
(*   H      := aes256_cipher (word 0) rk      (the NIST GHASH key,           *)
(*                                            E_K(0^128))                    *)
(*   ctr0   := word_reversefields 8 (ctr_block nonce c)                      *)
(*   ibytes := int128_list_to_bytes (list_of_seq inblock nblk)               *)
(* followed by restating the input per block (WBN_INPUT_ASSEMBLE), the       *)
(* output per block over the shared keystream (WBN_OUTPUT_POINTWISE_NONCE,   *)
(* GCM_DEC_BLOCKS_FROM_ASSEMBLED, AES256_ENCRYPT_CTR_AS_AES_CTR_BLOCK), the  *)
(* GHASH input as nist_input_block (NIST_INPUT_OF_ASSEMBLED) and the counter *)
(* write-back (GCM_CTR_INC_ITER_NIST_IVEC).  The key precondition forces     *)
(* LENGTH rk = 15, so the spines' hypothesis LENGTH rk = 15 needs no         *)
(* counterpart: when it fails, the precondition is unsatisfiable.            *)
(*                                                                           *)
(* c is the free counter of data block 0: the kernel increments whatever     *)
(* ivec holds, and c = 2 is the standard NIST SP 800-38D instance.  The SIMD *)
(* frame of the core lists Q0 through Q31 because the machine code writes    *)
(* every one of the 32 vector registers.                                     *)
(* ========================================================================= *)

let WBN_EXPORT_FROM_SPINE_TAC spine =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `LENGTH(rk:int128 list) = 15` THENL
   [ALL_TAC;
    ENSURES_PRECONDITION_TAC `\s:armstate. F` THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM(fun th ->
        let c = concl th in
        if is_eq c &&
           can (find_term (fun t -> is_const t &&
                             fst(dest_const t) = "wordlist_from_memory")) c
        then MP_TAC(AP_TERM `LENGTH:int128 list->num` th) else NO_TAC) THEN
      REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY; LENGTH_MAP] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[ENSURES_TRIVIAL]]] THEN
  MP_TAC(INST
   [`MAP (word_reversefields 8) (rk:int128 list)`,`rk:int128 list`;
    `aes256_cipher (word 0) (rk:int128 list)`,`H:int128`;
    `word_reversefields 8 (ctr_block (nonce:96 word) c)`,`ctr0:int128`;
    `int128_list_to_bytes (list_of_seq (inblock:num->int128) nblk)`,
    `ibytes:byte list`]
   (SPEC_ALL spine)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_INT128_LIST_TO_BYTES; LENGTH_LIST_OF_SEQ;
                    LENGTH_MAP];
    ALL_TAC] THEN
  DISCH_THEN(fun sp ->
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (rand(rator(rator(concl sp)))) THEN CONJ_TAC THENL
     [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WBN_INPUT_ASSEMBLE THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
      EXISTS_TAC (rand(rator(concl sp))) THEN
      CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC sp]]) THEN
  X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[NIST_INPUT_OF_ASSEMBLED; GCM_CTR_INC_ITER_NIST_IVEC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL
   [`nblk:num`;
    `int128_list_to_bytes (list_of_seq (inblock:num->int128) nblk)`;
    `word_reversefields 8 (ctr_block (nonce:96 word) c)`;
    `MAP (word_reversefields 8) (rk:int128 list)`; `out_p:int64`;
    `s:armstate`; `nonce:96 word`; `c:num`] WBN_OUTPUT_POINTWISE_NONCE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[BREV_RF8_INV_128] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[GCM_DEC_BLOCKS_FROM_ASSEMBLED;
               AES256_ENCRYPT_CTR_AS_AES_CTR_BLOCK] THEN
  MATCH_ACCEPT_TAC WORD_XOR_SYM;;

(* THE EXPORTED CORE CONTRACT (after the prologue, bit_len = 128 * nblk).    *)
let AESV8_GCM_8X_DEC_256_WB_CORRECT = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk inblock rk
    tag0 nonce c.
    1 <= nblk /\
    128 * nblk < 2 EXP 64 /\
    val in_p + 16 * nblk < 2 EXP 63 /\
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
              (!j. j < nblk
                   ==> read (memory :> bytes128
                              (word_add in_p (word (16 * j)))) s = inblock j) /\
              read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce c) /\
              wordlist_from_memory (key_p,15) s =
              MAP (word_reversefields 8) rk /\
              htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htbl_p s)
         (\s. read PC s = word (pc + 4560) /\
              read X9 s = word (16 * nblk) /\
              (!j. j < nblk
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block aes256_cipher c nonce rk j)
                                (inblock j)) /\
              read (memory :> bytes128 xi_p) s =
              word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_input_block inblock) nblk)) /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce (nblk + c)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
          [memory :> bytes (out_p,16 * nblk);
           memory :> bytes (xi_p,16);
           memory :> bytes (ivec_p,16);
           memory :> bytes (word_add stackpointer (word 64),16)] ,,
          MAYCHANGE
          [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14;
           Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27;
           Q28; Q29; Q30; Q31])`,
  WBN_EXPORT_FROM_SPINE_TAC WBN_DEC_CORE_BYTELIST);;

(* The whole-block subroutine result for bit_len = 128 * nblk, any nblk      *)
(* including 0: an internal helper for the public arbitrary-length theorem.  *)
let WBN_DEC_VALID_CALL_CORRECT = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk inblock rk
    tag0 nonce c returnaddress.
    128 * nblk < 2 EXP 64 /\
    val in_p + 16 * nblk < 2 EXP 63 /\
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
              (!j. j < nblk
                   ==> read (memory :> bytes128
                              (word_add in_p (word (16 * j)))) s = inblock j) /\
              read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce c) /\
              wordlist_from_memory (key_p,15) s =
              MAP (word_reversefields 8) rk /\
              htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htbl_p s)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word (16 * nblk) /\
              (!j. j < nblk
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block aes256_cipher c nonce rk j)
                                (inblock j)) /\
              read (memory :> bytes128 xi_p) s =
              word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_input_block inblock) nblk)) /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce (nblk + c)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
          [memory :> bytes (out_p,16 * nblk); memory :> bytes (xi_p,16);
           memory :> bytes (ivec_p,16);
           memory :> bytes (word_sub stackpointer (word 80),80)])`,
  WBN_EXPORT_FROM_SPINE_TAC WBN_DEC_SUBROUTINE_BYTELIST);;

(* The number of complete blocks processed by the public decrypt entry point.
   Both entry-reject paths map to zero blocks: a zero bit length is already
   zero under DIV, while a non-multiple of 128 is rejected before any memory
   access.  The name is decrypt-specific so that it cannot clash with an
   encrypt-side counterpart loaded alongside it. *)
let gcm_dec_wb_blocks = new_definition
 `gcm_dec_wb_blocks (bit_len:int64) =
    if val bit_len MOD 128 = 0 then val bit_len DIV 128 else 0`;;

let GCM_DEC_WB_BLOCKS_VALID = prove
 (`!bit_len:int64.
      val bit_len MOD 128 = 0
      ==> val bit_len = 128 * gcm_dec_wb_blocks bit_len`,
  REWRITE_TAC[gcm_dec_wb_blocks] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`val(bit_len:int64)`; `128`]
    (CONJUNCT2 DIVISION_SIMP)) THEN
  ASM_ARITH_TAC);;

(* THE EXPORTED SUBROUTINE CONTRACT (the AAPCS64-callable headline result),
   for an arbitrary bit_len.  gcm_dec_wb_blocks bit_len is the number of
   blocks processed, and every data-dependent clause is indexed by it, so one
   postcondition describes all three paths:
   - a non-multiple of 128 is rejected by the entry guard (cbz falls through,
     tst/b.ne branches to the return), which returns 0 and touches no memory;
   - zero and the nonzero multiples of 128 are WBN_DEC_VALID_CALL_CORRECT at
     bit_len = word (128 * nblk), where 128 * nblk < 2 EXP 64 is just
     VAL_BOUND_64.
   The pointer bound val in_p + 16 * nblk < 2 EXP 63 is genuine: the kernel
   compares pointers with signed conditions.
   This routine does not enforce the NIST GCM message limit. Callers must
   ensure the cumulative message length does not exceed 2^36 - 32 bytes
   (2^39 - 256 bits). *)
let AESV8_GCM_8X_DEC_256_WB_SUBROUTINE_CORRECT = prove
 (`!pc stackpointer in_p bit_len out_p xi_p ivec_p key_p htbl_p inblock rk
    tag0 nonce c returnaddress.
    val in_p + 16 * gcm_dec_wb_blocks bit_len < 2 EXP 63 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
    [out_p,16 * gcm_dec_wb_blocks bit_len; xi_p,16; ivec_p,16]
    [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc;
     in_p,16 * gcm_dec_wb_blocks bit_len; key_p,240; htbl_p,192;
     word_sub stackpointer (word 80),80] /\
    PAIRWISE nonoverlapping
    [out_p,16 * gcm_dec_wb_blocks bit_len; xi_p,16; ivec_p,16] /\
    ALL (nonoverlapping (word_sub stackpointer (word 80),80))
    [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc;
     in_p,16 * gcm_dec_wb_blocks bit_len; key_p,240; htbl_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
              read PC s = word pc /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS
              [in_p; bit_len; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
              (!j. j < gcm_dec_wb_blocks bit_len
                   ==> read (memory :> bytes128
                              (word_add in_p (word (16 * j)))) s = inblock j) /\
              read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce c) /\
              wordlist_from_memory (key_p,15) s =
              MAP (word_reversefields 8) rk /\
              htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htbl_p s)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word (16 * gcm_dec_wb_blocks bit_len) /\
              (!j. j < gcm_dec_wb_blocks bit_len
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block aes256_cipher c nonce rk j)
                                (inblock j)) /\
              read (memory :> bytes128 xi_p) s =
              word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_input_block inblock)
                           (gcm_dec_wb_blocks bit_len))) /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8
                (ctr_block nonce (gcm_dec_wb_blocks bit_len + c)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
          [memory :> bytes
             (out_p,16 * gcm_dec_wb_blocks bit_len);
           memory :> bytes (xi_p,16);
           memory :> bytes (ivec_p,16);
           memory :> bytes (word_sub stackpointer (word 80),80)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `nblk = gcm_dec_wb_blocks bit_len` THEN
  ASM_CASES_TAC `val(bit_len:int64) MOD 128 = 0` THENL
   [(* Whole blocks, including zero: bit_len = word (128 * nblk). *)
    SUBGOAL_THEN `val(bit_len:int64) = 128 * nblk` ASSUME_TAC THENL
     [EXPAND_TAC "nblk" THEN ASM_SIMP_TAC[GCM_DEC_WB_BLOCKS_VALID];
      ALL_TAC] THEN
    SUBGOAL_THEN `128 * nblk < 2 EXP 64` ASSUME_TAC THENL
     [MP_TAC(ISPEC `bit_len:int64` VAL_BOUND_64) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `bit_len:int64 = word (128 * nblk)` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(fun th ->
        if concl th = `val(bit_len:int64) = 128 * nblk`
        then SUBST1_TAC(SYM th) else NO_TAC) THEN
      REWRITE_TAC[WORD_VAL];
      ALL_TAC] THEN
    MATCH_MP_TAC WBN_DEC_VALID_CALL_CORRECT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* A non-multiple of 128: cbz falls through, tst/b.ne rejects, and no
     memory is touched. *)
  SUBGOAL_THEN `nblk = 0` SUBST_ALL_TAC THENL
   [EXPAND_TAC "nblk" THEN REWRITE_TAC[gcm_dec_wb_blocks] THEN
    ASM_REWRITE_TAC[COND_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val(bit_len:int64) = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(val(bit_len:int64) MOD 128 = 0)` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val(word_and (bit_len:int64) (word 127)) = 0)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `127 = 2 EXP 7 - 1` SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 EXP 7 = 128`];
    ALL_TAC] THEN
  REWRITE_TAC[MULT_CLAUSES;ADD_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_SIMD_REGS;MODIFIABLE_GPRS;
              MODIFIABLE_UPPER_SIMD_REGS;C_ARGUMENTS;C_RETURN;SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--6) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[list_of_seq;nist_ghash] THEN
  REWRITE_TAC[ARITH_RULE `j < 0 <=> F`]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let EXEC = AESV8_GCM_8X_DEC_256_WB_EXEC;;

(* ---- quiet stepper: the default one logs a line per state, and these legs
   run several hundred steps each ---- *)
let ARM_QSTEP_TAC th s =
  ARM_STEP_TAC th [] s None (K STRIP_TAC) THEN DISCARD_OLDSTATE_TAC s THEN CLARIFY_TAC;;
let ARM_QSTEPS_TAC th snums = MAP_EVERY (ARM_QSTEP_TAC th) (statenames "s" snums);;

(* ---- GENERAL affine word_sub cancellation (NO WORD_BLAST) ----
   For a `word_sub P Q` subterm whose only free int64 var is a single register base
   x (in_p/out_p/...), the difference P-Q is a constant independent of x. Prove
   `word_sub P Q = word_sub P[x:=0] Q[x:=0]` by WORD_RULE (the x-dependence cancels),
   then WORD_REDUCE the RHS to a numeral `word k`.  Covers the 9-16 loop-enter shape
   `word_sub in_p (word_add (word 128) in_p)` as well as the plain tail compares. *)
let affine_cancel_thm t =
  match t with
  | Comb(Comb(Const("word_sub",_),_),_) ->
    let fv = filter (fun v -> type_of v = `:int64` && is_var v) (frees t) in
    (match fv with
     | [x] ->
       let t0 = subst [`word 0:int64`, x] t in
       let step1 = WORD_RULE (mk_eq(t, t0)) in
       CONV_RULE (RAND_CONV WORD_REDUCE_CONV) step1     (* |- word_sub P Q = word k *)
     | _ -> failwith "affine_cancel_thm: not exactly one int64 var")
  | _ -> failwith "affine_cancel_thm: not word_sub";;

(* Collect every affine word_sub in goal+asms, cancel it, rewrite, then reduce the
   now-concrete PC if-condition. *)
let WB_TAIL_RESOLVE_TAC : tactic = fun (asl,w) ->
  let is_sub tm = match tm with
    | Comb(Comb(Const("word_sub",_),_),_) ->
        length (filter (fun v -> type_of v = `:int64` && is_var v) (frees tm)) = 1
    | _ -> false in
  let all = itlist (fun (_,th) acc -> concl th :: acc) asl [w] in
  let subs = setify (itlist (fun t acc -> find_terms is_sub t @ acc) all []) in
  let cancel_thms = mapfilter affine_cancel_thm subs in
  (RULE_ASSUM_TAC(REWRITE_RULE cancel_thms) THEN
   (* reflexive branch at 0x44c: ival in_p - ival in_p / word_sub X X = 0 *)
   RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL; WORD_SUB_REFL; VAL_WORD_0; IVAL_WORD_0]) THEN
   RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
   RULE_ASSUM_TAC(CONV_RULE(TRY_CONV INT_REDUCE_CONV)) THEN
   RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_EQ_CONV))) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[NOT_CLAUSES; COND_CLAUSES]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[])) (asl,w);;

(* ---- extract (current-state index, PC offset) from the goal's PC assumption.
   off: >=0 concrete pc+off (or bare word off); -2 symbolic if-term (needs resolve);
        -3 no PC assumption found. ---- *)
let pc_info (asl,_) =
  try
    let (_,th) = List.find (fun (_,th) -> match concl th with
        | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),_)),_) -> true
        | _ -> false) asl in
    let lhs,rhs = dest_eq (concl th) in
    let st = rand lhs in
    let sidx = (let nm = fst(dest_var st) in
                int_of_string (String.sub nm 1 (String.length nm - 1))) in
    let off = (match rhs with
      | Comb(Const("word",_),Comb(Comb(Const("+",_),_),n)) -> (try dest_small_numeral n with _ -> -2)
      | Comb(Const("word",_),n) -> (try dest_small_numeral n with _ -> -2)
      | _ -> -2) in
    (sidx, off)
  with _ -> (-1, -3);;

(* ---- DRIVE_TAC target maxsteps ----
   Steps ARM instrs one at a time from the current state; when the PC becomes a
   symbolic if-term, applies WB_TAIL_RESOLVE_TAC to make it concrete, then steps;
   stops when PC = word (pc + target).

   This is GEN_PROVE_SAFETY_SPEC_TAC's own driver loop (in common/consttime.ml:
   find the `read PC` assumption, compare its RHS to the destination, else take one
   more step) with one addition, which is why the stock tactic cannot be called here:
   the nblk dispatch leaves the PC a symbolic if-term part-way through a leg, and the
   stock loop has no resolver for that -- it only ever compares for equality, so it
   would stop, having neither reached the destination nor made progress.  Resolving
   such a PC by hand is what BIGNUM_EMONTREDC_8N_CORRECT does in the corpus
   (UNDISCH the if-term PC, rewrite it concrete, DISCH, keep stepping).  Here that
   would have to be repeated at every dispatch point of all 24 driven legs -- the
   sixteen concrete nblk bands and the eight tail residues -- so the resolve step is
   folded into the loop instead of being written out per band. ---- *)
let rec DRIVE_TAC target maxsteps : tactic = fun (asl,w) ->
  if maxsteps <= 0 then failwith "DRIVE_TAC: maxsteps exhausted" else
  let (sidx, off) = pc_info (asl,w) in
  if off = target then ALL_TAC (asl,w)
  else if off = -3 then failwith "DRIVE_TAC: no PC assumption"
  else if off = -2 then
    (WB_TAIL_RESOLVE_TAC THEN
     (fun g ->
        let (sidx2, off2) = pc_info g in
        if off2 = target then ALL_TAC g
        else if off2 = -2 then failwith "DRIVE_TAC: resolver left PC symbolic"
        else (ARM_QSTEP_TAC EXEC ("s"^string_of_int (sidx2+1)) THEN
              DRIVE_TAC target (maxsteps-1)) g)) (asl,w)
  else
    (ARM_QSTEP_TAC EXEC ("s"^string_of_int (sidx+1)) THEN
     DRIVE_TAC target (maxsteps-1)) (asl,w);;

(* ---- concrete-band prep: unfold list wrappers, keep nonoverlapping FOLDED,
   split the conjunctive nonoverlapping asms, init state s0 ---- *)
let BAND_PREP_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; ALLPAIRS; PAIRWISE; MAP; WB_MC_LEN]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  ENSURES_INIT_TAC "s0";;

(* ---- UNIFORM concrete-band closer: prep, then DRIVE from s0 to pc+4560, finalize.
   Works for ANY concrete nblk (1..16): every branch condition is concrete arithmetic
   the resolver reduces directly, so no band-specific step count or front prefix.
   The symbolic NBLK_ARITH lemmas are only needed for the symbolic >=17 leg. ---- *)
let concrete_band_close_tac =
  BAND_PREP_TAC THEN
  DRIVE_TAC 4560 700 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ---- n-way concrete split of a bounded nblk leg (lo..hi), then close each band ---- *)
let split_close_tac lo hi =
  let disj = end_itlist (fun a b -> mk_disj(a,b))
     (map (fun k -> mk_eq(`nblk:num`, mk_small_numeral k)) (lo--hi)) in
  SUBGOAL_THEN disj MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  concrete_band_close_tac;;

(* ---- reusable safety back-legs, starting at the compare just before the
   correctness proof's q_at seam.  At pc+0xee8 X5 is the public residual byte
   count; the theorem executes the compare and the initial ciphertext/H^8 loads
   itself, so its interface does not need to carry condition-code assumptions.
   From here the trace depends only on the public addresses and the fixed
   residual block count; all SIMD/data values may remain unconstrained.

   Prove each residual tail ONCE against the caller's whole-buffer bounds.  The
   selected witnesses below are closed choice terms, so all three consumers
   (5..8, 9..16, and >=17) can reuse them without existential-witness escape. ---- *)
let WB_SAFETY_BYTES_LEN = prove
 (`!nblk.
      128 * nblk < 2 EXP 64
      ==> val (word (128 * nblk):int64) DIV 8 * 1 = 16 * nblk`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  MP_TAC(SPECL [`8`; `16 * nblk`] DIV_MULT) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* The val-free twin of the above, needed on the >=17 leg only.
   WB_SAFETY_BYTES_LEN matches `val (word (128*nblk)) DIV 8 * 1`, but by the time
   the >=17 residue reaches its events discharge the goal's bound is already spelled
   `(128 * nblk) DIV 8 * 1`: CORE_SAFE_OPEN_TAC asserts `val (word (128*nblk)) =
   128*nblk` into the assumptions, and WB_TAIL_POST_ASM_REWRITE_TAC (which rewrites
   with every `val`-headed assumption) consumes the `val (word ...)` wrapper on the
   goal side.  The assumption side, stripped straight off the reusable tail theorem,
   keeps the val spelling.  So WB_SAFETY_BYTES_LEN cannot fire on the goal, and
   the two sides end up as `(128*nblk) DIV 8 * 1` and `16*nblk`.
   This rule closes that gap.  It needs no size side-condition: with the word
   wrapper already gone it is pure natural-number arithmetic, which is also why it is
   safe to keep unconditionally in the rewrite set.  The 9..16 bands never need it
   (nblk is a numeral there, so NUM_REDUCE collapses the bound outright). *)
let WB_SAFETY_BYTES_LEN_NOVAL = prove
 (`!nblk. (128 * nblk) DIV 8 * 1 = 16 * nblk`,
  GEN_TAC THEN
  MP_TAC(SPECL [`8`; `16 * nblk`] DIV_MULT) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* memaccess_inbounds distributes over a loop trace: if every iteration's own
   trace is in bounds, so is the concatenation ENUMERATEL builds.  Needed on the
   >=17 leg only, whose scaffold keeps the loop body symbolic in `i` -- the
   bands 1..16 unroll to concrete traces and never produce an ENUMERATEL goal.
   Stock consttime.ml has MEMACCESS_INBOUNDS_APPEND/_CONS/_MEM but no ENUMERATEL
   rule, so a quantified loop trace matches none of its dispatch cases. *)
let MEMACCESS_INBOUNDS_ENUMERATEL = prove
 (`!n (f:num->((N)address_uarch_event)list) rr ww.
     (!i. i < n ==> memaccess_inbounds (f i) rr ww)
     ==> memaccess_inbounds (ENUMERATEL n f) rr ww`,
  INDUCT_TAC THEN REWRITE_TAC[ENUMERATEL] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[memaccess_inbounds_def; ALL];
    REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LT] THEN
      DISCH_THEN MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let WB_CONTAINED_REFL = prove
 (`!(x:N word) n. contained (x,n) (x,n)`,
  REWRITE_TAC[CONTAINED] THEN MESON_TAC[]);;

let rec WB_FIRST_CONTAINED_DISJ_TAC : tactic = fun (asl,w) ->
  if is_disj w then
    try (DISJ1_TAC THEN CONTAINED_TAC) (asl,w)
    with Failure _ ->
      (DISJ2_TAC THEN WB_FIRST_CONTAINED_DISJ_TAC) (asl,w)
  else CONTAINED_TAC (asl,w);;

let WB_FIRST_NONOVERLAPPING_TAC : tactic = fun (asl,w) ->
  try FIRST_ASSUM ACCEPT_TAC (asl,w)
  with Failure _ ->
    (ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
     FIRST_ASSUM ACCEPT_TAC) (asl,w);;

let mk_tail_safe_goal r =
  subst [mk_small_numeral r,`rr:num`]
   `exists f_events.
      forall e pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk
             tail_in tail_out.
        1 <= nblk /\
        128 * nblk < 2 EXP 64 /\
        contained (tail_in,16 * rr) (in_p,16 * nblk) /\
        contained (tail_out,16 * rr) (out_p,16 * nblk) /\
        nonoverlapping
          (word pc,LENGTH aesv8_gcm_8x_dec_256_wb_mc) (stackpointer,80) /\
        ALLPAIRS nonoverlapping
          [out_p,16 * nblk; xi_p,16; ivec_p,16]
          [word pc,LENGTH aesv8_gcm_8x_dec_256_wb_mc]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
                  read PC s = word (pc + 0xee8) /\
                  read X0 s = tail_in /\
                  read X2 s = tail_out /\
                  read X3 s = xi_p /\
                  read X5 s = word (16 * rr) /\
                  read X6 s = htbl_p /\
                  read X10 s = word_add stackpointer (word 64) /\
                  read X16 s = ivec_p /\
                  read events s = e)
             (\s. read PC s = word (pc + 4560) /\
                  (exists e2.
                       read events s = APPEND e2 e /\
                       e2 =
                       f_events in_p key_p htbl_p out_p xi_p ivec_p nblk
                                tail_in tail_out pc stackpointer /\
                       memaccess_inbounds e2
                       [in_p,16 * nblk; xi_p,16; ivec_p,16;
                        key_p,240; htbl_p,192; out_p,16 * nblk;
                        stackpointer,80]
                       [out_p,16 * nblk; xi_p,16; ivec_p,16;
                        stackpointer,80]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
              [memory :> bytes (tail_out,16 * rr); memory :> bytes (xi_p,16);
               memory :> bytes (ivec_p,16);
               memory :> bytes (word_add stackpointer (word 64),16)] ,,
              MAYCHANGE
              [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13;
               Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25;
               Q26; Q27; Q28; Q29; Q30; Q31])`;;

let prove_tail_safe r =
  let tail_len = mk_binary "*" (`16`,mk_small_numeral r) in
  let tail_code_nonoverlap =
    subst [tail_len,`tail_len:num`]
      `nonoverlapping (word pc,5960) (tail_out:int64,tail_len)` in
  let tail_reads =
    subst [tail_len,`tail_len:num`]
      `[(tail_in:int64),tail_len; xi_p,16; ivec_p,16; key_p,240; htbl_p,192;
        tail_out,tail_len; stackpointer,80]` in
  let tail_writes =
    subst [tail_len,`tail_len:num`]
      `[(tail_out:int64),tail_len; xi_p,16; ivec_p,16; stackpointer,80]` in
  prove(mk_tail_safe_goal r,
    META_EXISTS_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
                MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL; ALLPAIRS; WB_MC_LEN]) THEN
    REPEAT(FIRST_X_ASSUM
      (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    SUBGOAL_THEN
      `nonoverlapping (word pc,5960) (out_p:int64,16 * nblk)`
      ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `nonoverlapping (word pc,5960) (xi_p:int64,16)`
      ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `nonoverlapping (word pc,5960) (ivec_p:int64,16)`
      ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN tail_code_nonoverlap ASSUME_TAC THENL
     [MATCH_MP_TAC NONOVERLAPPING_SUBREGIONS THEN
      MAP_EVERY EXISTS_TAC
       [`word pc:int64`; `5960`; `out_p:int64`; `16 * nblk`] THEN
      ASM_REWRITE_TAC[WB_CONTAINED_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `val (word (128 * nblk):int64) DIV 8 * 1 = 16 * nblk`
      SUBST_ALL_TAC THENL
     [MATCH_MP_TAC WB_SAFETY_BYTES_LEN THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    DRIVE_TAC 4560 400 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
    W (fun (asl,w) ->
      (if is_conj w then
         CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
       else ALL_TAC) THEN
      W (fun (asl,w) ->
        let _,[evs; target_reads; target_writes] = strip_comb w in
        MATCH_MP_TAC
          (REWRITE_RULE[IMP_IMP]
            (ISPECL [evs; tail_reads; target_reads;
                     tail_writes; target_writes]
              MEMACCESS_INBOUNDS_CONTAINED))) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[ALL; EX; MEM] THEN
        ASM_REWRITE_TAC[WB_CONTAINED_REFL];
        (!memaccess_inbounds_normalize_tac) THEN
        REWRITE_TAC[MESON[APPEND] `APPEND ([]:(A)list) [] = []`] THEN
        REWRITE_TAC[memaccess_inbounds; memaccess_inbounds_def; ALL; EX] THEN
        REWRITE_TAC[contained] THEN
        REPEAT CONJ_TAC THEN WB_FIRST_CONTAINED_DISJ_TAC]));;

let WB_TAIL_SAFE_1_EXISTS = prove_tail_safe 1;;
let WB_TAIL_SAFE_2_EXISTS = prove_tail_safe 2;;
let WB_TAIL_SAFE_3_EXISTS = prove_tail_safe 3;;
let WB_TAIL_SAFE_4_EXISTS = prove_tail_safe 4;;
let WB_TAIL_SAFE_5_EXISTS = prove_tail_safe 5;;
let WB_TAIL_SAFE_6_EXISTS = prove_tail_safe 6;;
let WB_TAIL_SAFE_7_EXISTS = prove_tail_safe 7;;
let WB_TAIL_SAFE_8_EXISTS = prove_tail_safe 8;;

let wbn_tail_safeties =
  map SELECT_RULE
   [WB_TAIL_SAFE_1_EXISTS; WB_TAIL_SAFE_2_EXISTS;
    WB_TAIL_SAFE_3_EXISTS; WB_TAIL_SAFE_4_EXISTS;
    WB_TAIL_SAFE_5_EXISTS; WB_TAIL_SAFE_6_EXISTS;
    WB_TAIL_SAFE_7_EXISTS; WB_TAIL_SAFE_8_EXISTS];;

(* Specialize a selected tail theorem to the current accumulated event trace,
   using the state equation's RHS so the old state variable does not survive
   ARM_BIGSTEP_TAC's cleanup. *)
let MP_WB_TAIL_SAFE_TAC r sname args : tactic = fun (asl,w) ->
  let st = mk_var(sname,`:armstate`) in
  let evth = snd(List.find (fun (_,th) ->
    let c = concl th in
    is_eq c &&
    (try rator(lhs c) = `read events` && rand(lhs c) = st with _ -> false)) asl) in
  MP_TAC(SPECL (rhs(concl evth) :: args) (el (r-1) wbn_tail_safeties)) (asl,w);;

(* These back-legs already finish at the enclosing safety theorem's final PC.
   Consume their ensures theorem directly instead of passing it through
   ARM_BIGSTEP_TAC: the latter needlessly rebuilds the whole state update and
   can fail while absorbing the nested MAYCHANGE relation. *)
let FINAL_TAIL_ENSURES = prove
 (`!step (P:S->bool) Q C Q' C' s.
      P s /\
      ensures step P Q C /\
      C subsumed C' /\
      (!s'. Q s' ==> Q' s')
      ==> eventually step (\s'. Q' s' /\ C' s s') s`,
  REWRITE_TAC[ensures; subsumed] THEN
  MESON_TAC[EVENTUALLY_MONO]);;

(* When the tail starts after a simulated prefix, compose its frame with the
   enclosing frame from the original state instead of rebasing that frame at
   the tail state.

   COMPOSE_FRAME_LEMMA is split out so MESON only ever sees the frame
   composition.  Handing it the whole composed statement instead diverges: the
   `seq` existential multiplies with `eventually`'s own quantifier. *)
let COMPOSE_FRAME_LEMMA = prove
 (`(C' ,, C) subsumed C' ==> C' s0 s /\ C s s' ==> C' s0 s'`,
  REWRITE_TAC[subsumed; seq] THEN MESON_TAC[]);;

let FINAL_COMPOSED_TAIL_ENSURES = prove
 (`!step (P:S->bool) Q C Q' C' s0 s.
      C' s0 s /\
      P s /\
      ensures step P Q C /\
      (C' ,, C) subsumed C' /\
      (!s'. Q s' ==> Q' s')
      ==> eventually step (\s'. Q' s' /\ C' s0 s') s`,
  REWRITE_TAC[ensures] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME `(P:S->bool) s`))) THEN
  MATCH_MP_TAC(REWRITE_RULE[GSYM RIGHT_FORALL_IMP_THM] EVENTUALLY_MONO) THEN
  BETA_TAC THEN X_GEN_TAC `t:S` THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP COMPOSE_FRAME_LEMMA o
                  check (fun th -> is_binary "subsumed" (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

let USE_WB_TAIL_SAFE_TAC post_tac : tactic =
  DISCH_THEN(fun tailth ->
    let _,args = strip_comb(concl tailth) in
    let tail_pre = el 1 args
    and tail_post = el 2 args
    and tail_frame = el 3 args in
    MATCH_MP_TAC FINAL_TAIL_ENSURES THEN
    MAP_EVERY EXISTS_TAC [tail_pre; tail_post; tail_frame] THEN
    REPEAT CONJ_TAC THENL
     [BETA_TAC THEN ASM_REWRITE_TAC[];
      ACCEPT_TAC tailth;
      REWRITE_TAC[ETA_AX; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                  MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS;
                  MODIFIABLE_UPPER_SIMD_REGS] THEN
      SUBSUMED_MAYCHANGE_TAC;
      post_tac]);;

let USE_WB_COMPOSED_TAIL_SAFE_TAC post_tac : tactic =
  DISCH_THEN(fun tailth ->
    let _,args = strip_comb(concl tailth) in
    let tail_pre = el 1 args
    and tail_post = el 2 args
    and tail_frame = el 3 args in
    MATCH_MP_TAC FINAL_COMPOSED_TAIL_ENSURES THEN
    MAP_EVERY EXISTS_TAC [tail_pre; tail_post; tail_frame] THEN
    REPEAT CONJ_TAC THENL
     [MONOTONE_MAYCHANGE_TAC;
      (* On legs whose tail is entered after a long symbolic front, the front
         leaves the leftover-byte count in X5 as the unreduced difference
         `word_sub (in_p + 16*nblk) (in_p + 128*k)`, so the blanket rewrite
         closes 9 of the 10 precondition conjuncts and leaves one word
         equation.  WORD_RULE finishes it.  The 5..8 legs enter the tail at s0,
         where every conjunct is literally an assumption and nothing is left --
         hence TRY, which keeps the step available without being load-bearing. *)
      BETA_TAC THEN ASM_REWRITE_TAC[] THEN TRY(CONV_TAC WORD_RULE);
      ACCEPT_TAC tailth;
      REWRITE_TAC[ETA_AX; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                  MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS;
                  MODIFIABLE_UPPER_SIMD_REGS] THEN
      SUBSUMED_MAYCHANGE_TAC;
      post_tac]);;

(* Targeted stand-in for the blanket ASM_REWRITE_TAC[] at the head of a composed
   tail's post-tactic.  A blanket call there stack-overflows on the 9..16 and >=17
   legs: unlike the 5..8 legs, whose tail starts at s0, these reach the tail after a
   long symbolic front, so the assumption list additionally carries that front's
   per-state reads plus front_916_setup_tac's asserted USHR / AND-mask / DIVISION
   identities, and the resulting rewrite net cycles.  ASM_SIMP_TAC is no better: same
   assumption set, same net.  Two measures are needed, since narrowing the assumption
   set alone still overflows:

   (a) Filter.  The postcondition here mentions only the freshly generalized final
   state and the event list, so only three kinds of assumption can contribute:
   variable definitions (the stripped `e2 = f_events ...`), reads of a state the goal
   still mentions, and the `val (word ...)` size facts the enclosing spec's buffer
   bounds are phrased over.  The rest are dropped rather than discharged.

   (b) Bounded traversal, which is what actually breaks the loop.  A rewrite *net*
   diverges on a cyclic equation pair, where a single ONCE_DEPTH pass terminates.
   Each pass below is one ONCE_DEPTH traversal, so it rewrites every redex at most
   once and cannot cycle; passes repeat only while the goal keeps changing, and at
   most 12 times.  The trailing REWRITE_TAC[] closes the trivial conjuncts a blanket
   call would. *)
let WB_TAIL_POST_ASM_REWRITE_TAC : tactic = fun (asl,w) ->
  let gvars = frees w in
  let usable th =
    let c = concl th in
    is_eq c &&
    (let l = lhs c in
     is_var l ||
     (match strip_comb l with
      | Const("read",_), [_; st] -> mem st gvars
      | Const("val",_), _ -> true
      | _ -> false)) in
  let ths = map snd (filter (usable o snd) asl) in
  let conv = GEN_REWRITE_CONV ONCE_DEPTH_CONV ths in
  let rec go k tm =
    if k <= 0 then REFL tm else
    let th = try conv tm with Failure _ -> REFL tm in
    let tm' = rhs(concl th) in
    if tm' = tm then th else TRANS th (go (k-1) tm') in
  (CONV_TAC (go 12) THEN REWRITE_TAC[]) (asl,w);;

(* After MEMACCESS_INBOUNDS_APPEND splits the trace, the first conjunct is the
   reusable tail theorem's own `memaccess_inbounds` postcondition, which is already
   an assumption -- so it needs matching, not search.  A blanket ASM_MESON_TAC[] is
   handed all 64 assumptions instead and diverges on the 9..16 and >=17 legs.  Trying
   the two assumption-matching tactics first closes that case immediately and never
   reaches MESON.

   The fallback must be the *unrestricted* ASM_MESON_TAC[].  Restricted to the
   inbounds assumptions it fails on band 5 with `solve_goal: Too deep`: the 5..8 legs
   reach this conjunct in a shape that genuinely needs facts beyond the inbounds
   ones.

   Plain matching is still not enough on the 9..16 and >=17 legs, because the two
   sides spell the same buffer bound differently.  mk_tail_safe_goal states the tail's
   postcondition over `val (word (128 * nblk):int64) DIV 8 * 1`, and prove_tail_safe
   SUBST_ALL_TACs that to `16 * nblk` only *inside* its own proof, so the exported
   theorem keeps the `val` spelling.  The enclosing band closers then run
   `RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV)` and `CONV_TAC NUM_REDUCE_CONV` over a
   leg where nblk is already a numeral, which collapses one side to a literal (`144`
   at band 9) while the other keeps the `val (word ...) DIV 8 * 1` form.  The 5..8
   legs never diverge this way because they specialize the tail at s0 with no
   intervening reduction.  So normalize both sides to the same spelling and try the
   match again; equality-shaped goals and the legs the plain matches close are
   untouched, because the plain matches are tried first.

   The decisive normalizer is APPEND_NIL.  Both sides carry the tail's selector
   `(@f_events. ...) in_p key_p ... stackpointer` -- the goal's copy inside a
   `memaccess_inbounds` argument, the assumption's as the `e2 = ...` definition.  But
   RESHAPE_LOOP_TAC leaves the goal's copy with `APPEND (APPEND [...] []) []`
   wrappers around the range lists *inside the epsilon's body*, where the
   assumption's copy has the bare lists.  Two epsilon terms whose bodies differ at
   all are different terms, so `e2` never rewrites and the conjunct cannot match
   however the bounds are spelled.  APPEND_NIL collapses the wrappers and the two
   selectors become alpha-equal.

   WB_SAFETY_BYTES_LEN and the `val` size facts additionally reconcile the buffer
   bounds, spelled `val (word 1152) DIV 8 * 1` in the
   assumption against the literal `144` in the goal.  WB_SAFETY_BYTES_LEN is the rule
   prove_tail_safe itself uses for this bound; it matters on the >=17 leg, where nblk
   stays symbolic and the `val` facts alone would leave `(128 * nblk) DIV 8 * 1`
   needing symbolic arithmetic that neither NUM_REDUCE nor MESON closes. *)
let WB_TAIL_EVENTS_DISCHARGE_TAC : tactic = fun (asl,w) ->
  let bytelen =
    mapfilter (fun (_,th) -> MATCH_MP WB_SAFETY_BYTES_LEN th) asl in
  let valfacts = map snd (filter (fun (_,th) ->
      let c = concl th in
      is_eq c &&
      (match strip_comb(lhs c) with
       | Const("val",_),_ -> true
       (* the stripped `e2 = f_events ...` definition.  Without it the assumption
          keeps the bare variable `e2` where the goal has the selector it stands for,
          so the two can never converge no matter how the rest is normalized. *)
       | _ -> is_var(lhs c))) asl) in
  (* WB_SAFETY_BYTES_LEN_NOVAL is unconditional, so it is prepended rather than
     derived from an assumption: on the >=17 leg the goal's bound has already lost its
     `val (word ...)` wrapper, so WB_SAFETY_BYTES_LEN cannot reach it.  See that
     lemma's own comment. *)
  let rules = WB_SAFETY_BYTES_LEN_NOVAL :: bytelen @ valfacts in
  (* APPEND_NIL gets TOP_DEPTH, because the wrappers are nested two deep
     (`APPEND (APPEND l []) []`) and a single ONCE_DEPTH pass strips only the outer
     one, leaving the two epsilon terms still unequal.  It is a terminating
     orientation (the RHS is a strict subterm), so a full traversal cannot cycle.

     The assumption-derived rules must NOT get TOP_DEPTH: it stack-overflows
     ("looping recursion?") on exactly the cyclic-pair hazard documented on
     WB_TAIL_POST_ASM_REWRITE_TAC above.  But a single ONCE_DEPTH pass
     is also not enough -- the bounds needing rewriting sit *inside* the epsilon's
     body, below the first redex the pass consumes, so goal and assumption normalize
     to shapes that still differ there.  Use the same bounded-repetition shape as
     that helper: each pass is one ONCE_DEPTH traversal, so it cannot cycle, and
     passes repeat only while the term keeps changing. *)
  let bounded_rewr ths k tm =
    let conv = GEN_REWRITE_CONV ONCE_DEPTH_CONV ths in
    let rec go k tm =
      if k <= 0 then REFL tm else
      let th = try conv tm with Failure _ -> REFL tm in
      let tm' = rhs(concl th) in
      if tm' = tm then th else TRANS th (go (k-1) tm') in
    go k tm in
  (* APPEND_NIL must run BOTH before and after the assumption-rule expansion.
     On the goal side the wrappers are present from the start, so the leading pass
     strips them.  On the assumption side they are not: there the trace is still the
     bare variable `e2`, and the wrappers only materialize once the `e2 = <selector>`
     definition has been rewritten in -- i.e. only after the leading pass has
     already run.  With the leading pass alone the two sides would therefore
     normalize to epsilon terms whose bodies differ by exactly
     `APPEND (APPEND [...] []) []`, and since epsilon terms with any difference in
     their bodies are different terms, the match could not fire however the bounds
     were spelled, and the goal would fall through to the diverging ASM_MESON_TAC[].
     With the trailing pass both sides become alpha-equal.  On the 5..8 and 9..16
     legs nblk is a numeral, so their bounds have already converged and the
     trailing pass leaves the stripped term unchanged.  Repeating the pass is safe
     for the reason the leading one is: APPEND_NIL's RHS is a strict subterm, so a
     full traversal terminates. *)
  let append_nil_pass = TRY_CONV(GEN_REWRITE_CONV TOP_DEPTH_CONV [APPEND_NIL]) in
  let nconv =
    append_nil_pass THENC
    (if rules = [] then ALL_CONV else bounded_rewr rules 12) THENC
    append_nil_pass THENC
    TRY_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV) in
  let match_with f =
    FIRST_ASSUM (fun th -> ACCEPT_TAC(f th)) ORELSE
    FIRST_ASSUM (fun th -> MATCH_ACCEPT_TAC(f th)) in
  (match_with I ORELSE
   match_with (CONV_RULE nconv) ORELSE
   (CONV_TAC nconv THEN (match_with I ORELSE match_with (CONV_RULE nconv))) ORELSE
   ASM_MESON_TAC[]) (asl,w);;

(* Local, net-safe shadow of the stock DISCHARGE_MEMACCESS_INBOUNDS_TAC
   (common/consttime.ml), for the second conjunct below.

   The stock tactic stack-overflows with "looping recursion?" on the 9..16 and
   >=17 legs, which reach this conjunct with 63 assumptions.  Its one blanket
   call is the ASM_REWRITE_TAC[] inside
   DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC, whose stated
   job is just to expand the stripped `e2 = f_events ...` definition so the
   undischarged assumption and the goal take the same shape.  It is the same
   failure mode WB_TAIL_POST_ASM_REWRITE_TAC and WB_TAIL_EVENTS_DISCHARGE_TAC above
   are written around: a REWRITE_TAC builds a rewrite *net* and re-descends, so a
   cyclic equation pair among the assumptions diverges.  The remedy is likewise the
   same -- bound the TRAVERSAL rather than narrow the fact set, which is not
   sufficient on its own.  The overflow needs the cycle to be reachable from the
   goal.

   On the shapes the stock tactic does close -- identical-term match, range
   widening, concrete goal, and APPEND-split with and without `e2` defined -- the
   shadow agrees with it exactly, so the already-passing 5..8 legs keep their path.

   Everything here is the stock tactic transcribed verbatim apart from that one
   call and a recursion cap on main_tac, which turns a non-shrinking trace into a
   Failure the enclosing ORELSE can act on instead of an exhausted OCaml stack.

   Two bounds matter in the traversal.  Each pass
   is a single ONCE_DEPTH traversal, so it rewrites every redex at most once and
   cannot cycle; passes repeat, because the shapes needing normalization sit below
   the first redex, inside the tail selector's epsilon body.  And repetition stops
   when a term *repeats*, not merely when it stops changing: an oscillating
   equation pair flips the term's parity on every pass, so a stabilization test
   alone never fires and the conjunct is left unprovable. *)
let WB_BOUNDED_ASM_REWRITE_TAC (extra:thm list) : tactic = fun (asl,w) ->
  let gvars = frees w in
  let usable th =
    let c = concl th in
    is_eq c &&
    (let l = lhs c in
     is_var l ||
     (match strip_comb l with
      | Const("read",_), [_; st] -> mem st gvars
      | Const("val",_), _ -> true
      | _ -> false)) in
  let rules = extra @ map snd (filter (usable o snd) asl) in
  let conv = GEN_REWRITE_CONV ONCE_DEPTH_CONV rules in
  let rec go seen k tm =
    if k <= 0 then REFL tm else
    let th = try conv tm with Failure _ -> REFL tm in
    let tm' = rhs(concl th) in
    if tm' = tm || exists (fun t -> t = tm') seen then REFL tm
    else TRANS th (go (tm::seen) (k-1) tm') in
  (CONV_TAC (go [] 12) THEN REWRITE_TAC extra) (asl,w);;

let WB_DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC:tactic =
  let try_discharge (meminb_th:thm):tactic =
    UNDISCH_TAC (concl meminb_th) THEN
    WB_BOUNDED_ASM_REWRITE_TAC [] THEN
    REWRITE_TAC[APPEND;APPEND_NIL] THEN
    ((MATCH_MP_TAC MEMACCESS_INBOUNDS_MEM THEN
      REWRITE_TAC[ALL;MEM] THEN NO_TAC) ORELSE
     (MATCH_MP_TAC MEMACCESS_INBOUNDS_CONTAINED THEN
      DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC)) in
  W (fun (asl,w) ->
    let meminbounds = map snd (filter (fun (_,th) ->
          let cth = concl th in
          is_comb cth &&
          name_of (fst (strip_comb cth)) = "memaccess_inbounds") asl) in
    if meminbounds = [] then
      failwith "No memaccess_inbounds assumption" else
    end_itlist (fun tac1 tac2 -> tac1 ORELSE tac2)
      (map try_discharge meminbounds));;

let WB_DISCHARGE_MEMACCESS_INBOUNDS_TAC =
  let append_nil_th =
      MESON[APPEND]
        `memaccess_inbounds (APPEND [] b) = memaccess_inbounds b /\
         memaccess_inbounds (APPEND (APPEND [] []) b) = memaccess_inbounds b` in
  let rec main_tac d (asl,w) =
    if d <= 0 then failwith "WB_DISCHARGE_MEMACCESS_INBOUNDS_TAC: depth" else
    ((WB_DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC) ORELSE

    (DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC) ORELSE

    (REWRITE_TAC[CONJUNCT2 APPEND] THEN
      CONV_TAC ((RATOR_CONV o RATOR_CONV o RAND_CONV) CONS_TO_APPEND_CONV) THEN
      GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
      CONJ_TAC THENL [
        DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC;
        REWRITE_TAC[append_nil_th] THEN main_tac (d-1) THEN NO_TAC
      ]) ORELSE

    (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
      CONJ_TAC THENL [
        main_tac (d-1) THEN NO_TAC;
        DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC;
      ]) ORELSE

    (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
      CONJ_TAC THENL [
        WB_DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC;
        main_tac (d-1);
      ] THEN NO_TAC)) (asl,w)
  in
  (* Two dispatch cases main_tac does not have, both reached only by the >=17
     leg and no-ops on every shape the 5..8 and 9..16 legs present.

     (1) REPEAT CONJ_TAC.  main_tac dispatches on `memaccess_inbounds` heads and
     on MEMACCESS_INBOUNDS_APPEND, so a top-level `/\` matches nothing at all and
     the whole tactic reports "could not identify the pattern".  The >=17 leg
     gets one because its scaffold entry is APPEND residue (APPEND (ENUMERATEL
     ..) front): DISCHARGE_WB_COMPOSED_TAIL_TAC's REWRITE_TAC
     [MEMACCESS_INBOUNDS_APPEND] then distributes all the way down and hands this
     call a five-way conjunction.  Bands 9..16 enter the scaffold at a bare
     f_ev_k with no APPEND, so their goal stays a single mi term and REPEAT
     CONJ_TAC is a no-op there.

     (2) the ENUMERATEL rule.  Of those five conjuncts four are concrete traces
     that main_tac already closes; the fifth is the symbolic loop trace, and it
     needs the quantified-i step before the per-iteration body -- which main_tac
     then closes by its ordinary assumption route, since the body's stores are
     already covered by the tail theorem's own inbounds assumption. *)
  let close_one =
    main_tac 8 ORELSE
    (MATCH_MP_TAC MEMACCESS_INBOUNDS_ENUMERATEL THEN
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN main_tac 8) ORELSE
    FAIL_TAC
      "WB_DISCHARGE_MEMACCESS_INBOUNDS_TAC could not identify the pattern" in
  REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL] THEN
  REPEAT CONJ_TAC THEN close_one;;

let DISCHARGE_WB_COMPOSED_TAIL_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W (fun (asl,w) ->
    (if is_conj w then
       CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
     else ALL_TAC) THEN
    REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
    CONJ_TAC THENL
     [WB_TAIL_EVENTS_DISCHARGE_TAC;
      WB_DISCHARGE_MEMACCESS_INBOUNDS_TAC]);;


(* ---- the nblk 9..16 leg: symbolic front, then concretize per band.  A
   concrete-band DRIVE from s0 does NOT work here: the front branch at 0x44c is a
   flag compare rather than an affine word_sub, so the resolver cannot make its PC
   concrete.  Hence the front runs symbolically off WB_LOOPENTER_FLAGS_GE9 and each
   band is concretized only afterwards. ---- *)

let front_916_setup_tac =
  SUBGOAL_THEN `9 <= nblk` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)` ASSUME_TAC THENL
   [MATCH_MP_TAC USHR_128NBLK_ANY THEN NBLK_ARITH_GE9_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_sub (word (16 * nblk)) (word 1)) (word 18446744073709551488):int64
       = word (128 * ((nblk - 1) DIV 8))` ASSUME_TAC THENL
   [MATCH_MP_TAC AND_MASK_16NBLK_ANY THEN NBLK_ARITH_GE9_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; ALLPAIRS; PAIRWISE; MAP; WB_MC_LEN]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPEC `nblk:num` GUARD_LE_FALLTHRU) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [NBLK_ARITH_GE9_TAC;
      MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN NBLK_ARITH_GE9_TAC]; DISCH_TAC] THEN
  MP_TAC(SPECL [`in_p:int64`; `nblk:num`] WB_LOOPENTER_FLAGS_GE9) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [NBLK_ARITH_GE9_TAC;
      MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN NBLK_ARITH_GE9_TAC]; DISCH_TAC];;

(* front sim 1--295 -> pc+1212 (0x4bc); resolve 0x49c; step 296 -> pc+2576 (0xa10) *)
let front_916_sim_tac =
  ARM_QSTEPS_TAC EXEC (1--295) THEN
  SUBGOAL_THEN `(nblk - 1) DIV 8 = 1` ASSUME_TAC THENL
   [MP_TAC(ASSUME `9 <= nblk`) THEN MP_TAC(ASSUME `nblk <= 16`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(nblk - 1) DIV 8 = 1`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  MP_TAC(SPECL [`in_p:int64`; `128`; `128`] WB_PTRCMP_FLAGS) THEN ANTS_TAC THENL
   [CONJ_TAC THEN MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
    MP_TAC(ASSUME `9 <= nblk`) THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(128 < 128) <=> F`]) THEN
  ARM_QSTEPS_TAC EXEC (296--296);;

(* ---- the nblk>=17 leg.  Its trace is already in ENSURES_EVENTS_WHILE_UP2 shape:
     e2 = APPEND <residue ladder> (APPEND (ENUMERATEL ((nblk-9) DIV 8) f_ev_loop)
                                          f_ev_front)
   so the residue ladder lands in the rule's discarded e_back.  The scaffold below
   gives the ladder its eight residue metavars, one per (nblk-9) MOD 8 value, since
   HOL metavars are shared across the goalstack and a single shared one would be
   fixed by whichever residue closed first. ---- *)

let core_scaffold =
 `\(in_p:int64) (key_p:int64) (htbl_p:int64) (out_p:int64) (xi_p:int64)
   (ivec_p:int64) (nblk:num) (pc:num) (stackpointer:int64).
     if nblk = 1 then f_ev_1 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 2 then f_ev_2 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 3 then f_ev_3 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 4 then f_ev_4 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk <= 8 then
       APPEND
         ((if nblk = 5 then f_ev_5
           else if nblk = 6 then f_ev_6
           else if nblk = 7 then f_ev_7
           else f_ev_8) in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer)
         (f_ev_58_front in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer)
     else if nblk = 9 then f_ev_9 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 10 then f_ev_10 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 11 then f_ev_11 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 12 then f_ev_12 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 13 then f_ev_13 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 14 then f_ev_14 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 15 then f_ev_15 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 16 then f_ev_16 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else
       APPEND
         ((if (nblk - 9) MOD 8 = 0 then f_ev_t0
           else if (nblk - 9) MOD 8 = 1 then f_ev_t1
           else if (nblk - 9) MOD 8 = 2 then f_ev_t2
           else if (nblk - 9) MOD 8 = 3 then f_ev_t3
           else if (nblk - 9) MOD 8 = 4 then f_ev_t4
           else if (nblk - 9) MOD 8 = 5 then f_ev_t5
           else if (nblk - 9) MOD 8 = 6 then f_ev_t6
           else f_ev_t7) in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer)
         (APPEND
           (ENUMERATEL ((nblk - 9) DIV 8)
             (\i. f_ev_loop in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer i))
           (f_ev_front in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer))
     :(uarch_event)list`;;

(* ---- >=17 entry prep: establish the bounds and collapse the 16-way ladder to its
   else-branch.  Collapsing it by asserting sixteen `~(nblk = k)` hypotheses instead is
   ruinously slow: those hypotheses are walked once per simulation step and again by
   DISCHARGE_SAFETY_PROPERTY_TAC over the whole trace, which turns seconds into tens of
   minutes.  Hence the rewrite carries the already-present 17<=nblk and leaves no
   hypotheses behind. ---- *)
let GE17_LADDER_KILL_TAC : tactic = fun (asl,w) ->
  let neq = map (fun k ->
    EQF_INTRO (UNDISCH (ARITH_RULE
      (mk_imp(`17 <= nblk`, mk_neg(mk_eq(`nblk:num`, mk_small_numeral k))))))) (1--16) in
  let nle8 = EQF_INTRO
    (UNDISCH (ARITH_RULE `17 <= nblk ==> ~(nblk <= 8)`)) in
  (GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV)
      (COND_CLAUSES::nle8::neq) THEN
   REWRITE_TAC (nle8::neq)) (asl,w);;

let GE17_PREP_TAC =
  SUBGOAL_THEN `17 <= nblk /\ 9 <= nblk` STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `~(nblk <= 16)`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  GE17_LADDER_KILL_TAC;;

(* ---- RESHAPE the collapsed trace for SEQUENCE:
        APPEND ladder (APPEND loop front) -> APPEND (APPEND ladder (APPEND loop [])) front
   so SEQUENCE at the loop head peels e_front_tail = front, e_back = APPEND ladder (APPEND loop []).
   NOTE: must use ONCE_REWRITE_TAC (GEN_REWRITE_TAC with a RAND o ONCE_DEPTH path silently
   missed the intended APPEND occurrence). ---- *)
let RESHAPE_LOOP_TAC : tactic = fun (asl,w) ->
  let e2var = `e2:(uarch_event)list` in
  let e2eq = find_term (fun t -> is_eq t && lhs t = e2var
                 && (match rhs t with Comb(Comb(Const("APPEND",_),_),_) -> true | _ -> false)) w in
  let rhs_e2 = rhs e2eq in
  let a,bb,c = (match rhs_e2 with
     | Comb(Comb(Const("APPEND",_),a),Comb(Comb(Const("APPEND",_),bb),c)) -> a,bb,c
     | _ -> failwith "RESHAPE_LOOP_TAC: unexpected e2 shape") in
  let nil = `[]:(uarch_event)list` in
  let ap x y = mk_binop `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list` x y in
  let reshaped = ap (ap a (ap bb nil)) c in
  let reshape_thm = prove(mk_eq(rhs_e2, reshaped), REWRITE_TAC[APPEND_NIL; APPEND_ASSOC]) in
  ONCE_REWRITE_TAC[reshape_thm] (asl,w);;

(* ---- front invariant at pc+0x4c0 (the loop head; the i=0 register state of
   wbn_loop_invariant_raw).  SEQUENCE augments it with e2 = f_ev_front. ---- *)
let front_inv = `\s:armstate.
     aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
     read SP s = stackpointer /\
     read X0 s = word_add in_p (word 128) /\
     read X2 s = word_add out_p (word 128) /\
     read X4 s = word_add in_p (word (16 * nblk)) /\
     read X5 s = word_add (word (128 * ((nblk - 1) DIV 8))) in_p /\
     read X9 s = word (16 * nblk) /\
     read X10 s = word_add stackpointer (word 64) /\
     read X1 s = word (128 * nblk) /\
     read X16 s = ivec_p /\
     read X6 s = htbl_p /\
     read X3 s = xi_p /\
     read X11 s = key_p`;;

(* ---- nblk 5..8 shared front.  These four paths execute the same 270
   instructions from pc+0x20 through the taken branch at pc+0x44c and the
   common tail setup, landing at pc+0xee8 immediately before the tail compare.
   SEQUENCE augments the invariant with e2 = f_ev_58_front. ---- *)
let front_58_inv = `\s:armstate.
     aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
     read PC s = word (pc + 0xee8) /\
     read SP s = stackpointer /\
     read X0 s = in_p /\
     read X2 s = out_p /\
     read X3 s = xi_p /\
     read X4 s = word_add in_p (word (16 * nblk)) /\
     read X5 s = word (16 * nblk) /\
     read X6 s = htbl_p /\
     read X9 s = word (16 * nblk) /\
     read X10 s = word_add stackpointer (word 64) /\
     read X11 s = key_p /\
     read X16 s = ivec_p`;;

(* Collapse the first four concrete leaves of core_scaffold and expose the
   APPEND shared by the 5..8 band without first concretizing nblk. *)
let LE8_58_LADDER_OPEN_TAC : tactic = fun (asl,w) ->
  let neq = map (fun k ->
    EQF_INTRO (UNDISCH (ARITH_RULE
      (mk_imp(`5 <= nblk`, mk_neg(mk_eq(`nblk:num`, mk_small_numeral k))))))) (1--4) in
  (GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV)
      (COND_CLAUSES::(ASSUME `nblk <= 8`)::neq) THEN
   REWRITE_TAC neq) (asl,w);;

let FRONT_58_ENTER_TAC =
  SUBGOAL_THEN `5 <= nblk` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~(nblk <= 4)`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;
    ALL_TAC] THEN
  LE8_58_LADDER_OPEN_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xee8` front_58_inv THEN CONJ_TAC;;

let FRONT_58_CLOSE_TAC =
  SUBGOAL_THEN `word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)` ASSUME_TAC THENL
   [MATCH_MP_TAC USHR_128NBLK_ANY THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_and (word_sub (word (16 * nblk)) (word 1))
             (word 18446744073709551488):int64 = word 0`
   ASSUME_TAC THENL
   [MATCH_MP_TAC AND_MASK_16NBLK THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; ALLPAIRS; PAIRWISE; MAP; WB_MC_LEN]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPEC `nblk:num` GUARD_LE_FALLTHRU) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  ARM_QSTEPS_TAC EXEC (1--267) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `nblk:num` D_ZERO_LE8)
    (CONJ (MATCH_MP (ARITH_RULE `5 <= nblk ==> 1 <= nblk`) (ASSUME `5 <= nblk`))
          (ASSUME `nblk <= 8`))]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  SUBGOAL_THEN `ival (in_p:int64) - ival in_p = &0` ASSUME_TAC THENL
   [CONV_TAC INT_ARITH; ALL_TAC] THEN
  ARM_QSTEPS_TAC EXEC (268--270) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_sub (word_add in_p (word (16 * nblk))) in_p:int64 = word (16 * nblk)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let close_58_tail_band k =
  UNDISCH_TAC (mk_eq(`nblk:num`, mk_small_numeral k)) THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; ALLPAIRS; PAIRWISE; MAP; WB_MC_LEN]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  MP_WB_TAIL_SAFE_TAC k "s0"
   [`pc:num`; `stackpointer:int64`; `in_p:int64`; `out_p:int64`;
    `xi_p:int64`; `ivec_p:int64`; `key_p:int64`; `htbl_p:int64`;
    mk_small_numeral k; `in_p:int64`; `out_p:int64`] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[WB_CONTAINED_REFL; ALLPAIRS; ALL; WB_MC_LEN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN WB_FIRST_NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  USE_WB_TAIL_SAFE_TAC
   (GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    DISCHARGE_WB_COMPOSED_TAIL_TAC);;

(* ---- >=17 leg entry.  Leaves two subgoals: the front (pc+32 -> pc+1216), then the
   rest (loop + tail, pc+1216 -> pc+4560). ---- *)
let GE17_ENTER_TAC =
  GE17_PREP_TAC THEN RESHAPE_LOOP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x4c0` front_inv THEN CONJ_TAC;;

(* ---- the >=17 front leg, pc+32 -> pc+1216 (the loop head).  The branch at 0x4bc
   is the loop-entry compare, resolved off WB_PTRCMP_FLAGS and D_GT_128 rather than by
   the affine resolver, since both of its operands are symbolic in nblk. ---- *)
let GE17_FRONT_CLOSE_TAC =
  front_916_setup_tac THEN
  ARM_QSTEPS_TAC EXEC (1--295) THEN
  MP_TAC(SPECL [`in_p:int64`; `128`; `128 * ((nblk-1) DIV 8)`] WB_PTRCMP_FLAGS) THEN ANTS_TAC THENL
   [CONJ_TAC THEN MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
    MP_TAC(ASSUME `17 <= nblk`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  MP_TAC(SPEC `nblk:num` D_GT_128) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ARM_QSTEPS_TAC EXEC (296--296) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ---- loop invariant: the register state at the loop head on iteration i.  WHILE
   augments it with e2 = APPEND (ENUMERATEL i f_ev_loop) (APPEND [] front). ---- *)
let loop_inv = `\(i:num) s:armstate.
     aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
     read SP s = stackpointer /\
     read X0 s = word_add in_p (word (128 * (i + 1))) /\
     read X2 s = word_add out_p (word (128 * (i + 1))) /\
     read X4 s = word_add in_p (word (16 * nblk)) /\
     read X5 s = word_add (word (128 * ((nblk - 1) DIV 8))) in_p /\
     read X9 s = word (16 * nblk) /\
     read X10 s = word_add stackpointer (word 64) /\
     read X1 s = word (128 * nblk) /\
     read X16 s = ivec_p /\
     read X6 s = htbl_p /\
     read X3 s = xi_p /\
     read X11 s = key_p`;;

(* ---- LOOP decomposition: on the rest subgoal (prePC=pc+1216) after GE17 front closed.
        ENSURES_EVENTS_WHILE_UP2_TAC then REPEAT CONJ_TAC yields 4 subgoals in ORDER:
          G0 count-nonzero ~((nblk-9)DIV8=0)
          G1 entry (i=0)         prePC=pc+1216 (establish inv at 0)
          G2 loop BODY (forall i) -- the crux
          G3 exit/TAIL           prePC=pc+2576 -> pc+4560 (residue dispatch)   ---- *)
let GE17_LOOP_OPEN_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `(nblk - 9) DIV 8` `pc + 0x4c0` `pc + 0xa10` loop_inv THEN
  REPEAT CONJ_TAC;;

(* G0 count-nonzero *)
let GE17_COUNT_TAC =
  MP_TAC(ASSUME `17 <= nblk`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN ARITH_TAC;;

(* G1 entry (i=0): precond=postcond after normalizing 0+1, 128*1, ENUMERATEL 0, APPEND [], *1 *)
let GE17_ENTRY_TAC =
  ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ENUMERATEL; APPEND; ADD_CLAUSES; MULT_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_exists (concl th))) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES];;

(* G2, the loop body.  STRIP_EXISTS_ASSUM_TAC after ENSURES_INIT_TAC is required, not
   cosmetic: the invariant carries an accumulated `exists e2. read events s0 = APPEND e2 e
   /\ ...`, and unless it is stripped, `read events s0` is never exposed and the closing
   EXISTS_E2_TAC fails in AP_THM_TAC.  This mirrors what
   bignum_copy_row_from_table_8n.ml gets from ARM_SIM_TAC's
   ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC).  WBN_PC_BRIDGE already has i free, so it
   is MP'd rather than SPEC'd. *)
let ptrcmp_i = SPECL [`in_p:int64`; `128 * (i + 2)`; `128 * ((nblk - 1) DIV 8)`] WB_PTRCMP_FLAGS;;
let x0norm_i = WORD_RULE
  `word_add (word_add in_p (word (128 * (i + 1)))) (word 128):int64 = word_add in_p (word (128 * (i + 2)))`;;
let pcbridge_i = MP WBN_PC_BRIDGE (ASSUME `9 <= nblk`);;

let GE17_BODY_CLOSE_TAC =
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; ALLPAIRS; PAIRWISE; MAP; WB_MC_LEN]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_QSTEPS_TAC EXEC (1--340) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[x0norm_i]) THEN
  MP_TAC ptrcmp_i THEN ANTS_TAC THENL
   [CONJ_TAC THEN MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
    MP_TAC(ASSUME `i < (nblk - 9) DIV 8`) THEN MP_TAC(ASSUME `17 <= nblk`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SIMP_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pcbridge_i]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `(i + 1) + 1 = i + 2`; GSYM COND_RAND] THEN
  GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [CONJUNCT1 APPEND] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ---- G3, the exit/tail leg, pc+2576 -> pc+4560: a straight-line prepretail to
   pc+3816, then the 8-way dispatch on the leftover block count (nblk-9) MOD 8. ---- *)

(* the leftover-byte count left in X5 at pc+3816, guarded by 17<=nblk + no overflow. *)
let TAIL_LEFTOVER_BYTES = prove
  (`17 <= nblk /\ val (in_p:int64) + 16 * nblk < 2 EXP 63
     ==> word_sub (word_add in_p (word (16 * nblk)))
                  (word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1))))
         = word (16 * ((nblk - 9) MOD 8 + 1)):int64`,
   STRIP_TAC THEN
   SUBGOAL_THEN `16 * nblk = 128 * ((nblk - 9) DIV 8 + 1) + 16 * ((nblk - 9) MOD 8 + 1)` ASSUME_TAC THENL
    [MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
     MP_TAC(ASSUME `17 <= nblk`) THEN ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE);;

(* tail setup: init, strip the accumulated e2, and simulate only the shared
   prepretail prefix to the tail compare at pc+0xee8. *)
let GE17_TAIL_SETUP_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; ALLPAIRS; PAIRWISE; MAP; WB_MC_LEN]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_QSTEPS_TAC EXEC (1--310) THEN                (* pc+2576 -> pc+3816 *)
  MP_TAC TAIL_LEFTOVER_BYTES THEN ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  SUBGOAL_THEN `(nblk - 9) MOD 8 < 8` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC; ALL_TAC];;

let GE17_TAIL_SPLIT_TAC =
  SUBGOAL_THEN
   `(nblk-9)MOD 8 = 0 \/ (nblk-9)MOD 8 = 1 \/ (nblk-9)MOD 8 = 2 \/ (nblk-9)MOD 8 = 3 \/
    (nblk-9)MOD 8 = 4 \/ (nblk-9)MOD 8 = 5 \/ (nblk-9)MOD 8 = 6 \/ (nblk-9)MOD 8 = 7` MP_TAC THENL
   [MP_TAC(ASSUME `(nblk - 9) MOD 8 < 8`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC; ALL_TAC] THEN
   STRIP_TAC;;

(* per-residue closer: drive the concrete residue tail to pc+4560, collapse the ladder
   down to this residue's f_ev_t<rr>, then discharge. *)
let close_tail_residue rr =
  (* the DIVISION identity is load-bearing: without it CONTAINED_TAC's arithmetic
     cannot show the residue store at out_p+128*((nblk-9) DIV 8+1)+k is in bounds. *)
  SUBGOAL_THEN `16 * nblk = 128 * ((nblk - 9) DIV 8 + 1) + 16 * ((nblk - 9) MOD 8 + 1)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    MP_TAC(ASSUME `17 <= nblk`) THEN ARITH_TAC; ALL_TAC] THEN
  MP_WB_TAIL_SAFE_TAC (rr+1) "s310"
   [`pc:num`; `stackpointer:int64`; `in_p:int64`; `out_p:int64`;
    `xi_p:int64`; `ivec_p:int64`; `key_p:int64`; `htbl_p:int64`; `nblk:num`;
    `word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1))):int64`;
    `word_add out_p (word (128 * ((nblk - 9) DIV 8 + 1))):int64`] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; ALL; WB_MC_LEN] THEN
    REPEAT CONJ_TAC THEN
    (* This leg's antecedent needs two alternatives the 9..16 bands do not,
       because here nblk is still symbolic: three of the eight conjuncts are not
       discharged by the assumption hit.

       (a) `1 <= nblk` follows from the leg's `17 <= nblk`, so it needs an
       arithmetic closer.  It must be NBLK_ARITH_TAC, not ASM_ARITH_TAC: at this
       point the goal carries the ~60 post-simulation memory assumptions, and
       handing those to the arithmetic decision procedure exhausts memory.
       NBLK_ARITH_TAC keeps only the two nblk bounds and drops the rest before
       ARITH_TAC.

       (b) the two `contained (tail_ptr,16*(rr+1)) (base,16*nblk)` conjuncts need
       `contained` unfolded first: CONTAINED_TAC (common/components.ml)
       leads with GEN_REWRITE_TAC I [GSYM CONTAINED_MODULO_MOD2] and so only
       applies to a top-level contained_modulo -- on a folded `contained` it
       *raises* REWRITES_CONV rather than failing (of the rewrite tactics only
       the `I` traversal raises on a no-match).  prove_tail_safe above does the
       same REWRITE_TAC[contained] before its own contained closer.

       CONV_TAC NUM_REDUCE_CONV is deliberately NOT in this chain.  It cannot
       close any conjunct here (nblk is symbolic), and it "succeeds" as a *no-op*
       on the nonoverlapping, contained and `1 <= nblk` shapes alike -- so
       wherever it sits ahead of a real handler it satisfies ORELSE, that handler
       never runs, and the conjunct stays open, leaving the antecedent branch
       with nothing for ANTS_TAC's DISCH_TAC to discharge.  The 9..16
       bands can keep it only because nblk is a numeral there, so the reduction
       genuinely closes their conjuncts. *)
    (WB_FIRST_NONOVERLAPPING_TAC ORELSE
     (REWRITE_TAC[contained] THEN CONTAINED_TAC) ORELSE
     CONTAINED_TAC ORELSE
     NBLK_ARITH_TAC);
    ALL_TAC] THEN
  USE_WB_COMPOSED_TAIL_SAFE_TAC
   (GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN
    WB_TAIL_POST_ASM_REWRITE_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[
      ASSUME (mk_eq(`(nblk - 9) MOD 8`, mk_small_numeral rr))]) THEN
    GEN_REWRITE_TAC (ONCE_DEPTH_CONV)
      [ASSUME (mk_eq(`(nblk - 9) MOD 8`, mk_small_numeral rr))] THEN
    TRY(CONV_TAC WORD_RULE) THEN
    CONV_TAC(DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC[COND_CLAUSES] THEN
    GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [CONJUNCT1 APPEND] THEN
    DISCHARGE_WB_COMPOSED_TAIL_TAC);;

(* per-band closer for nblk 9..16, concretizing off the shared symbolic front. *)
let close_916_band k =
  let r = k - 8 in
  UNDISCH_TAC (mk_eq(`nblk:num`, mk_small_numeral k)) THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  (* s606, not s517: the shared front must walk all the way to the tail
     theorem's entry pc+3816, which is 89 steps past pc+3460.  And not s610 --
     by then X0 has advanced to in_p+144, so the eight precondition registers
     are simultaneously correct only at s606. *)
  MP_WB_TAIL_SAFE_TAC r "s606"
   [`pc:num`; `stackpointer:int64`; `in_p:int64`; `out_p:int64`;
    `xi_p:int64`; `ivec_p:int64`; `key_p:int64`; `htbl_p:int64`;
    mk_small_numeral k; `word_add in_p (word 128):int64`;
    `word_add out_p (word 128):int64`] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; ALL; WB_MC_LEN] THEN
    REPEAT CONJ_TAC THEN
    (* Order matters, and NUM_REDUCE must come LAST.  As a tactic,
       CONV_TAC NUM_REDUCE_CONV *succeeds without closing* on any conjunct that
       merely contains a reducible numeral: on `contained (in_p+128,16*1)
       (in_p,16*9)` it returns the same goal with `16*1`/`16*9` folded to
       `16`/`144`.  Listed first in an ORELSE it therefore swallows every
       structural conjunct and shadows the alternatives that would close them,
       leaving all six open -- which is silent, because a stage that leaves
       subgoals does not fail.  The two arithmetic conjuncts (`1 <= 9`,
       `128 * 9 < 2 EXP 64`) are the only ones NUM_REDUCE genuinely discharges.
       Of the rest, both `contained` goals close under the unfold and all four
       `nonoverlapping` goals under WB_FIRST_NONOVERLAPPING_TAC.  The >=17
       antecedent chain above avoids the same trap. *)
    ((REWRITE_TAC[contained] THEN CONTAINED_TAC) ORELSE
     CONTAINED_TAC ORELSE
     WB_FIRST_NONOVERLAPPING_TAC ORELSE
     (* Last resort, and note the retry: NUM_REDUCE is useful here in two
        different ways.  On the two arithmetic conjuncts it closes the goal
        outright.  On a structural conjunct whose numerals are still unfolded
        (`nonoverlapping (out_p,16 * 9) ...`) it closes nothing but normalizes
        the spelling, after which the structural closers above do apply -- so
        retry them rather than stopping.  TRY keeps the arithmetic case working,
        where the retry has nothing left to do. *)
     (CONV_TAC NUM_REDUCE_CONV THEN
      TRY((REWRITE_TAC[contained] THEN CONTAINED_TAC) ORELSE
          CONTAINED_TAC ORELSE
          WB_FIRST_NONOVERLAPPING_TAC)));
    ALL_TAC] THEN
  USE_WB_COMPOSED_TAIL_SAFE_TAC
   (GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN
    WB_TAIL_POST_ASM_REWRITE_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    (* WORD_RULE normalizes the tail's pointer arithmetic when any survives, but
       on these bands the preceding NUM_REDUCE already leaves the goal as the
       event-trace existential, which is not a word equation -- WORD_RULE then
       dies in RAND_CONV.  The 5..8 closer omits the step entirely for the same
       reason; TRY keeps it available without making it load-bearing. *)
    TRY(CONV_TAC WORD_RULE) THEN
    DISCHARGE_WB_COMPOSED_TAIL_TAC);;

(* ---- the core safety opening.  Unlike a `\s s'. true` frame, this one unfolds
   MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI up front so ENSURES_FINAL_STATE_TAC can
   discharge the real frame at every leaf; the wrapper needs the real frame, because it
   simulates the epilogue after the core big-step and so needs aligned_bytes_loaded
   preserved across it.  Mirrors BIGNUM_INV_P25519_SAFE. ---- *)
let CORE_SAFE_OPEN_TAC =
  CONCRETIZE_F_EVENTS_TAC core_scaffold THEN REPEAT META_EXISTS_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val (word (16 * nblk):int64) = 16 * nblk` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (128 * nblk):int64) = 128 * nblk` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC];;

let CORE_SAFE_TAC =
  CORE_SAFE_OPEN_TAC THEN
  ASM_CASES_TAC `nblk <= 8` THENL [
    ASM_CASES_TAC `nblk <= 4` THENL [
      split_close_tac 1 4;
      FRONT_58_ENTER_TAC THENL [
        FRONT_58_CLOSE_TAC;
        SUBGOAL_THEN `nblk=5\/nblk=6\/nblk=7\/nblk=8` MP_TAC THENL
         [MP_TAC(ASSUME `5 <= nblk`) THEN MP_TAC(ASSUME `nblk <= 8`) THEN
          POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC; ALL_TAC] THEN
        STRIP_TAC THENL
         [close_58_tail_band 5; close_58_tail_band 6;
          close_58_tail_band 7; close_58_tail_band 8]
      ]
    ];
    ASM_CASES_TAC `nblk <= 16` THENL [
      front_916_setup_tac THEN front_916_sim_tac THEN ARM_QSTEPS_TAC EXEC (297--606) THEN
      SUBGOAL_THEN `nblk=9\/nblk=10\/nblk=11\/nblk=12\/nblk=13\/nblk=14\/nblk=15\/nblk=16` MP_TAC THENL
       [MP_TAC(ASSUME `9 <= nblk`) THEN MP_TAC(ASSUME `nblk <= 16`) THEN
        POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THENL
       [close_916_band 9; close_916_band 10; close_916_band 11; close_916_band 12;
        close_916_band 13; close_916_band 14; close_916_band 15; close_916_band 16];
      GE17_ENTER_TAC THENL [
        GE17_FRONT_CLOSE_TAC;
        GE17_LOOP_OPEN_TAC THENL [
          GE17_COUNT_TAC;
          GE17_ENTRY_TAC;
          GE17_BODY_CLOSE_TAC;
          GE17_TAIL_SETUP_TAC THEN GE17_TAIL_SPLIT_TAC THENL
           [close_tail_residue 0; close_tail_residue 1; close_tail_residue 2;
            close_tail_residue 3; close_tail_residue 4; close_tail_residue 5;
            close_tail_residue 6; close_tail_residue 7]
        ]
      ]
    ]
  ];;

(* ---- the ABI wrapper.  Stock ARM_ADD_RETURN_STACK_TAC does not apply: the exported
   spec quantifies over the C argument bit_len, while the core below takes
   word (128 * nblk) with 1 <= nblk, and the prologue contains the entry guard, whose
   zero and non-multiple-of-128 branches return before the core.  The crossing is
   therefore hand-rolled, mirroring the functional wrapper WBN_DEC_SUBROUTINE_BYTELIST
   above. ---- *)

let WB_GUARD_FALLTHROUGH_TAC =
  SUBGOAL_THEN `val (word (128 * nblk):int64) = 128 * nblk` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(128 * nblk = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word_and (word (128 * nblk):int64) (word 127)) = 0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(127:num) = 2 EXP 7 - 1` SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(2:num) EXP 7 = 128` SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[MOD_MULT]; ALL_TAC];;

(* ---- the core safety theorem, over the real MAYCHANGE frame the wrapper needs.
   Its memaccess bounds are the assembly's exact footprint.  The public theorem
   below takes its bounds from the C signature through mk_safety_spec: the tag and
   ivec (16), key (240) and htable (192) bounds and the 80-byte frame equal this
   footprint, while the in/out bounds are the C length len_bits/8 (val bit_len DIV 8
   bytes), which contains the 16 * nblk footprint and equals it when
   bit_len = word (128 * nblk). ---- *)
let AESV8_GCM_8X_DEC_256_WB_SAFE = prove
 (`exists f_events.
     forall e pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk.
         1 <= nblk /\
         128 * nblk < 2 EXP 64 /\
         val in_p + 16 * nblk < 2 EXP 63 /\
         aligned 16 stackpointer /\
         ALLPAIRS nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16]
         [word pc,LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,16 * nblk;
          key_p,240; htbl_p,192; stackpointer,80] /\
         PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
         ALL (nonoverlapping (stackpointer,80))
         [word pc,LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,16 * nblk;
          key_p,240; htbl_p,192]
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
                  read PC s = word (pc + 32) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS
                  [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p]
                  s /\
                  read events s = e)
             (\s. read PC s = word (pc + 4560) /\
                  (exists e2.
                       read events s = APPEND e2 e /\
                       e2 =
                       f_events in_p key_p htbl_p out_p xi_p ivec_p nblk pc
                       stackpointer /\
                       memaccess_inbounds e2
                       [in_p,16 * nblk; xi_p,16; ivec_p,16;
                        key_p,240; htbl_p,192; out_p,16 * nblk;
                        stackpointer,80]
                       [out_p,16 * nblk; xi_p,16; ivec_p,16;
                        stackpointer,80]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
              [memory :> bytes (out_p,16 * nblk); memory :> bytes (xi_p,16);
               memory :> bytes (ivec_p,16);
               memory :> bytes (word_add stackpointer (word 64),16)] ,,
              MAYCHANGE
              [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13;
               Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25;
               Q26; Q27; Q28; Q29; Q30; Q31])`,
  CORE_SAFE_TAC);;

(* The wrapper's f_events gets an explicit three-path witness rather than
   CONCRETIZE + UNIFY_REFL.  The latter leaves the core's X_CHOOSE'd
   f_events_callee variable in the witness, which then escapes its scope and
   makes the CHOOSE fail at extraction.

   The public witness dispatches only on public bit_len:
   - invalid non-multiple: the three reject-path jumps;
   - zero: the cbz/return jumps;
   - valid nonzero: prologue stores/jumps, the core trace, and epilogue
     loads/return.

   f_events_core is a placeholder for the core's trace; the only part that
   cannot be written down is which variable holds it, since
   ASSUME_CALLEE_SAFETY_TAILED_TAC mints that name from a counter of its own
   (fresh_f_events_var_counter, in ASSUME_CALLEE_SAFETY_TAC). *)
let wrapper_witness_template =
 `\(in_p:int64) (key_p:int64) (htbl_p:int64) (out_p:int64) (xi_p:int64)
   (ivec_p:int64) (bit_len:int64) (pc:num) (sp:int64) (ra:int64).
     if val bit_len MOD 128 = 0 then
       if val bit_len = 0 then
         [EventJump (word (pc + 5956),ra);
          EventJump (word (pc + 4),word (pc + 5952))]
       else
         APPEND
           [EventJump (word (pc + 4580),ra); EventLoad (sp,16);
            EventLoad (word_add sp (word 48),16);
            EventLoad (word_add sp (word 32),16);
            EventLoad (word_add sp (word 16),16)]
           (APPEND
             (f_events_core in_p key_p htbl_p out_p xi_p ivec_p
               (gcm_dec_wb_blocks bit_len) pc sp)
             [EventStore (word_add sp (word 48),16);
              EventStore (word_add sp (word 32),16);
              EventStore (word_add sp (word 16),16); EventStore (sp,16);
              EventJump (word (pc + 12),word (pc + 16));
              EventJump (word (pc + 4),word (pc + 8))])
     else
       [EventJump (word (pc + 5956),ra);
        EventJump (word (pc + 12),word (pc + 5952));
        EventJump (word (pc + 4),word (pc + 8))]:(uarch_event)list`;;

let f_events_core_placeholder =
  find_term (fun t -> is_var t && name_of t = "f_events_core")
            wrapper_witness_template;;

(* Plug the core's chosen f_events variable into the template above.  The corpus reads
   that variable the same way, by its name prefix: EXISTS_E2_TAC and
   FULL_UNIFY_F_EVENTS_TAC in common/consttime.ml. *)
let build_wrapper_witness (asl:(string*thm)list) : term =
  let fev = find_term
     (fun t -> is_var t && find_substring (name_of t) "f_events_callee" <> None)
     (concl (assoc "CORE" asl)) in
  subst [fev, f_events_core_placeholder] wrapper_witness_template;;

let ARBITRARY_WRAPPER_SAFE_TAC coreth =
  ASSUME_CALLEE_SAFETY_TAILED_TAC coreth "CORE" THEN
  W(fun (asl,w) -> EXISTS_TAC (build_wrapper_witness asl)) THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES;PAIRWISE;ALLPAIRS;ALL] THEN
  REWRITE_TAC[C_ARGUMENTS;C_RETURN;SOME_FLAGS] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN BETA_TAC THEN
  ABBREV_TAC `nblk = gcm_dec_wb_blocks bit_len` THEN
  ASM_CASES_TAC `val(bit_len:int64) MOD 128 = 0` THENL
   [ALL_TAC;
    (* Invalid non-multiple: reject before any memory access. *)
    SUBGOAL_THEN `nblk = 0` SUBST_ALL_TAC THENL
     [EXPAND_TAC "nblk" THEN REWRITE_TAC[gcm_dec_wb_blocks] THEN
      ASM_REWRITE_TAC[COND_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(val(bit_len:int64) = 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~(val(bit_len:int64) MOD 128 = 0)` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~(val(word_and (bit_len:int64) (word 127)) = 0)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `127 = 2 EXP 7 - 1` SUBST1_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
      ASM_REWRITE_TAC[ARITH_RULE `2 EXP 7 = 128`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[COND_CLAUSES;MULT_CLAUSES;ADD_CLAUSES] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
      MODIFIABLE_SIMD_REGS;MODIFIABLE_GPRS;MODIFIABLE_UPPER_SIMD_REGS;
      fst EXEC] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC
     `[EventJump (word (pc + 5956),returnaddress);
       EventJump (word (pc + 12),word (pc + 5952));
       EventJump (word (pc + 4),word (pc + 8))]:(uarch_event)list` THEN
    REWRITE_TAC[APPEND;memaccess_inbounds;ALL;EX;FST;SND]] THEN
  ASM_CASES_TAC `val(bit_len:int64) = 0` THENL
   [(* Zero: cbz returns before the stack saves. *)
    SUBGOAL_THEN `nblk = 0` SUBST_ALL_TAC THENL
     [EXPAND_TAC "nblk" THEN REWRITE_TAC[gcm_dec_wb_blocks] THEN
      ASM_REWRITE_TAC[COND_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `bit_len:int64 = word 0` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[GSYM VAL_EQ_0];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[COND_CLAUSES;MULT_CLAUSES;ADD_CLAUSES] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
      MODIFIABLE_SIMD_REGS;MODIFIABLE_GPRS;MODIFIABLE_UPPER_SIMD_REGS;
      fst EXEC] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC
     `[EventJump (word (pc + 5956),returnaddress);
       EventJump (word (pc + 4),word (pc + 5952))]:(uarch_event)list` THEN
    REWRITE_TAC[APPEND;VAL_WORD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[memaccess_inbounds;ALL;EX;FST;SND];
    ALL_TAC] THEN
  (* Valid nonzero: recover word (128*nblk), then use the valid-only core
     safety theorem inside the existing wrapper simulation. *)
  SUBGOAL_THEN `1 <= nblk` ASSUME_TAC THENL
   [EXPAND_TAC "nblk" THEN REWRITE_TAC[gcm_dec_wb_blocks] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`val(bit_len:int64)`; `128`]
      (CONJUNCT2 DIVISION_SIMP)) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(bit_len:int64) = 128 * nblk` ASSUME_TAC THENL
   [EXPAND_TAC "nblk" THEN ASM_SIMP_TAC[GCM_DEC_WB_BLOCKS_VALID];
    ALL_TAC] THEN
  SUBGOAL_THEN `128 * nblk < 2 EXP 64` ASSUME_TAC THENL
   [MP_TAC(ISPEC `bit_len:int64` VAL_BOUND_64) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bit_len:int64 = word (128 * nblk)` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if concl th = `val(bit_len:int64) = 128 * nblk`
      then MP_TAC th else failwith "") THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[COND_CLAUSES] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;MODIFIABLE_SIMD_REGS;
    MODIFIABLE_GPRS;MODIFIABLE_UPPER_SIMD_REGS;fst EXEC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun c -> ENSURES_PRESERVED_DREG_TAC ("init_"^fst(dest_const c)) c)
    [`D8`;`D9`;`D10`;`D11`;`D12`;`D13`;`D14`;`D15`] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
  WB_GUARD_FALLTHROUGH_TAC THEN ARM_STEPS_TAC EXEC (1--8) THEN
  W(fun (asl,w) ->
     let s8ev = find (fun (_,th) -> let c = concl th in
         is_eq c && (try rator(lhs c) = `read events` with _ -> false)
                  && (try rand(lhs c) = `s8:armstate` with _ -> false)) asl in
     let pd =
       subst [`[]:(uarch_event)list`,`e:(uarch_event)list`]
         (rhs (concl (snd s8ev))) in
     USE_THEN "CORE" (fun cth -> MP_TAC (SPECL
       [`e:(uarch_event)list`;`pc:num`;
        `word_sub stackpointer (word 80):int64`;
        `in_p:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
        `key_p:int64`;`htbl_p:int64`;`nblk:num`;pd] cth))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES;PAIRWISE;ALLPAIRS;ALL] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC ALIGNED_WORD_SUB THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[aligned;WORD_VAL] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_DIVIDES_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;MODIFIABLE_SIMD_REGS;
    MODIFIABLE_GPRS;MODIFIABLE_UPPER_SIMD_REGS;fst EXEC] THEN
  ARM_BIGSTEP_TAC EXEC "s9" THENL
   [REWRITE_TAC[C_ARGUMENTS;APPEND] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ARM_STEPS_TAC EXEC (10--15) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [HINT_EXISTS_REFL_TAC THEN
    REWRITE_TAC[GSYM APPEND_ASSOC;APPEND] THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC;
    REWRITE_TAC
     [WORD_BLAST`(word_zx:int128->int64)(word_zx(x:int64))=x`] THEN
    CONV_TAC WORD_RULE];;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "aesv8_gcm_8x_dec_256_wb" subroutine_signatures)
    AESV8_GCM_8X_DEC_256_WB_SUBROUTINE_CORRECT
    AESV8_GCM_8X_DEC_256_WB_EXEC;;

(* The statement of the exported safety theorem, for an arbitrary bit_len.  The
   theorem below is proved as the full_spec that mk_safety_spec generates above
   from AESV8_GCM_8X_DEC_256_WB_SUBROUTINE_CORRECT and the C signature, and the
   load fails unless that term is exactly the one written here:
   - the correctness theorem's hypotheses: the signed pointer bound, the stack
     alignment and the nonoverlapping lists;
   - access bounds sized by the C objects: in/out len_bits/8, tag 16, ivec 16,
     key 240, htable 24 * 8 = 192, and the 80-byte frame;
   - by keep_maychanges, the correctness theorem's MAYCHANGE frame, based on
     gcm_dec_wb_blocks.
   Apart from the loaded code it constrains no memory contents (no key
   schedule, table, tag, counter or data precondition), so it holds for every
   content.
   This routine does not enforce the NIST GCM message limit. Callers must
   ensure the cumulative message length does not exceed 2^36 - 32 bytes
   (2^39 - 256 bits). *)
let AESV8_GCM_8X_DEC_256_WB_SUBROUTINE_SAFE = prove
 (`exists f_events.
     forall e pc stackpointer in_p bit_len out_p xi_p ivec_p key_p htbl_p
            returnaddress.
         val in_p + 16 * gcm_dec_wb_blocks bit_len < 2 EXP 63 /\
         aligned 16 stackpointer /\
         ALLPAIRS nonoverlapping
         [out_p,16 * gcm_dec_wb_blocks bit_len; xi_p,16; ivec_p,16]
         [word pc,LENGTH aesv8_gcm_8x_dec_256_wb_mc;
          in_p,16 * gcm_dec_wb_blocks bit_len; key_p,240; htbl_p,192;
          word_sub stackpointer (word 80),80] /\
         PAIRWISE nonoverlapping
         [out_p,16 * gcm_dec_wb_blocks bit_len; xi_p,16; ivec_p,16] /\
         ALL (nonoverlapping (word_sub stackpointer (word 80),80))
         [word pc,LENGTH aesv8_gcm_8x_dec_256_wb_mc;
          in_p,16 * gcm_dec_wb_blocks bit_len; key_p,240; htbl_p,192]
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    aesv8_gcm_8x_dec_256_wb_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS
                  [in_p; bit_len; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                       read events s = APPEND e2 e /\
                       e2 =
                       f_events in_p key_p htbl_p out_p xi_p ivec_p bit_len pc
                         (word_sub stackpointer (word 80)) returnaddress /\
                       memaccess_inbounds e2
                       [in_p,val bit_len DIV 8 * 1; xi_p,16; ivec_p,16;
                        key_p,240; htbl_p,192; out_p,val bit_len DIV 8 * 1;
                        word_sub stackpointer (word 80),80]
                       [out_p,val bit_len DIV 8 * 1; xi_p,16; ivec_p,16;
                        word_sub stackpointer (word 80),80]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
              [memory :> bytes (out_p,16 * gcm_dec_wb_blocks bit_len);
               memory :> bytes (xi_p,16);
               memory :> bytes (ivec_p,16);
               memory :> bytes (word_sub stackpointer (word 80),80)])`,
  ASSERT_CONCL_TAC full_spec THEN
  ARBITRARY_WRAPPER_SAFE_TAC AESV8_GCM_8X_DEC_256_WB_SAFE);;
