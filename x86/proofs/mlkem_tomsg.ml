(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a polynomial to a 32-byte message.                          *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "x86/proofs/utils/mlkem_bytes.ml";;
needs "x86/proofs/utils/mlkem_lanes.ml";;
needs "x86/proofs/utils/mlkem_codec_specs.ml";;

(**** print_literal_from_elf "x86/mlkem/mlkem_tomsg.o";;
 ****)

let mlkem_tomsg_mc = define_assert_from_elf
  "mlkem_tomsg_mc" "x86/mlkem/mlkem_tomsg.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x41; 0x03; 0x41; 0x03;
                           (* MOV (% eax) (Imm32 (word 54592321)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0xc1; 0x09; 0xc1; 0x09;
                           (* MOV (% eax) (Imm32 (word 163645889)) *)
  0xc5; 0xf9; 0x6e; 0xc8;  (* VMOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xc5; 0xfe; 0x6f; 0x16;  (* VMOVDQU (%_% ymm2) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0xed; 0xf9; 0xd8;  (* VPSUBW (%_% ymm3) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0xed; 0xf9; 0xd1;  (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm1) *)
  0xc5; 0xe5; 0xdf; 0xd2;  (* VPANDN (%_% ymm2) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0xed; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm2) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0xfe; 0x6f; 0x66; 0x20;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0xdd; 0xf9; 0xe8;  (* VPSUBW (%_% ymm5) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0xf9; 0xe1;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xd5; 0xdf; 0xe4;  (* VPANDN (%_% ymm4) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x0f;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0xed; 0x67; 0xd4;  (* VPACKUSWB (%_% ymm2) (%_% ymm2) (%_% ymm4) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xd2; 0xd8;
                           (* VPERMQ (%_% ymm2) (%_% ymm2) (Imm8 (word 216)) *)
  0xc5; 0xed; 0x71; 0xf2; 0x07;
                           (* VPSLLW (%_% ymm2) (%_% ymm2) (Imm8 (word 7)) *)
  0xc5; 0xfd; 0xd7; 0xc2;  (* VPMOVMSKB (% eax) (%_% ymm2) *)
  0x89; 0x07;              (* MOV (Memop Doubleword (%% (rdi,0))) (% eax) *)
  0xc5; 0xfe; 0x6f; 0x56; 0x40;
                           (* VMOVDQU (%_% ymm2) (Memop Word256 (%% (rsi,64))) *)
  0xc5; 0xed; 0xf9; 0xd8;  (* VPSUBW (%_% ymm3) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0xed; 0xf9; 0xd1;  (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm1) *)
  0xc5; 0xe5; 0xdf; 0xd2;  (* VPANDN (%_% ymm2) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0xed; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm2) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0xfe; 0x6f; 0x66; 0x60;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsi,96))) *)
  0xc5; 0xdd; 0xf9; 0xe8;  (* VPSUBW (%_% ymm5) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0xf9; 0xe1;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xd5; 0xdf; 0xe4;  (* VPANDN (%_% ymm4) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x0f;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0xed; 0x67; 0xd4;  (* VPACKUSWB (%_% ymm2) (%_% ymm2) (%_% ymm4) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xd2; 0xd8;
                           (* VPERMQ (%_% ymm2) (%_% ymm2) (Imm8 (word 216)) *)
  0xc5; 0xed; 0x71; 0xf2; 0x07;
                           (* VPSLLW (%_% ymm2) (%_% ymm2) (Imm8 (word 7)) *)
  0xc5; 0xfd; 0xd7; 0xc2;  (* VPMOVMSKB (% eax) (%_% ymm2) *)
  0x89; 0x47; 0x04;        (* MOV (Memop Doubleword (%% (rdi,4))) (% eax) *)
  0xc5; 0xfe; 0x6f; 0x96; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm2) (Memop Word256 (%% (rsi,128))) *)
  0xc5; 0xed; 0xf9; 0xd8;  (* VPSUBW (%_% ymm3) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0xed; 0xf9; 0xd1;  (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm1) *)
  0xc5; 0xe5; 0xdf; 0xd2;  (* VPANDN (%_% ymm2) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0xed; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm2) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0xfe; 0x6f; 0xa6; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsi,160))) *)
  0xc5; 0xdd; 0xf9; 0xe8;  (* VPSUBW (%_% ymm5) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0xf9; 0xe1;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xd5; 0xdf; 0xe4;  (* VPANDN (%_% ymm4) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x0f;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0xed; 0x67; 0xd4;  (* VPACKUSWB (%_% ymm2) (%_% ymm2) (%_% ymm4) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xd2; 0xd8;
                           (* VPERMQ (%_% ymm2) (%_% ymm2) (Imm8 (word 216)) *)
  0xc5; 0xed; 0x71; 0xf2; 0x07;
                           (* VPSLLW (%_% ymm2) (%_% ymm2) (Imm8 (word 7)) *)
  0xc5; 0xfd; 0xd7; 0xc2;  (* VPMOVMSKB (% eax) (%_% ymm2) *)
  0x89; 0x47; 0x08;        (* MOV (Memop Doubleword (%% (rdi,8))) (% eax) *)
  0xc5; 0xfe; 0x6f; 0x96; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm2) (Memop Word256 (%% (rsi,192))) *)
  0xc5; 0xed; 0xf9; 0xd8;  (* VPSUBW (%_% ymm3) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0xed; 0xf9; 0xd1;  (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm1) *)
  0xc5; 0xe5; 0xdf; 0xd2;  (* VPANDN (%_% ymm2) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0xed; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm2) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0xfe; 0x6f; 0xa6; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsi,224))) *)
  0xc5; 0xdd; 0xf9; 0xe8;  (* VPSUBW (%_% ymm5) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0xf9; 0xe1;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xd5; 0xdf; 0xe4;  (* VPANDN (%_% ymm4) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x0f;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0xed; 0x67; 0xd4;  (* VPACKUSWB (%_% ymm2) (%_% ymm2) (%_% ymm4) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xd2; 0xd8;
                           (* VPERMQ (%_% ymm2) (%_% ymm2) (Imm8 (word 216)) *)
  0xc5; 0xed; 0x71; 0xf2; 0x07;
                           (* VPSLLW (%_% ymm2) (%_% ymm2) (Imm8 (word 7)) *)
  0xc5; 0xfd; 0xd7; 0xc2;  (* VPMOVMSKB (% eax) (%_% ymm2) *)
  0x89; 0x47; 0x0c;        (* MOV (Memop Doubleword (%% (rdi,12))) (% eax) *)
  0xc5; 0xfe; 0x6f; 0x96; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm2) (Memop Word256 (%% (rsi,256))) *)
  0xc5; 0xed; 0xf9; 0xd8;  (* VPSUBW (%_% ymm3) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0xed; 0xf9; 0xd1;  (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm1) *)
  0xc5; 0xe5; 0xdf; 0xd2;  (* VPANDN (%_% ymm2) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0xed; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm2) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0xfe; 0x6f; 0xa6; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsi,288))) *)
  0xc5; 0xdd; 0xf9; 0xe8;  (* VPSUBW (%_% ymm5) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0xf9; 0xe1;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xd5; 0xdf; 0xe4;  (* VPANDN (%_% ymm4) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x0f;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0xed; 0x67; 0xd4;  (* VPACKUSWB (%_% ymm2) (%_% ymm2) (%_% ymm4) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xd2; 0xd8;
                           (* VPERMQ (%_% ymm2) (%_% ymm2) (Imm8 (word 216)) *)
  0xc5; 0xed; 0x71; 0xf2; 0x07;
                           (* VPSLLW (%_% ymm2) (%_% ymm2) (Imm8 (word 7)) *)
  0xc5; 0xfd; 0xd7; 0xc2;  (* VPMOVMSKB (% eax) (%_% ymm2) *)
  0x89; 0x47; 0x10;        (* MOV (Memop Doubleword (%% (rdi,16))) (% eax) *)
  0xc5; 0xfe; 0x6f; 0x96; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm2) (Memop Word256 (%% (rsi,320))) *)
  0xc5; 0xed; 0xf9; 0xd8;  (* VPSUBW (%_% ymm3) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0xed; 0xf9; 0xd1;  (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm1) *)
  0xc5; 0xe5; 0xdf; 0xd2;  (* VPANDN (%_% ymm2) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0xed; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm2) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0xfe; 0x6f; 0xa6; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsi,352))) *)
  0xc5; 0xdd; 0xf9; 0xe8;  (* VPSUBW (%_% ymm5) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0xf9; 0xe1;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xd5; 0xdf; 0xe4;  (* VPANDN (%_% ymm4) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x0f;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0xed; 0x67; 0xd4;  (* VPACKUSWB (%_% ymm2) (%_% ymm2) (%_% ymm4) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xd2; 0xd8;
                           (* VPERMQ (%_% ymm2) (%_% ymm2) (Imm8 (word 216)) *)
  0xc5; 0xed; 0x71; 0xf2; 0x07;
                           (* VPSLLW (%_% ymm2) (%_% ymm2) (Imm8 (word 7)) *)
  0xc5; 0xfd; 0xd7; 0xc2;  (* VPMOVMSKB (% eax) (%_% ymm2) *)
  0x89; 0x47; 0x14;        (* MOV (Memop Doubleword (%% (rdi,20))) (% eax) *)
  0xc5; 0xfe; 0x6f; 0x96; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm2) (Memop Word256 (%% (rsi,384))) *)
  0xc5; 0xed; 0xf9; 0xd8;  (* VPSUBW (%_% ymm3) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0xed; 0xf9; 0xd1;  (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm1) *)
  0xc5; 0xe5; 0xdf; 0xd2;  (* VPANDN (%_% ymm2) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0xed; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm2) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0xfe; 0x6f; 0xa6; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsi,416))) *)
  0xc5; 0xdd; 0xf9; 0xe8;  (* VPSUBW (%_% ymm5) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0xf9; 0xe1;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xd5; 0xdf; 0xe4;  (* VPANDN (%_% ymm4) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x0f;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0xed; 0x67; 0xd4;  (* VPACKUSWB (%_% ymm2) (%_% ymm2) (%_% ymm4) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xd2; 0xd8;
                           (* VPERMQ (%_% ymm2) (%_% ymm2) (Imm8 (word 216)) *)
  0xc5; 0xed; 0x71; 0xf2; 0x07;
                           (* VPSLLW (%_% ymm2) (%_% ymm2) (Imm8 (word 7)) *)
  0xc5; 0xfd; 0xd7; 0xc2;  (* VPMOVMSKB (% eax) (%_% ymm2) *)
  0x89; 0x47; 0x18;        (* MOV (Memop Doubleword (%% (rdi,24))) (% eax) *)
  0xc5; 0xfe; 0x6f; 0x96; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm2) (Memop Word256 (%% (rsi,448))) *)
  0xc5; 0xed; 0xf9; 0xd8;  (* VPSUBW (%_% ymm3) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0xed; 0xf9; 0xd1;  (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm1) *)
  0xc5; 0xe5; 0xdf; 0xd2;  (* VPANDN (%_% ymm2) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0xed; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm2) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0xfe; 0x6f; 0xa6; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsi,480))) *)
  0xc5; 0xdd; 0xf9; 0xe8;  (* VPSUBW (%_% ymm5) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0xf9; 0xe1;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xd5; 0xdf; 0xe4;  (* VPANDN (%_% ymm4) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x0f;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0xed; 0x67; 0xd4;  (* VPACKUSWB (%_% ymm2) (%_% ymm2) (%_% ymm4) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xd2; 0xd8;
                           (* VPERMQ (%_% ymm2) (%_% ymm2) (Imm8 (word 216)) *)
  0xc5; 0xed; 0x71; 0xf2; 0x07;
                           (* VPSLLW (%_% ymm2) (%_% ymm2) (Imm8 (word 7)) *)
  0xc5; 0xfd; 0xd7; 0xc2;  (* VPMOVMSKB (% eax) (%_% ymm2) *)
  0x89; 0x47; 0x1c;        (* MOV (Memop Doubleword (%% (rdi,28))) (% eax) *)
  0xc5; 0xf8; 0x77;        (* VZEROUPPER *)
  0xc3                     (* RET *)
];;

let mlkem_tomsg_tmc = define_trimmed "mlkem_tomsg_tmc" mlkem_tomsg_mc;;

let MLKEM_TOMSG_TMC_EXEC = X86_MK_CORE_EXEC_RULE mlkem_tomsg_tmc;;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to one bit, as a comparison, and as the  *)
(* code computes it for a coefficient in range: the sign bit of the AND-NOT  *)
(* of x - 2497 with x - 833, shifted down; and the simplifications of the    *)
(* packing of those bits (VPACKUSWB saturating bits does nothing) and of    *)
(* the mask (VPMOVMSKB) used in the simulation.                              *)
(* ------------------------------------------------------------------------- *)

let TOMSG_COMPRESS = prove
 (`!x:int16.
        val x < 3329
        ==> ((4 * val x + 3329) DIV 6658) MOD 2 =
            bitval(word_ugt (word 1664) (word_sub x (word 833)))`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_UGT; VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(x:int16)`,`n:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `n < 833` THENL
   [SUBGOAL_THEN `(4 * n + 3329) DIV 6658 = 0` SUBST1_TAC THENL
     [REWRITE_TAC[DIV_EQ_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `n < 833 ==> ~(833 <= n)`];
    ASM_SIMP_TAC[ARITH_RULE `~(n < 833) ==> 833 <= n`] THEN
    ASM_CASES_TAC `n < 2497` THENL
     [SUBGOAL_THEN `(4 * n + 3329) DIV 6658 = 1` SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `4 * n - 3329` THEN
        REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC;
        ALL_TAC];
      SUBGOAL_THEN `(4 * n + 3329) DIV 6658 = 2` SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `4 * n - 9987` THEN
        ASM_ARITH_TAC;
        ALL_TAC]]] THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_ARITH_TAC);;

let TOMSG_LANE = prove
 (`!x:int16.
        val x < 3329
        ==> word_zx(word_ushr (word_and (word_not (word_sub x (word 833)))
                                        (word_sub x (word 2497))) 15):byte =
            word(bitval(word_ugt (word 1664) (word_sub x (word 833))))`,
  BITBLAST_TAC);;

let TOMSG_SAT = prove
 (`!x:int16. word(MIN (if bit 15 (word_ushr x 15) then 0
                      else val(word_ushr x 15)) 255):byte =
            word_zx(word_ushr x 15)`,
  GEN_TAC THEN
  SUBGOAL_THEN `~bit 15 (word_ushr (x:int16) 15)` (fun th -> REWRITE_TAC[th])
  THENL [BITBLAST_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_ushr (x:int16) 15) < 2` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_USHR] THEN MP_TAC(ISPEC `x:int16` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_16] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < 2 ==> MIN n 255 = n`] THEN
  REWRITE_TAC[word_zx]);;

let TOMSG_MASK32 = MASK_JOIN_RULE 32;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The message is checked bit by bit.                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_TOMSG_CORRECT = prove
 (`!r a x pc.
        ALL (nonoverlapping (r,32)) [(word pc,593); (a,512)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mlkem_tomsg_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = word(pc + 593) /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,32)) s =
                       nsum {i | i < 256}
                            (\i. ((4 * val(x i) + 3329) DIV 6658) MOD 2 *
                                 2 EXP i)))
             (MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                         ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14;
                         ZMM15] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(r,32)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; ALL; SOME_FLAGS; fst MLKEM_TOMSG_TMC_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Manually expand the cases in the hypotheses ***)

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 4
            (subst[mk_small_numeral(32*n),`n:num`]
                  `read (memory :> bytes256(word_add a (word n))) s0`))
            (0--15))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  STRIP_TAC THEN

  (*** Simulate, folding the packing of the bits into joins of bytes ***)

  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_TOMSG_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_NOT_TAC
                       (map GSYM [TOMSG_SAT; GSYM ADD_ASSOC;
                                  CONV_RULE NUM_REDUCE_CONV BYTES256_JOIN]))
            (1--127) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** The masks as joins of bits, and the bits as comparisons ***)

  RULE_ASSUM_TAC(REWRITE_RULE[TOMSG_MASK32]) THEN
  DISCH_THEN(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE
     (map (fun i -> MP (SPEC (mk_comb(`x:num->int16`,mk_small_numeral i))
                             TOMSG_LANE)
                       (MP (SPEC (mk_small_numeral i) th)
                           (EQT_ELIM(NUM_REDUCE_CONV
                             (mk_binop `(<):num->num->bool`
                                (mk_small_numeral i) `256`)))))
          (0--255))) THEN
    ASSUME_TAC th) THEN

  (*** The message bit by bit ***)

  MATCH_MP_TAC READ_MEMORY_BYTES_EQ_BITS THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8 * 32 = 256`] THEN
    MATCH_MP_TAC(REWRITE_RULE[MULT_CLAUSES] (SPEC `1` NSUM_FIELD_BOUND)) THEN
    REWRITE_TAC[EXP_1; MOD_LT_EQ; ARITH_EQ];
    ALL_TAC] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  UNDISCH_TAC `p < 8 * 32` THEN REWRITE_TAC[ARITH_RULE `8 * 32 = 256`] THEN
  DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NSUM_BIT o rand o snd) THEN
  ASM_REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP TOMSG_COMPRESS) THEN
  REWRITE_TAC[BITVAL_EQ_1] THEN

  (*** Split the stored words into bytes and look at each bit ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
   check (can (term_match [] `read (memory :> bytes32 a) s = xxx`) o
          concl))) THEN
  UNDISCH_TAC `p < 256` THEN SPEC_TAC(`p:num`,`p:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s127" THEN
  CHUNKED_CMP_BITBLAST_TAC 8);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the IBT landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_TOMSG_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a x pc stackpointer returnaddress.
        ALL (nonoverlapping (r,32))
            [(word pc,LENGTH mlkem_tomsg_tmc); (a,512); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_tomsg_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,32)) s =
                       nsum {i | i < 256}
                            (\i. ((4 * val(x i) + 3329) DIV 6658) MOD 2 *
                                 2 EXP i)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,32)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_tomsg_tmc MLKEM_TOMSG_CORRECT);;

let MLKEM_TOMSG_SUBROUTINE_CORRECT = prove
 (`!r a x pc stackpointer returnaddress.
        ALL (nonoverlapping (r,32))
            [(word pc,LENGTH mlkem_tomsg_mc); (a,512); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_tomsg_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,32)) s =
                       nsum {i | i < 256}
                            (\i. ((4 * val(x i) + 3329) DIV 6658) MOD 2 *
                                 2 EXP i)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,32)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_TOMSG_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_tomsg" subroutine_signatures)
    MLKEM_TOMSG_CORRECT
    MLKEM_TOMSG_TMC_EXEC;;

let MLKEM_TOMSG_SAFE = time prove
 (`exists f_events.
    forall e r a pc.
        ALL (nonoverlapping (r,32)) [word pc,593; a,512]
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) (BUTLAST mlkem_tomsg_tmc) /\
                 read RIP s = word pc /\
                 C_ARGUMENTS [r; a] s /\
                 read events s = e)
            (\s.
                 read RIP s = word (pc + 593) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events a r pc /\
                      memaccess_inbounds e2 [a,512; r,32] [r,32]))
            (MAYCHANGE [RIP] ,,
             MAYCHANGE [RAX] ,,
             MAYCHANGE
             [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9;
              ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes (r,32)])`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_TOMSG_TMC_EXEC);;

let MLKEM_TOMSG_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e r a pc stackpointer returnaddress.
        ALL (nonoverlapping (r,32))
            [word pc,LENGTH mlkem_tomsg_tmc; a,512; stackpointer,8]
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) mlkem_tomsg_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events a r pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,512; r,32; stackpointer,8]
                      [r,32; stackpointer,8]))
            (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_tomsg_tmc MLKEM_TOMSG_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_TOMSG_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e r a pc stackpointer returnaddress.
        ALL (nonoverlapping (r,32))
            [word pc,LENGTH mlkem_tomsg_mc; a,512; stackpointer,8]
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) mlkem_tomsg_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events a r pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,512; r,32; stackpointer,8]
                      [r,32; stackpointer,8]))
            (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_TOMSG_NOIBT_SUBROUTINE_SAFE));;
