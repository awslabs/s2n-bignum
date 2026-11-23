(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling from the centered binomial distribution with eta = 2.            *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "x86/proofs/utils/mlkem_bytes.ml";;
needs "x86/proofs/utils/mlkem_lanes.ml";;

(**** print_literal_from_elf "x86/mlkem/mlkem_cbd2.o";;
 ****)

let mlkem_cbd2_mc = define_assert_from_elf
  "mlkem_cbd2_mc" "x86/mlkem/mlkem_cbd2.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x0f; 0x00; 0x0f; 0x00;
                           (* MOV (% eax) (Imm32 (word 983055)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0x00; 0x80; 0x00; 0x80;
                           (* MOV (% eax) (Imm32 (word 2147516416)) *)
  0xc5; 0xf9; 0x6e; 0xc8;  (* VMOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0x48; 0xb8; 0x02; 0x03; 0x03; 0x04; 0x01; 0x02; 0x02; 0x03;
                           (* MOV (% rax) (Imm64 (word 216737935452734210)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xd0;
                           (* VMOVQ (%_% xmm2) (% rax) *)
  0x48; 0xb8; 0x01; 0x02; 0x02; 0x03; 0x00; 0x01; 0x01; 0x02;
                           (* MOV (% rax) (Imm64 (word 144397762614657537)) *)
  0xc4; 0xe3; 0xe9; 0x22; 0xd0; 0x01;
                           (* VPINSRQ (%_% xmm2) (%_% xmm2) (% rax) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x6d; 0x38; 0xd2; 0x01;
                           (* VINSERTI128 (%_% ymm2) (%_% ymm2) (%_% xmm2) (Imm8 (word 1)) *)
  0xb8; 0x02; 0x00; 0x02; 0x00;
                           (* MOV (% eax) (Imm32 (word 131074)) *)
  0xc5; 0xf9; 0x6e; 0xd8;  (* VMOVD (%_% xmm3) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xdb;
                           (* VPBROADCASTD (%_% ymm3) (%_% xmm3) *)
  0xc4; 0xe2; 0x7d; 0x31; 0x26;
                           (* VPMOVZXBD (%_% ymm4) (Memop Quadword (%% (rsi,0))) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0c;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 12)) *)
  0xc5; 0xdd; 0xeb; 0xe5;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xdd; 0xdb; 0xe0;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xe4;
                           (* VPSHUFB (%_% ymm4) (%_% ymm2) (%_% ymm4) *)
  0xc5; 0xdd; 0xf9; 0xe3;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0x27;  (* VMOVDQU (Memop Word256 (%% (rdi,0))) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x31; 0x76; 0x08;
                           (* VPMOVZXBD (%_% ymm6) (Memop Quadword (%% (rsi,8))) *)
  0xc5; 0xc5; 0x72; 0xf6; 0x0c;
                           (* VPSLLD (%_% ymm7) (%_% ymm6) (Imm8 (word 12)) *)
  0xc5; 0xcd; 0xeb; 0xf7;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xdb; 0xf0;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xcd; 0xeb; 0xf1;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xf6;
                           (* VPSHUFB (%_% ymm6) (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xcd; 0xf9; 0xf3;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0x77; 0x20;
                           (* VMOVDQU (Memop Word256 (%% (rdi,32))) (%_% ymm6) *)
  0xc4; 0xe2; 0x7d; 0x31; 0x66; 0x10;
                           (* VPMOVZXBD (%_% ymm4) (Memop Quadword (%% (rsi,16))) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0c;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 12)) *)
  0xc5; 0xdd; 0xeb; 0xe5;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xdd; 0xdb; 0xe0;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xe4;
                           (* VPSHUFB (%_% ymm4) (%_% ymm2) (%_% ymm4) *)
  0xc5; 0xdd; 0xf9; 0xe3;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0x67; 0x40;
                           (* VMOVDQU (Memop Word256 (%% (rdi,64))) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x31; 0x76; 0x18;
                           (* VPMOVZXBD (%_% ymm6) (Memop Quadword (%% (rsi,24))) *)
  0xc5; 0xc5; 0x72; 0xf6; 0x0c;
                           (* VPSLLD (%_% ymm7) (%_% ymm6) (Imm8 (word 12)) *)
  0xc5; 0xcd; 0xeb; 0xf7;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xdb; 0xf0;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xcd; 0xeb; 0xf1;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xf6;
                           (* VPSHUFB (%_% ymm6) (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xcd; 0xf9; 0xf3;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0x77; 0x60;
                           (* VMOVDQU (Memop Word256 (%% (rdi,96))) (%_% ymm6) *)
  0xc4; 0xe2; 0x7d; 0x31; 0x66; 0x20;
                           (* VPMOVZXBD (%_% ymm4) (Memop Quadword (%% (rsi,32))) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0c;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 12)) *)
  0xc5; 0xdd; 0xeb; 0xe5;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xdd; 0xdb; 0xe0;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xe4;
                           (* VPSHUFB (%_% ymm4) (%_% ymm2) (%_% ymm4) *)
  0xc5; 0xdd; 0xf9; 0xe3;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,128))) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x31; 0x76; 0x28;
                           (* VPMOVZXBD (%_% ymm6) (Memop Quadword (%% (rsi,40))) *)
  0xc5; 0xc5; 0x72; 0xf6; 0x0c;
                           (* VPSLLD (%_% ymm7) (%_% ymm6) (Imm8 (word 12)) *)
  0xc5; 0xcd; 0xeb; 0xf7;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xdb; 0xf0;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xcd; 0xeb; 0xf1;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xf6;
                           (* VPSHUFB (%_% ymm6) (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xcd; 0xf9; 0xf3;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,160))) (%_% ymm6) *)
  0xc4; 0xe2; 0x7d; 0x31; 0x66; 0x30;
                           (* VPMOVZXBD (%_% ymm4) (Memop Quadword (%% (rsi,48))) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0c;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 12)) *)
  0xc5; 0xdd; 0xeb; 0xe5;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xdd; 0xdb; 0xe0;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xe4;
                           (* VPSHUFB (%_% ymm4) (%_% ymm2) (%_% ymm4) *)
  0xc5; 0xdd; 0xf9; 0xe3;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,192))) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x31; 0x76; 0x38;
                           (* VPMOVZXBD (%_% ymm6) (Memop Quadword (%% (rsi,56))) *)
  0xc5; 0xc5; 0x72; 0xf6; 0x0c;
                           (* VPSLLD (%_% ymm7) (%_% ymm6) (Imm8 (word 12)) *)
  0xc5; 0xcd; 0xeb; 0xf7;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xdb; 0xf0;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xcd; 0xeb; 0xf1;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xf6;
                           (* VPSHUFB (%_% ymm6) (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xcd; 0xf9; 0xf3;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,224))) (%_% ymm6) *)
  0xc4; 0xe2; 0x7d; 0x31; 0x66; 0x40;
                           (* VPMOVZXBD (%_% ymm4) (Memop Quadword (%% (rsi,64))) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0c;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 12)) *)
  0xc5; 0xdd; 0xeb; 0xe5;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xdd; 0xdb; 0xe0;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xe4;
                           (* VPSHUFB (%_% ymm4) (%_% ymm2) (%_% ymm4) *)
  0xc5; 0xdd; 0xf9; 0xe3;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,256))) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x31; 0x76; 0x48;
                           (* VPMOVZXBD (%_% ymm6) (Memop Quadword (%% (rsi,72))) *)
  0xc5; 0xc5; 0x72; 0xf6; 0x0c;
                           (* VPSLLD (%_% ymm7) (%_% ymm6) (Imm8 (word 12)) *)
  0xc5; 0xcd; 0xeb; 0xf7;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xdb; 0xf0;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xcd; 0xeb; 0xf1;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xf6;
                           (* VPSHUFB (%_% ymm6) (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xcd; 0xf9; 0xf3;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,288))) (%_% ymm6) *)
  0xc4; 0xe2; 0x7d; 0x31; 0x66; 0x50;
                           (* VPMOVZXBD (%_% ymm4) (Memop Quadword (%% (rsi,80))) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0c;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 12)) *)
  0xc5; 0xdd; 0xeb; 0xe5;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xdd; 0xdb; 0xe0;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xe4;
                           (* VPSHUFB (%_% ymm4) (%_% ymm2) (%_% ymm4) *)
  0xc5; 0xdd; 0xf9; 0xe3;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,320))) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x31; 0x76; 0x58;
                           (* VPMOVZXBD (%_% ymm6) (Memop Quadword (%% (rsi,88))) *)
  0xc5; 0xc5; 0x72; 0xf6; 0x0c;
                           (* VPSLLD (%_% ymm7) (%_% ymm6) (Imm8 (word 12)) *)
  0xc5; 0xcd; 0xeb; 0xf7;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xdb; 0xf0;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xcd; 0xeb; 0xf1;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xf6;
                           (* VPSHUFB (%_% ymm6) (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xcd; 0xf9; 0xf3;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,352))) (%_% ymm6) *)
  0xc4; 0xe2; 0x7d; 0x31; 0x66; 0x60;
                           (* VPMOVZXBD (%_% ymm4) (Memop Quadword (%% (rsi,96))) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0c;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 12)) *)
  0xc5; 0xdd; 0xeb; 0xe5;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xdd; 0xdb; 0xe0;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xe4;
                           (* VPSHUFB (%_% ymm4) (%_% ymm2) (%_% ymm4) *)
  0xc5; 0xdd; 0xf9; 0xe3;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,384))) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x31; 0x76; 0x68;
                           (* VPMOVZXBD (%_% ymm6) (Memop Quadword (%% (rsi,104))) *)
  0xc5; 0xc5; 0x72; 0xf6; 0x0c;
                           (* VPSLLD (%_% ymm7) (%_% ymm6) (Imm8 (word 12)) *)
  0xc5; 0xcd; 0xeb; 0xf7;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xdb; 0xf0;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xcd; 0xeb; 0xf1;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xf6;
                           (* VPSHUFB (%_% ymm6) (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xcd; 0xf9; 0xf3;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,416))) (%_% ymm6) *)
  0xc4; 0xe2; 0x7d; 0x31; 0x66; 0x70;
                           (* VPMOVZXBD (%_% ymm4) (Memop Quadword (%% (rsi,112))) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0c;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 12)) *)
  0xc5; 0xdd; 0xeb; 0xe5;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xdd; 0xdb; 0xe0;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xe4;
                           (* VPSHUFB (%_% ymm4) (%_% ymm2) (%_% ymm4) *)
  0xc5; 0xdd; 0xf9; 0xe3;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,448))) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x31; 0x76; 0x78;
                           (* VPMOVZXBD (%_% ymm6) (Memop Quadword (%% (rsi,120))) *)
  0xc5; 0xc5; 0x72; 0xf6; 0x0c;
                           (* VPSLLD (%_% ymm7) (%_% ymm6) (Imm8 (word 12)) *)
  0xc5; 0xcd; 0xeb; 0xf7;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xdb; 0xf0;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xcd; 0xeb; 0xf1;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xf6;
                           (* VPSHUFB (%_% ymm6) (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xcd; 0xf9; 0xf3;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,480))) (%_% ymm6) *)
  0xc5; 0xf8; 0x77;        (* VZEROUPPER *)
  0xc3                     (* RET *)
];;

let mlkem_cbd2_tmc = define_trimmed "mlkem_cbd2_tmc" mlkem_cbd2_mc;;

let MLKEM_CBD2_TMC_EXEC = X86_MK_CORE_EXEC_RULE mlkem_cbd2_tmc;;

(* ------------------------------------------------------------------------- *)
(* The coefficient of each 4-bit field as the code computes it: the lookup   *)
(* of the field in the table in ymm2 by VPSHUFB, the number of 1 bits in its *)
(* low half minus that in its high half, plus 2, and the subtraction of 2.   *)
(* ------------------------------------------------------------------------- *)

let cbd2_lookup = new_definition
 `cbd2_lookup (x:nybble) =
  word_zx (word_subword
    (word 2663668571768852569606280777117664002:int128) (8 * val x,8):byte)
  :int16`;;

let cbd2_lane = new_definition
 `cbd2_lane (x:nybble) = word_sub (cbd2_lookup x) (word 2):int16`;;

let CBD2_LANE = prove
 (`!n p. iword(&((n DIV 2 EXP p) MOD 2 + (n DIV 2 EXP (p + 1)) MOD 2) -
               &((n DIV 2 EXP (p + 2)) MOD 2 +
                 (n DIV 2 EXP (p + 3)) MOD 2)):int16 =
         cbd2_lane(word((n DIV 2 EXP p) MOD 2 EXP 4))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!t. t < 4
        ==> (n DIV 2 EXP (p + t)) MOD 2 =
            (((n DIV 2 EXP p) MOD 2 EXP 4) DIV 2 EXP t) MOD 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
    CONV_TAC SYM_CONV THEN
    MP_TAC(SPECL [`n DIV 2 EXP p`; `4`; `t:num`; `1`] DIV_MOD_EXP_LOW) THEN
    REWRITE_TAC[EXP_1] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `0`) THEN FIRST_ASSUM(MP_TAC o SPEC `1`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `2`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `3`) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; DIV_1] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ARITH_RULE `(n DIV 2 EXP p) MOD 16 < 16`) THEN
  SPEC_TAC(`(n DIV 2 EXP p) MOD 16`,`x:num`) THEN
  REWRITE_TAC[cbd2_lane; cbd2_lookup] THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)) THEN
  REWRITE_TAC[]);;

(*** The vector computed by VPSHUFB from an 8-byte block x, 16 lanes, each
 *** the lookup of a 4-bit field of x
 ***)

let CBD2_CHUNK =
  (16,16,(fun xs k -> mk_comb(`cbd2_lookup`,mk_wsubword (hd xs) (4 * k) 4)),
   LANE_BITBLAST_TAC[cbd2_lookup]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_CBD2_CORRECT = prove
 (`!r a n pc.
        ALL (nonoverlapping (r,512)) [(word pc,708); (a,128)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mlkem_cbd2_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = n)
             (\s. read RIP s = word(pc + 708) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 3)) MOD 2)))
             (MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                         ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14;
                         ZMM15] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              fst MLKEM_CBD2_TMC_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The 8-byte blocks of the input, as loaded, are subwords of word n,
   *** abbreviated as l0, ..., l15
   ***)

  MP_TAC(end_itlist CONJ (map (fun k ->
    let th = SPECL [`a:int64`; `128`; `n:num`; mk_small_numeral k;
                    `s0:x86state`] READ_MEMORY_BYTES64_OF_NUM in
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
              REWRITE_CONV[WORD_ADD_0]) th)
    (map (fun i -> 8 * i) (0--15)))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV THENC
           ONCE_DEPTH_CONV NUM_LE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INST_TYPE [`:1024`,`:N`] QWORD64_AS_SUBWORD;
           DIMINDEX_CONV `dimindex(:1024)`; ARITH] THEN
  MAP_EVERY (fun k ->
    ABBREV_TAC(mk_eq(mk_var("l"^string_of_int k,`:int64`),
                     mk_wsubword `word n:1024 word` (64 * k) 64)))
   (0--15) THEN
  STRIP_TAC THEN

  (*** Simulate, replacing each vector of lookups by its lanes, and folding
   *** the subtraction of 2 in each lane
   ***)

  MAP_EVERY (fun k ->
    X86_STEPS_TAC MLKEM_CBD2_TMC_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[cbd2_lane] THEN
    (if k >= 20 && (k - 20) mod 8 = 0 && k <= 140 then
       let c = (k - 20) / 8 in
       CHUNK_ABSTRACT_TAC CBD2_CHUNK
         (if c mod 2 = 0 then `YMM4` else `YMM6`)
         [mk_var("l"^string_of_int c,`:int64`)] k
     else ALL_TAC)) (1--143) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Each coefficient is the lane function of a 4-bit field of word n ***)

  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[CBD2_LANE] THEN
  MP_TAC(ISPECL [`n:num`; `4 * i`; `4`]
    (INST_TYPE [`:1024`,`:N`; `:4`,`:M`] WORD_SUBWORD_WORD)) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1024)`] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  UNDISCH_TAC `i < 256` THEN SPEC_TAC(`i:num`,`i:num`) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
   check (can (term_match [] `read (memory :> bytes256 a) s = xxx`) o
          concl))) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN

  (*** Expand the abbreviations of the blocks, and compare the fields ***)

  MAP_EVERY (fun k ->
    let v = mk_var("l"^string_of_int k,`:int64`) in
    FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && rhs c = v && is_comb(lhs c) &&
         fst(strip_comb(lhs c)) = `word_subword:1024 word->num#num->int64`
      then SUBST1_TAC(SYM th) else NO_TAC)) (0--15) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the IBT landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_CBD2_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a n pc stackpointer returnaddress.
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_cbd2_tmc); (a,128); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_cbd2_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 3)) MOD 2)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_cbd2_tmc MLKEM_CBD2_CORRECT);;

let MLKEM_CBD2_SUBROUTINE_CORRECT = prove
 (`!r a n pc stackpointer returnaddress.
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_cbd2_mc); (a,128); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_cbd2_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 3)) MOD 2)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_CBD2_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_cbd2" subroutine_signatures)
    MLKEM_CBD2_CORRECT
    MLKEM_CBD2_TMC_EXEC;;

let MLKEM_CBD2_SAFE = time prove
 (`exists f_events.
    forall e r a pc.
        ALL (nonoverlapping (r,512)) [word pc,708; a,128]
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) (BUTLAST mlkem_cbd2_tmc) /\
                 read RIP s = word pc /\
                 C_ARGUMENTS [r; a] s /\
                 read events s = e)
            (\s.
                 read RIP s = word (pc + 708) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events a r pc /\
                      memaccess_inbounds e2 [a,128; r,512] [r,512]))
            (MAYCHANGE [RIP] ,,
             MAYCHANGE [RAX] ,,
             MAYCHANGE
             [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9;
              ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes (r,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_CBD2_TMC_EXEC);;

let MLKEM_CBD2_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e r a pc stackpointer returnaddress.
        ALL (nonoverlapping (r,512))
            [word pc,LENGTH mlkem_cbd2_tmc; a,128; stackpointer,8]
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) mlkem_cbd2_tmc /\
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
                      [a,128; r,512; stackpointer,8]
                      [r,512; stackpointer,8]))
            (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_cbd2_tmc MLKEM_CBD2_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_CBD2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e r a pc stackpointer returnaddress.
        ALL (nonoverlapping (r,512))
            [word pc,LENGTH mlkem_cbd2_mc; a,128; stackpointer,8]
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) mlkem_cbd2_mc /\
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
                      [a,128; r,512; stackpointer,8]
                      [r,512; stackpointer,8]))
            (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_CBD2_NOIBT_SUBROUTINE_SAFE));;
