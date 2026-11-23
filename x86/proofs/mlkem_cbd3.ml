(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling from the centered binomial distribution with eta = 3.            *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "x86/proofs/utils/mlkem_bytes.ml";;
needs "x86/proofs/utils/mlkem_lanes.ml";;

(**** print_literal_from_elf "x86/mlkem/mlkem_cbd3.o";;
 ****)

let mlkem_cbd3_mc = define_assert_from_elf
  "mlkem_cbd3_mc" "x86/mlkem/mlkem_cbd3.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0xb8; 0x00; 0x01; 0x80; 0x80; 0x01; 0x02; 0x80; 0x80;
                           (* MOV (% rax) (Imm64 (word 9259403039347835136)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xc0;
                           (* VMOVQ (%_% xmm0) (% rax) *)
  0x48; 0xb8; 0x03; 0x04; 0x80; 0x80; 0x04; 0x05; 0x80; 0x80;
                           (* MOV (% rax) (Imm64 (word 9259406350767621123)) *)
  0xc4; 0xe3; 0xf9; 0x22; 0xc0; 0x01;
                           (* VPINSRQ (%_% xmm0) (%_% xmm0) (% rax) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc0; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm0) (Imm8 (word 1)) *)
  0xb8; 0x04; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 4)) *)
  0xc5; 0xf9; 0x6e; 0xc8;  (* VMOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xc5; 0xf5; 0x73; 0xf1; 0x20;
                           (* VPSLLQ (%_% ymm1) (%_% ymm1) (Imm8 (word 32)) *)
  0xb8; 0x3f; 0x00; 0x3f; 0x00;
                           (* MOV (% eax) (Imm32 (word 4128831)) *)
  0xc5; 0xf9; 0x6e; 0xd0;  (* VMOVD (%_% xmm2) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;
                           (* VPBROADCASTD (%_% ymm2) (%_% xmm2) *)
  0xb8; 0x07; 0x00; 0x07; 0x00;
                           (* MOV (% eax) (Imm32 (word 458759)) *)
  0xc5; 0xf9; 0x6e; 0xd8;  (* VMOVD (%_% xmm3) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xdb;
                           (* VPBROADCASTD (%_% ymm3) (%_% xmm3) *)
  0x48; 0xb8; 0x00; 0x01; 0x01; 0x02; 0x01; 0x02; 0x02; 0x03;
                           (* MOV (% rax) (Imm64 (word 216737935419048192)) *)
  0xc4; 0x61; 0xf9; 0x6e; 0xc0;
                           (* VMOVQ (%_% xmm8) (% rax) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 0)) *)
  0xc4; 0x63; 0xb9; 0x22; 0xc0; 0x01;
                           (* VPINSRQ (%_% xmm8) (%_% xmm8) (% rax) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x3d; 0x38; 0xc0; 0x01;
                           (* VINSERTI128 (%_% ymm8) (%_% ymm8) (%_% xmm8) (Imm8 (word 1)) *)
  0x48; 0xb8; 0x04; 0x05; 0x80; 0x80; 0x05; 0x06; 0x80; 0x80;
                           (* MOV (% rax) (Imm64 (word 9259407454574216452)) *)
  0xc4; 0x61; 0xf9; 0x6e; 0xc8;
                           (* VMOVQ (%_% xmm9) (% rax) *)
  0x48; 0xb8; 0x07; 0x08; 0x80; 0x80; 0x08; 0x09; 0x80; 0x80;
                           (* MOV (% rax) (Imm64 (word 9259410765994002439)) *)
  0xc4; 0x63; 0xb1; 0x22; 0xc8; 0x01;
                           (* VPINSRQ (%_% xmm9) (%_% xmm9) (% rax) (Imm8 (word 1)) *)
  0x48; 0xb8; 0x0a; 0x0b; 0x80; 0x80; 0x0b; 0x0c; 0x80; 0x80;
                           (* MOV (% rax) (Imm64 (word 9259414077413788426)) *)
  0xc4; 0x61; 0xf9; 0x6e; 0xd0;
                           (* VMOVQ (%_% xmm10) (% rax) *)
  0x48; 0xb8; 0x0d; 0x0e; 0x80; 0x80; 0x0e; 0x0f; 0x80; 0x80;
                           (* MOV (% rax) (Imm64 (word 9259417388833574413)) *)
  0xc4; 0x63; 0xa9; 0x22; 0xd0; 0x01;
                           (* VPINSRQ (%_% xmm10) (%_% xmm10) (% rax) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x35; 0x38; 0xca; 0x01;
                           (* VINSERTI128 (%_% ymm9) (%_% ymm9) (%_% xmm10) (Imm8 (word 1)) *)
  0xc5; 0xfa; 0x6f; 0x26;  (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,0))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0x66; 0x06; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (Memop Word128 (%% (rsi,6)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe0;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc4; 0xe2; 0x5d; 0x45; 0xe1;
                           (* VPSRLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0a;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 10)) *)
  0xc5; 0xdd; 0xeb; 0xe5;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xd5; 0x71; 0xd4; 0x03;
                           (* VPSRLW (%_% ymm5) (%_% ymm4) (Imm8 (word 3)) *)
  0xc5; 0xdd; 0xdb; 0xe3;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xe4;
                           (* VPSHUFB (%_% ymm4) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xed;
                           (* VPSHUFB (%_% ymm5) (%_% ymm8) (%_% ymm5) *)
  0xc5; 0xdd; 0xf9; 0xe5;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0x27;  (* VMOVDQU (Memop Word256 (%% (rdi,0))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0x76; 0x0c;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,12))) *)
  0xc4; 0xe3; 0x4d; 0x38; 0x76; 0x12; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (Memop Word128 (%% (rsi,18)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf0;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf1;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0xc5; 0x72; 0xf6; 0x0a;
                           (* VPSLLD (%_% ymm7) (%_% ymm6) (Imm8 (word 10)) *)
  0xc5; 0xcd; 0xeb; 0xf7;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xdb; 0xf2;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0x71; 0xd6; 0x03;
                           (* VPSRLW (%_% ymm7) (%_% ymm6) (Imm8 (word 3)) *)
  0xc5; 0xcd; 0xdb; 0xf3;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xf6;
                           (* VPSHUFB (%_% ymm6) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xff;
                           (* VPSHUFB (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc5; 0xcd; 0xf9; 0xf7;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xfe; 0x7f; 0x77; 0x20;
                           (* VMOVDQU (Memop Word256 (%% (rdi,32))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0x66; 0x18;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,24))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0x66; 0x1e; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (Memop Word128 (%% (rsi,30)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe0;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc4; 0xe2; 0x5d; 0x45; 0xe1;
                           (* VPSRLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0a;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 10)) *)
  0xc5; 0xdd; 0xeb; 0xe5;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xd5; 0x71; 0xd4; 0x03;
                           (* VPSRLW (%_% ymm5) (%_% ymm4) (Imm8 (word 3)) *)
  0xc5; 0xdd; 0xdb; 0xe3;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xe4;
                           (* VPSHUFB (%_% ymm4) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xed;
                           (* VPSHUFB (%_% ymm5) (%_% ymm8) (%_% ymm5) *)
  0xc5; 0xdd; 0xf9; 0xe5;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0x67; 0x40;
                           (* VMOVDQU (Memop Word256 (%% (rdi,64))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0x76; 0x24;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,36))) *)
  0xc4; 0xe3; 0x4d; 0x38; 0x76; 0x2a; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (Memop Word128 (%% (rsi,42)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf0;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf1;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0xc5; 0x72; 0xf6; 0x0a;
                           (* VPSLLD (%_% ymm7) (%_% ymm6) (Imm8 (word 10)) *)
  0xc5; 0xcd; 0xeb; 0xf7;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xdb; 0xf2;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0x71; 0xd6; 0x03;
                           (* VPSRLW (%_% ymm7) (%_% ymm6) (Imm8 (word 3)) *)
  0xc5; 0xcd; 0xdb; 0xf3;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xf6;
                           (* VPSHUFB (%_% ymm6) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xff;
                           (* VPSHUFB (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc5; 0xcd; 0xf9; 0xf7;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xfe; 0x7f; 0x77; 0x60;
                           (* VMOVDQU (Memop Word256 (%% (rdi,96))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0x66; 0x30;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,48))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0x66; 0x36; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (Memop Word128 (%% (rsi,54)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe0;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc4; 0xe2; 0x5d; 0x45; 0xe1;
                           (* VPSRLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0a;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 10)) *)
  0xc5; 0xdd; 0xeb; 0xe5;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xd5; 0x71; 0xd4; 0x03;
                           (* VPSRLW (%_% ymm5) (%_% ymm4) (Imm8 (word 3)) *)
  0xc5; 0xdd; 0xdb; 0xe3;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xe4;
                           (* VPSHUFB (%_% ymm4) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xed;
                           (* VPSHUFB (%_% ymm5) (%_% ymm8) (%_% ymm5) *)
  0xc5; 0xdd; 0xf9; 0xe5;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,128))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0x76; 0x3c;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,60))) *)
  0xc4; 0xe3; 0x4d; 0x38; 0x76; 0x42; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (Memop Word128 (%% (rsi,66)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf0;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf1;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0xc5; 0x72; 0xf6; 0x0a;
                           (* VPSLLD (%_% ymm7) (%_% ymm6) (Imm8 (word 10)) *)
  0xc5; 0xcd; 0xeb; 0xf7;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xdb; 0xf2;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0x71; 0xd6; 0x03;
                           (* VPSRLW (%_% ymm7) (%_% ymm6) (Imm8 (word 3)) *)
  0xc5; 0xcd; 0xdb; 0xf3;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xf6;
                           (* VPSHUFB (%_% ymm6) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xff;
                           (* VPSHUFB (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc5; 0xcd; 0xf9; 0xf7;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,160))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0x66; 0x48;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,72))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0x66; 0x4e; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (Memop Word128 (%% (rsi,78)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe0;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc4; 0xe2; 0x5d; 0x45; 0xe1;
                           (* VPSRLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0a;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 10)) *)
  0xc5; 0xdd; 0xeb; 0xe5;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xd5; 0x71; 0xd4; 0x03;
                           (* VPSRLW (%_% ymm5) (%_% ymm4) (Imm8 (word 3)) *)
  0xc5; 0xdd; 0xdb; 0xe3;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xe4;
                           (* VPSHUFB (%_% ymm4) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xed;
                           (* VPSHUFB (%_% ymm5) (%_% ymm8) (%_% ymm5) *)
  0xc5; 0xdd; 0xf9; 0xe5;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,192))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0x76; 0x54;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,84))) *)
  0xc4; 0xe3; 0x4d; 0x38; 0x76; 0x5a; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (Memop Word128 (%% (rsi,90)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf0;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf1;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0xc5; 0x72; 0xf6; 0x0a;
                           (* VPSLLD (%_% ymm7) (%_% ymm6) (Imm8 (word 10)) *)
  0xc5; 0xcd; 0xeb; 0xf7;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xdb; 0xf2;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0x71; 0xd6; 0x03;
                           (* VPSRLW (%_% ymm7) (%_% ymm6) (Imm8 (word 3)) *)
  0xc5; 0xcd; 0xdb; 0xf3;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xf6;
                           (* VPSHUFB (%_% ymm6) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xff;
                           (* VPSHUFB (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc5; 0xcd; 0xf9; 0xf7;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,224))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0x66; 0x60;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,96))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0x66; 0x66; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (Memop Word128 (%% (rsi,102)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe0;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc4; 0xe2; 0x5d; 0x45; 0xe1;
                           (* VPSRLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0a;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 10)) *)
  0xc5; 0xdd; 0xeb; 0xe5;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xd5; 0x71; 0xd4; 0x03;
                           (* VPSRLW (%_% ymm5) (%_% ymm4) (Imm8 (word 3)) *)
  0xc5; 0xdd; 0xdb; 0xe3;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xe4;
                           (* VPSHUFB (%_% ymm4) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xed;
                           (* VPSHUFB (%_% ymm5) (%_% ymm8) (%_% ymm5) *)
  0xc5; 0xdd; 0xf9; 0xe5;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,256))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0x76; 0x6c;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,108))) *)
  0xc4; 0xe3; 0x4d; 0x38; 0x76; 0x72; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (Memop Word128 (%% (rsi,114)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf0;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf1;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0xc5; 0x72; 0xf6; 0x0a;
                           (* VPSLLD (%_% ymm7) (%_% ymm6) (Imm8 (word 10)) *)
  0xc5; 0xcd; 0xeb; 0xf7;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xdb; 0xf2;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0x71; 0xd6; 0x03;
                           (* VPSRLW (%_% ymm7) (%_% ymm6) (Imm8 (word 3)) *)
  0xc5; 0xcd; 0xdb; 0xf3;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xf6;
                           (* VPSHUFB (%_% ymm6) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xff;
                           (* VPSHUFB (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc5; 0xcd; 0xf9; 0xf7;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,288))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0x66; 0x78;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,120))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0x66; 0x7e; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (Memop Word128 (%% (rsi,126)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe0;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc4; 0xe2; 0x5d; 0x45; 0xe1;
                           (* VPSRLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0a;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 10)) *)
  0xc5; 0xdd; 0xeb; 0xe5;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xd5; 0x71; 0xd4; 0x03;
                           (* VPSRLW (%_% ymm5) (%_% ymm4) (Imm8 (word 3)) *)
  0xc5; 0xdd; 0xdb; 0xe3;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xe4;
                           (* VPSHUFB (%_% ymm4) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xed;
                           (* VPSHUFB (%_% ymm5) (%_% ymm8) (%_% ymm5) *)
  0xc5; 0xdd; 0xf9; 0xe5;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,320))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0xb6; 0x84; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,132))) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xb6; 0x8a; 0x00; 0x00; 0x00; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (Memop Word128 (%% (rsi,138)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf0;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf1;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0xc5; 0x72; 0xf6; 0x0a;
                           (* VPSLLD (%_% ymm7) (%_% ymm6) (Imm8 (word 10)) *)
  0xc5; 0xcd; 0xeb; 0xf7;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xdb; 0xf2;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0x71; 0xd6; 0x03;
                           (* VPSRLW (%_% ymm7) (%_% ymm6) (Imm8 (word 3)) *)
  0xc5; 0xcd; 0xdb; 0xf3;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xf6;
                           (* VPSHUFB (%_% ymm6) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xff;
                           (* VPSHUFB (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc5; 0xcd; 0xf9; 0xf7;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,352))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0xa6; 0x90; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,144))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xa6; 0x96; 0x00; 0x00; 0x00; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (Memop Word128 (%% (rsi,150)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe0;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc4; 0xe2; 0x5d; 0x45; 0xe1;
                           (* VPSRLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0a;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 10)) *)
  0xc5; 0xdd; 0xeb; 0xe5;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xd5; 0x71; 0xd4; 0x03;
                           (* VPSRLW (%_% ymm5) (%_% ymm4) (Imm8 (word 3)) *)
  0xc5; 0xdd; 0xdb; 0xe3;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xe4;
                           (* VPSHUFB (%_% ymm4) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xed;
                           (* VPSHUFB (%_% ymm5) (%_% ymm8) (%_% ymm5) *)
  0xc5; 0xdd; 0xf9; 0xe5;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,384))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0xb6; 0x9c; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,156))) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xb6; 0xa2; 0x00; 0x00; 0x00; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (Memop Word128 (%% (rsi,162)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf0;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf1;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0xc5; 0x72; 0xf6; 0x0a;
                           (* VPSLLD (%_% ymm7) (%_% ymm6) (Imm8 (word 10)) *)
  0xc5; 0xcd; 0xeb; 0xf7;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xdb; 0xf2;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0x71; 0xd6; 0x03;
                           (* VPSRLW (%_% ymm7) (%_% ymm6) (Imm8 (word 3)) *)
  0xc5; 0xcd; 0xdb; 0xf3;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xf6;
                           (* VPSHUFB (%_% ymm6) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xff;
                           (* VPSHUFB (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc5; 0xcd; 0xf9; 0xf7;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,416))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0xa6; 0xa8; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,168))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xa6; 0xae; 0x00; 0x00; 0x00; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (Memop Word128 (%% (rsi,174)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe0;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc4; 0xe2; 0x5d; 0x45; 0xe1;
                           (* VPSRLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xd5; 0x72; 0xf4; 0x0a;
                           (* VPSLLD (%_% ymm5) (%_% ymm4) (Imm8 (word 10)) *)
  0xc5; 0xdd; 0xeb; 0xe5;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xd5; 0x71; 0xd4; 0x03;
                           (* VPSRLW (%_% ymm5) (%_% ymm4) (Imm8 (word 3)) *)
  0xc5; 0xdd; 0xdb; 0xe3;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xe4;
                           (* VPSHUFB (%_% ymm4) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xed;
                           (* VPSHUFB (%_% ymm5) (%_% ymm8) (%_% ymm5) *)
  0xc5; 0xdd; 0xf9; 0xe5;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,448))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0xb6; 0xb0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,176))) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf6; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm6) (Imm8 (word 1)) *)
  0xc4; 0xc2; 0x4d; 0x00; 0xf1;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm9) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf1;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0xc5; 0x72; 0xf6; 0x0a;
                           (* VPSLLD (%_% ymm7) (%_% ymm6) (Imm8 (word 10)) *)
  0xc5; 0xcd; 0xeb; 0xf7;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xdb; 0xf2;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0x71; 0xd6; 0x03;
                           (* VPSRLW (%_% ymm7) (%_% ymm6) (Imm8 (word 3)) *)
  0xc5; 0xcd; 0xdb; 0xf3;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xf6;
                           (* VPSHUFB (%_% ymm6) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xe2; 0x3d; 0x00; 0xff;
                           (* VPSHUFB (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc5; 0xcd; 0xf9; 0xf7;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,480))) (%_% ymm6) *)
  0xc5; 0xf8; 0x77;        (* VZEROUPPER *)
  0xc3                     (* RET *)
];;

let mlkem_cbd3_tmc = define_trimmed "mlkem_cbd3_tmc" mlkem_cbd3_mc;;

let MLKEM_CBD3_TMC_EXEC = X86_MK_CORE_EXEC_RULE mlkem_cbd3_tmc;;

(* ------------------------------------------------------------------------- *)
(* The coefficient of each 6-bit field as the code computes it: the numbers  *)
(* of 1 bits in its low and high halves, each looked up in the table in ymm8 *)
(* by VPSHUFB, and their difference.                                         *)
(* ------------------------------------------------------------------------- *)

let cbd3_lookup = new_definition
 `cbd3_lookup (x:nybble) =
  word_zx (word_subword (word 0x0302020102010100:int128) (8 * val x,8):byte)
  :int16`;;

let cbd3_lane = new_definition
 `cbd3_lane (y:6 word) =
  word_sub (cbd3_lookup (word_zx (word_subword y (0,3):3 word)))
           (cbd3_lookup (word_zx (word_subword y (3,3):3 word)))`;;

let CBD3_LANE = prove
 (`!n p. iword(&((n DIV 2 EXP p) MOD 2 + (n DIV 2 EXP (p + 1)) MOD 2 +
                 (n DIV 2 EXP (p + 2)) MOD 2) -
               &((n DIV 2 EXP (p + 3)) MOD 2 + (n DIV 2 EXP (p + 4)) MOD 2 +
                 (n DIV 2 EXP (p + 5)) MOD 2)):int16 =
         cbd3_lane(word((n DIV 2 EXP p) MOD 2 EXP 6))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!t. t < 6
        ==> (n DIV 2 EXP (p + t)) MOD 2 =
            (((n DIV 2 EXP p) MOD 2 EXP 6) DIV 2 EXP t) MOD 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
    CONV_TAC SYM_CONV THEN
    MP_TAC(SPECL [`n DIV 2 EXP p`; `6`; `t:num`; `1`] DIV_MOD_EXP_LOW) THEN
    REWRITE_TAC[EXP_1] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(MP_TAC o SPEC(mk_small_numeral t)))
   (0--5) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; DIV_1] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ARITH_RULE `(n DIV 2 EXP p) MOD 64 < 64`) THEN
  SPEC_TAC(`(n DIV 2 EXP p) MOD 64`,`x:num`) THEN
  REWRITE_TAC[cbd3_lane; cbd3_lookup] THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)) THEN
  REWRITE_TAC[]);;

(*** The vectors of lookups of the low and high halves of the fields, from
 *** the two 16-byte loads x0 and x1 of a block of 12 bytes (the fields of
 *** lanes 0..7 in bits 0..47 of x0, those of lanes 8..15 in bits 0..47 of
 *** x1), or for the last block from the one load x0 (all in bits 32..127)
 ***)

let cbd3_field xs k h =
  match xs with
    [x0;x1] -> if k < 8 then mk_wsubword x0 (6 * k + h) 3
               else mk_wsubword x1 (6 * (k - 8) + h) 3
  | [x0] -> mk_wsubword x0 (32 + 6 * k + h) 3
  | _ -> failwith "cbd3_field";;

let cbd3_lookup_lane h xs k =
  mk_comb(`cbd3_lookup`,
          mk_comb(`word_zx:3 word->nybble`,cbd3_field xs k h));;

let CBD3_CHUNK_LO =
  (16,16,cbd3_lookup_lane 0,LANE_BITBLAST_TAC[cbd3_lookup]);;
let CBD3_CHUNK_HI =
  (16,16,cbd3_lookup_lane 3,LANE_BITBLAST_TAC[cbd3_lookup]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_CBD3_CORRECT = prove
 (`!r a n pc.
        ALL (nonoverlapping (r,512)) [(word pc,1260); (a,192)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mlkem_cbd3_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,192)) s = n)
             (\s. read RIP s = word(pc + 1260) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 5)) MOD 2)))
             (MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                         ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14;
                         ZMM15] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  let offs = flat(map (fun c -> [12 * c; 12 * c + 6]) (0--14)) @ [176] in
  let lname k = "l"^string_of_int k in
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              fst MLKEM_CBD3_TMC_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The 16-byte loads of the input are subwords of word n, abbreviated
   *** as l0, ..., l30
   ***)

  MP_TAC(end_itlist CONJ (map (fun k ->
    let th = SPECL [`a:int64`; `192`; `n:num`; mk_small_numeral k;
                    `s0:x86state`] READ_MEMORY_BYTES128_OF_NUM in
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
              REWRITE_CONV[WORD_ADD_0]) th) offs)) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV THENC
           ONCE_DEPTH_CONV NUM_LE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INST_TYPE [`:1536`,`:N`] QWORD128_AS_SUBWORD;
           DIMINDEX_CONV `dimindex(:1536)`; ARITH] THEN
  MAP_EVERY (fun (k,off) ->
    ABBREV_TAC(mk_eq(mk_var(lname k,`:int128`),
                     mk_wsubword `word n:1536 word` (8 * off) 128)))
   (zip (0--30) offs) THEN
  STRIP_TAC THEN

  (*** Simulate, replacing each vector of lookups by its lanes ***)

  MAP_EVERY (fun k ->
    X86_STEPS_TAC MLKEM_CBD3_TMC_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[] THEN
    (if k >= 39 && k <= 235 && ((k - 39) mod 13 = 0 || (k - 40) mod 13 = 0)
     then
       let c = if (k - 39) mod 13 = 0 then (k - 39) / 13 else (k - 40) / 13
       and hi = (k - 40) mod 13 = 0 in
       let reg = if c mod 2 = 0 then (if hi then `YMM5` else `YMM4`)
                 else (if hi then `YMM7` else `YMM6`) in
       let vs = if c < 15
                then [mk_var(lname(2 * c),`:int128`);
                      mk_var(lname(2 * c + 1),`:int128`)]
                else [mk_var(lname 30,`:int128`)] in
       CHUNK_ABSTRACT_TAC (if hi then CBD3_CHUNK_HI else CBD3_CHUNK_LO)
         reg vs k
     else ALL_TAC)) (1--238) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Each coefficient is the lane function of a 6-bit field of word n ***)

  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[CBD3_LANE] THEN
  MP_TAC(ISPECL [`n:num`; `6 * i`; `6`]
    (INST_TYPE [`:1536`,`:N`; `:6`,`:M`] WORD_SUBWORD_WORD)) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1536)`] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[cbd3_lane] THEN
  UNDISCH_TAC `i < 256` THEN SPEC_TAC(`i:num`,`i:num`) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
   check (can (term_match [] `read (memory :> bytes256 a) s = xxx`) o
          concl))) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN

  (*** Expand the abbreviations of the loads, and compare the fields ***)

  MAP_EVERY (fun k ->
    let v = mk_var(lname k,`:int128`) in
    FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && rhs c = v && is_comb(lhs c) &&
         fst(strip_comb(lhs c)) = `word_subword:1536 word->num#num->int128`
      then SUBST1_TAC(SYM th) else NO_TAC)) (0--30) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the IBT landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_CBD3_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a n pc stackpointer returnaddress.
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_cbd3_tmc); (a,192); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_cbd3_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,192)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 5)) MOD 2)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_cbd3_tmc MLKEM_CBD3_CORRECT);;

let MLKEM_CBD3_SUBROUTINE_CORRECT = prove
 (`!r a n pc stackpointer returnaddress.
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_cbd3_mc); (a,192); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_cbd3_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,192)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 5)) MOD 2)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_CBD3_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_cbd3" subroutine_signatures)
    MLKEM_CBD3_CORRECT
    MLKEM_CBD3_TMC_EXEC;;

let MLKEM_CBD3_SAFE = time prove
 (`exists f_events.
    forall e r a pc.
        ALL (nonoverlapping (r,512)) [word pc,1260; a,192]
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) (BUTLAST mlkem_cbd3_tmc) /\
                 read RIP s = word pc /\
                 C_ARGUMENTS [r; a] s /\
                 read events s = e)
            (\s.
                 read RIP s = word (pc + 1260) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events a r pc /\
                      memaccess_inbounds e2 [a,192; r,512] [r,512]))
            (MAYCHANGE [RIP] ,,
             MAYCHANGE [RAX] ,,
             MAYCHANGE
             [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9;
              ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes (r,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_CBD3_TMC_EXEC);;

let MLKEM_CBD3_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e r a pc stackpointer returnaddress.
        ALL (nonoverlapping (r,512))
            [word pc,LENGTH mlkem_cbd3_tmc; a,192; stackpointer,8]
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) mlkem_cbd3_tmc /\
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
                      [a,192; r,512; stackpointer,8]
                      [r,512; stackpointer,8]))
            (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_cbd3_tmc MLKEM_CBD3_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_CBD3_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e r a pc stackpointer returnaddress.
        ALL (nonoverlapping (r,512))
            [word pc,LENGTH mlkem_cbd3_mc; a,192; stackpointer,8]
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) mlkem_cbd3_mc /\
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
                      [a,192; r,512; stackpointer,8]
                      [r,512; stackpointer,8]))
            (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_CBD3_NOIBT_SUBROUTINE_SAFE));;
