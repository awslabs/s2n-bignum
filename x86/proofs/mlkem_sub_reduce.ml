(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Subtraction of polynomials and reduction of the coefficients.             *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "x86/mlkem/mlkem_sub_reduce.o";;
 ****)

let mlkem_sub_reduce_mc = define_assert_from_elf
  "mlkem_sub_reduce_mc" "x86/mlkem/mlkem_sub_reduce.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x01; 0x0d; 0x01; 0x0d;
                           (* MOV (% eax) (Imm32 (word 218172673)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0xbf; 0x4e; 0xbf; 0x4e;
                           (* MOV (% eax) (Imm32 (word 1321160383)) *)
  0xc5; 0xf9; 0x6e; 0xc8;  (* VMOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xc5; 0xfe; 0x6f; 0x17;  (* VMOVDQU (%_% ymm2) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfe; 0x6f; 0x5f; 0x20;
                           (* VMOVDQU (%_% ymm3) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfe; 0x6f; 0x67; 0x40;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfe; 0x6f; 0x6f; 0x60;
                           (* VMOVDQU (%_% ymm5) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0xfe; 0x6f; 0xb7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm6) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0xfe; 0x6f; 0xbf; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm7) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0x7e; 0x6f; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm8) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0x7e; 0x6f; 0x8f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm9) (Memop Word256 (%% (rdi,224))) *)
  0xc5; 0xed; 0xf9; 0x16;  (* VPSUBW (%_% ymm2) (%_% ymm2) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0xe5; 0xf9; 0x5e; 0x20;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0xdd; 0xf9; 0x66; 0x40;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (Memop Word256 (%% (rsi,64))) *)
  0xc5; 0xd5; 0xf9; 0x6e; 0x60;
                           (* VPSUBW (%_% ymm5) (%_% ymm5) (Memop Word256 (%% (rsi,96))) *)
  0xc5; 0xcd; 0xf9; 0xb6; 0x80; 0x00; 0x00; 0x00;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (Memop Word256 (%% (rsi,128))) *)
  0xc5; 0xc5; 0xf9; 0xbe; 0xa0; 0x00; 0x00; 0x00;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (Memop Word256 (%% (rsi,160))) *)
  0xc5; 0x3d; 0xf9; 0x86; 0xc0; 0x00; 0x00; 0x00;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (Memop Word256 (%% (rsi,192))) *)
  0xc5; 0x35; 0xf9; 0x8e; 0xe0; 0x00; 0x00; 0x00;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (Memop Word256 (%% (rsi,224))) *)
  0xc5; 0x6d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm2) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x6d; 0xf9; 0xd4;
                           (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm12) *)
  0xc5; 0x65; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm3) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x65; 0xf9; 0xdc;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0x5d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm4) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xf9; 0xe4;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x55; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x55; 0xf9; 0xec;
                           (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0x4d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x4d; 0xf9; 0xf4;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x45; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xfc;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x3d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc4;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc5; 0x35; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xcc;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0xed; 0xf9; 0xd0;  (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe2; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x9d; 0xfd; 0xd2;  (* VPADDW (%_% ymm2) (%_% ymm12) (%_% ymm2) *)
  0xc5; 0xe5; 0xf9; 0xd8;  (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe3; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm3) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x9d; 0xfd; 0xdb;  (* VPADDW (%_% ymm3) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0xdd; 0xf9; 0xe0;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe4; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x9d; 0xfd; 0xe4;  (* VPADDW (%_% ymm4) (%_% ymm12) (%_% ymm4) *)
  0xc5; 0xd5; 0xf9; 0xe8;  (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe5; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm5) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x9d; 0xfd; 0xed;  (* VPADDW (%_% ymm5) (%_% ymm12) (%_% ymm5) *)
  0xc5; 0xcd; 0xf9; 0xf0;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe6; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm6) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x9d; 0xfd; 0xf6;  (* VPADDW (%_% ymm6) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0xc5; 0xf9; 0xf8;  (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe7; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm7) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x9d; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm12) (%_% ymm7) *)
  0xc5; 0x3d; 0xf9; 0xc0;  (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe0; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm8) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xfd; 0xc4;
                           (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc5; 0x35; 0xf9; 0xc8;  (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe1; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm9) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xfd; 0xcc;
                           (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0xfe; 0x7f; 0x17;  (* VMOVDQU (Memop Word256 (%% (rdi,0))) (%_% ymm2) *)
  0xc5; 0xfe; 0x7f; 0x5f; 0x20;
                           (* VMOVDQU (Memop Word256 (%% (rdi,32))) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0x67; 0x40;
                           (* VMOVDQU (Memop Word256 (%% (rdi,64))) (%_% ymm4) *)
  0xc5; 0xfe; 0x7f; 0x6f; 0x60;
                           (* VMOVDQU (Memop Word256 (%% (rdi,96))) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,128))) (%_% ymm6) *)
  0xc5; 0xfe; 0x7f; 0xbf; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,160))) (%_% ymm7) *)
  0xc5; 0x7e; 0x7f; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,192))) (%_% ymm8) *)
  0xc5; 0x7e; 0x7f; 0x8f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,224))) (%_% ymm9) *)
  0xc5; 0xfe; 0x6f; 0x97; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm2) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0xfe; 0x6f; 0x9f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm3) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0xfe; 0x6f; 0xa7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0xfe; 0x6f; 0xaf; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm5) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0xfe; 0x6f; 0xb7; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm6) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0xfe; 0x6f; 0xbf; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm7) (Memop Word256 (%% (rdi,416))) *)
  0xc5; 0x7e; 0x6f; 0x87; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm8) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0x7e; 0x6f; 0x8f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm9) (Memop Word256 (%% (rdi,480))) *)
  0xc5; 0xed; 0xf9; 0x96; 0x00; 0x01; 0x00; 0x00;
                           (* VPSUBW (%_% ymm2) (%_% ymm2) (Memop Word256 (%% (rsi,256))) *)
  0xc5; 0xe5; 0xf9; 0x9e; 0x20; 0x01; 0x00; 0x00;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (Memop Word256 (%% (rsi,288))) *)
  0xc5; 0xdd; 0xf9; 0xa6; 0x40; 0x01; 0x00; 0x00;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (Memop Word256 (%% (rsi,320))) *)
  0xc5; 0xd5; 0xf9; 0xae; 0x60; 0x01; 0x00; 0x00;
                           (* VPSUBW (%_% ymm5) (%_% ymm5) (Memop Word256 (%% (rsi,352))) *)
  0xc5; 0xcd; 0xf9; 0xb6; 0x80; 0x01; 0x00; 0x00;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (Memop Word256 (%% (rsi,384))) *)
  0xc5; 0xc5; 0xf9; 0xbe; 0xa0; 0x01; 0x00; 0x00;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (Memop Word256 (%% (rsi,416))) *)
  0xc5; 0x3d; 0xf9; 0x86; 0xc0; 0x01; 0x00; 0x00;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (Memop Word256 (%% (rsi,448))) *)
  0xc5; 0x35; 0xf9; 0x8e; 0xe0; 0x01; 0x00; 0x00;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (Memop Word256 (%% (rsi,480))) *)
  0xc5; 0x6d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm2) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x6d; 0xf9; 0xd4;
                           (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm12) *)
  0xc5; 0x65; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm3) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x65; 0xf9; 0xdc;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0x5d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm4) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xf9; 0xe4;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x55; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x55; 0xf9; 0xec;
                           (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0x4d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x4d; 0xf9; 0xf4;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x45; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xfc;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x3d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc4;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc5; 0x35; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xcc;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0xed; 0xf9; 0xd0;  (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe2; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x9d; 0xfd; 0xd2;  (* VPADDW (%_% ymm2) (%_% ymm12) (%_% ymm2) *)
  0xc5; 0xe5; 0xf9; 0xd8;  (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe3; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm3) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x9d; 0xfd; 0xdb;  (* VPADDW (%_% ymm3) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0xdd; 0xf9; 0xe0;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe4; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x9d; 0xfd; 0xe4;  (* VPADDW (%_% ymm4) (%_% ymm12) (%_% ymm4) *)
  0xc5; 0xd5; 0xf9; 0xe8;  (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe5; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm5) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x9d; 0xfd; 0xed;  (* VPADDW (%_% ymm5) (%_% ymm12) (%_% ymm5) *)
  0xc5; 0xcd; 0xf9; 0xf0;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe6; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm6) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x9d; 0xfd; 0xf6;  (* VPADDW (%_% ymm6) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0xc5; 0xf9; 0xf8;  (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe7; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm7) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x9d; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm12) (%_% ymm7) *)
  0xc5; 0x3d; 0xf9; 0xc0;  (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe0; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm8) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xfd; 0xc4;
                           (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc5; 0x35; 0xf9; 0xc8;  (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe1; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm9) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xfd; 0xcc;
                           (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0xfe; 0x7f; 0x97; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,256))) (%_% ymm2) *)
  0xc5; 0xfe; 0x7f; 0x9f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,288))) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,320))) (%_% ymm4) *)
  0xc5; 0xfe; 0x7f; 0xaf; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,352))) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,384))) (%_% ymm6) *)
  0xc5; 0xfe; 0x7f; 0xbf; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,416))) (%_% ymm7) *)
  0xc5; 0x7e; 0x7f; 0x87; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,448))) (%_% ymm8) *)
  0xc5; 0x7e; 0x7f; 0x8f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,480))) (%_% ymm9) *)
  0xc5; 0xf8; 0x77;        (* VZEROUPPER *)
  0xc3                     (* RET *)
];;

let mlkem_sub_reduce_tmc =
  define_trimmed "mlkem_sub_reduce_tmc" mlkem_sub_reduce_mc;;

let MLKEM_SUB_REDUCE_TMC_EXEC =
  X86_MK_CORE_EXEC_RULE mlkem_sub_reduce_tmc;;

(* ------------------------------------------------------------------------- *)
(* The reduction of each lane is that of mlkem_reduce: the Barrett reduction *)
(* barred_x86 and the conditional addition of 3329, whose operands are in    *)
(* either order in the code (for the shorter VEX encoding where it has one). *)
(* ------------------------------------------------------------------------- *)

let MLKEM_SUB_REDUCE_REM = prove
 (`(y == x) (mod &3329) /\
   &0 <= y /\ y <= &6657
   ==> x rem &3329 = if y >= &3329 then y - &3329 else y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_REM_UNIQUE] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN
  UNDISCH_TAC `(y:int == x) (mod &3329)` THEN
  SPEC_TAC(`&3329:int`,`p:int`) THEN CONV_TAC INTEGER_RULE);;

let MLKEM_SUB_REDUCE_LANE =
  let th = prove
   (`!x:int16.
        ival(word_add (word_sub (barred_x86 x) (word 3329))
                      (word_and (word_ishr
                                  (word_sub (barred_x86 x) (word 3329)) 15)
                                (word 3329))) =
        ival x rem &3329`,
    REWRITE_TAC[MATCH_MP MLKEM_SUB_REDUCE_REM
                 (CONGBOUND_RULE `barred_x86 x`)] THEN
    GEN_TAC THEN MP_TAC(CONGBOUND_RULE `barred_x86 x`) THEN
    BITBLAST_TAC) in
  let th' = GEN_ALL(REWRITE_RULE[IWORD_IVAL]
              (AP_TERM `iword:int->int16` (SPEC_ALL th))) in
  CONJ th' (ONCE_REWRITE_RULE[WORD_ADD_SYM] th');;

let MLKEM_SUB_REDUCE_IVAL = prove
 (`!x:int16. ival(iword(ival x rem &3329):int16) = ival x rem &3329`,
  GEN_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_16; ARITH] THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(*** As in mlkem_reduce, simplify subwords in the simulation, so that the
 *** terms do not explode (restored at the end of the file)
 ***)

let mlkem_sub_reduce_extra_word_conv = !extra_word_CONV;;
extra_word_CONV := [WORD_SIMPLE_SUBWORD_CONV] @ !extra_word_CONV;;

let MLKEM_SUB_REDUCE_CORRECT = prove
 (`!r a x y pc.
        ALL (nonoverlapping (word pc,960)) [(r,512); (a,512)] /\
        nonoverlapping (r,512) (a,512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mlkem_sub_reduce_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                 (word_add r (word(2 * i)))) s =
                           x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s =
                           y i))
             (\s. read RIP s = word(pc + 960) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add r (word(2 * i)))) s) =
                          ival(word_sub (x i) (y i)) rem &3329)
             (MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                         ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14;
                         ZMM15] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `y:num->int16`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; ALL; fst MLKEM_SUB_REDUCE_TMC_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Manually expand the cases in the hypotheses ***)

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN

  ENSURES_INIT_TAC "s0" THEN

  (*** Restructure to match the 256-bit loads ***)

  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 4
            (subst[mk_small_numeral(32*n),`n:num`]
                  `read (memory :> bytes256(word_add r (word n))) s0`))
            (0--15))) THEN
  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 4
            (subst[mk_small_numeral(32*n),`n:num`]
                  `read (memory :> bytes256(word_add a (word n))) s0`))
            (0--15))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  REPEAT STRIP_TAC THEN

  (*** Simulate the whole thing ***)

  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_SUB_REDUCE_TMC_EXEC [n] THEN
                      RULE_ASSUM_TAC(CONV_RULE(SIMD_SIMPLIFY_CONV
                                                 [barred_x86])))
            (1--183) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Split the 256-bit results into 16-bit coefficients ***)

  RULE_ASSUM_TAC(REWRITE_RULE[GSYM barred_x86]) THEN
  RULE_ASSUM_TAC(CONV_RULE(SIMD_SIMPLIFY_CONV[])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLKEM_SUB_REDUCE_LANE]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
   check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN
  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s183" THEN
  REWRITE_TAC[GSYM barred_x86; MLKEM_SUB_REDUCE_LANE] THEN
  REWRITE_TAC[MLKEM_SUB_REDUCE_IVAL]);;

extra_word_CONV := mlkem_sub_reduce_extra_word_conv;;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the IBT landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_SUB_REDUCE_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a x y pc stackpointer returnaddress.
        ALL (nonoverlapping (word pc,LENGTH mlkem_sub_reduce_tmc))
            [(r,512); (a,512)] /\
        nonoverlapping (r,512) (a,512) /\
        nonoverlapping (stackpointer,8) (r,512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_sub_reduce_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                 (word_add r (word(2 * i)))) s =
                           x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s =
                           y i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add r (word(2 * i)))) s) =
                          ival(word_sub (x i) (y i)) rem &3329)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_sub_reduce_tmc
    MLKEM_SUB_REDUCE_CORRECT);;

let MLKEM_SUB_REDUCE_SUBROUTINE_CORRECT = prove
 (`!r a x y pc stackpointer returnaddress.
        ALL (nonoverlapping (word pc,LENGTH mlkem_sub_reduce_mc))
            [(r,512); (a,512)] /\
        nonoverlapping (r,512) (a,512) /\
        nonoverlapping (stackpointer,8) (r,512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_sub_reduce_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                 (word_add r (word(2 * i)))) s =
                           x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s =
                           y i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add r (word(2 * i)))) s) =
                          ival(word_sub (x i) (y i)) rem &3329)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_SUB_REDUCE_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_sub_reduce" subroutine_signatures)
    MLKEM_SUB_REDUCE_CORRECT
    MLKEM_SUB_REDUCE_TMC_EXEC;;

let MLKEM_SUB_REDUCE_SAFE = time prove
 (`exists f_events.
    forall e r a pc.
        ALL (nonoverlapping (word pc,960)) [r,512; a,512] /\
        nonoverlapping (r,512) (a,512)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) (BUTLAST mlkem_sub_reduce_tmc) /\
                 read RIP s = word pc /\
                 C_ARGUMENTS [r; a] s /\
                 read events s = e)
            (\s.
                 read RIP s = word (pc + 960) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events a r pc /\
                      memaccess_inbounds e2 [r,512; a,512] [r,512]))
            (MAYCHANGE [RIP] ,,
             MAYCHANGE [RAX] ,,
             MAYCHANGE
             [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9;
              ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes (r,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_SUB_REDUCE_TMC_EXEC);;

let MLKEM_SUB_REDUCE_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e r a pc stackpointer returnaddress.
        ALL (nonoverlapping (word pc,LENGTH mlkem_sub_reduce_tmc))
            [r,512; a,512] /\
        nonoverlapping (r,512) (a,512) /\
           nonoverlapping (stackpointer,8) (r,512)
           ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) mlkem_sub_reduce_tmc /\
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
                      [r,512; a,512; stackpointer,8]
                      [r,512; stackpointer,8]))
            (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_sub_reduce_tmc
    MLKEM_SUB_REDUCE_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_SUB_REDUCE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e r a pc stackpointer returnaddress.
        ALL (nonoverlapping (word pc,LENGTH mlkem_sub_reduce_mc))
            [r,512; a,512] /\
        nonoverlapping (r,512) (a,512) /\
           nonoverlapping (stackpointer,8) (r,512)
           ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) mlkem_sub_reduce_mc /\
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
                      [r,512; a,512; stackpointer,8]
                      [r,512; stackpointer,8]))
            (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_SUB_REDUCE_NOIBT_SUBROUTINE_SAFE));;
