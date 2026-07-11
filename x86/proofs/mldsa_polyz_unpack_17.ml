(*
 * Copyright (c) The mldsa-native project authors
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Functional correctness of polyz_unpack_17 (x86_64 AVX2):                  *)
(* Unpack polynomial z with 18-bit packed coefficients (GAMMA1 = 2^17)       *)
(* Maps packed [0, 2^18-1] to signed [-(2^17-1), 2^17] via GAMMA1 - x        *)
(* (ML-DSA-44).                                                              *)
(*                                                                           *)
(* The x86 routine builds the shuffle/shift/mask/gamma1 constants inline     *)
(* (VMOVQ/VPINSRQ/VINSERTI128/VPBROADCASTD) and unpacks 8 coefficients per   *)
(* block with VPSHUFB/VPSRLVD/VPAND/VPSUBD.                                  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "x86/mldsa/mldsa_polyz_unpack_17.o";;
 ****)

let mldsa_polyz_unpack_17_mc = define_assert_from_elf
  "mldsa_polyz_unpack_17_mc" "x86/mldsa/mldsa_polyz_unpack_17.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0xb8; 0x00; 0x01; 0x02; 0xff; 0x02; 0x03; 0x04; 0xff;
                           (* MOV (% rax) (Imm64 (word 18375815690981605632)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xc8;
                           (* VMOVQ (%_% xmm1) (% rax) *)
  0x48; 0xb8; 0x04; 0x05; 0x06; 0xff; 0x06; 0x07; 0x08; 0xff;
                           (* MOV (% rax) (Imm64 (word 18376946006115091716)) *)
  0xc4; 0xe3; 0xf1; 0x22; 0xc8; 0x01;
                           (* VPINSRQ (%_% xmm1) (%_% xmm1) (% rax) (Imm8 (word 1)) *)
  0x48; 0xb8; 0x17; 0x18; 0x19; 0xff; 0x19; 0x1a; 0x1b; 0xff;
                           (* MOV (% rax) (Imm64 (word 18382315002999150615)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xe8;
                           (* VMOVQ (%_% xmm5) (% rax) *)
  0x48; 0xb8; 0x1b; 0x1c; 0x1d; 0xff; 0x1d; 0x1e; 0x1f; 0xff;
                           (* MOV (% rax) (Imm64 (word 18383445318132636699)) *)
  0xc4; 0xe3; 0xd1; 0x22; 0xe8; 0x01;
                           (* VPINSRQ (%_% xmm5) (%_% xmm5) (% rax) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x75; 0x38; 0xcd; 0x01;
                           (* VINSERTI128 (%_% ymm1) (%_% ymm1) (%_% xmm5) (Imm8 (word 1)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 8589934592)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xd0;
                           (* VMOVQ (%_% xmm2) (% rax) *)
  0x48; 0xb8; 0x04; 0x00; 0x00; 0x00; 0x06; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 25769803780)) *)
  0xc4; 0xe3; 0xe9; 0x22; 0xd0; 0x01;
                           (* VPINSRQ (%_% xmm2) (%_% xmm2) (% rax) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x6d; 0x38; 0xd2; 0x01;
                           (* VINSERTI128 (%_% ymm2) (%_% ymm2) (%_% xmm2) (Imm8 (word 1)) *)
  0xb8; 0xff; 0xff; 0x03; 0x00;
                           (* MOV (% eax) (Imm32 (word 262143)) *)
  0xc5; 0xf9; 0x6e; 0xd8;  (* VMOVD (%_% xmm3) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xdb;
                           (* VPBROADCASTD (%_% ymm3) (%_% xmm3) *)
  0xb8; 0x00; 0x00; 0x02; 0x00;
                           (* MOV (% eax) (Imm32 (word 131072)) *)
  0xc5; 0xf9; 0x6e; 0xe0;  (* VMOVD (%_% xmm4) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xe4;
                           (* VPBROADCASTD (%_% ymm4) (%_% xmm4) *)
  0xc5; 0xfa; 0x6f; 0x06;  (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,0))) *)
  0xc5; 0xfa; 0x6f; 0x6e; 0x02;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,2))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x07;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x46; 0x12;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,18))) *)
  0xc5; 0xfa; 0x6f; 0x6e; 0x14;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,20))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x47; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x46; 0x24;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,36))) *)
  0xc5; 0xfa; 0x6f; 0x6e; 0x26;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,38))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x47; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x46; 0x36;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,54))) *)
  0xc5; 0xfa; 0x6f; 0x6e; 0x38;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,56))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x47; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x46; 0x48;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,72))) *)
  0xc5; 0xfa; 0x6f; 0x6e; 0x4a;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,74))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x46; 0x5a;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,90))) *)
  0xc5; 0xfa; 0x6f; 0x6e; 0x5c;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,92))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x46; 0x6c;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,108))) *)
  0xc5; 0xfa; 0x6f; 0x6e; 0x6e;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,110))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x46; 0x7e;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,126))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,128))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0x90; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,144))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x92; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,146))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0xa2; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,162))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xa4; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,164))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0xb4; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,180))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xb6; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,182))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0xc6; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,198))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xc8; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,200))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0xd8; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,216))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xda; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,218))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0xea; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,234))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xec; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,236))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0xfc; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,252))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xfe; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,254))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0x0e; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,270))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x10; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,272))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,288))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x22; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,290))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,512))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0x32; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,306))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x34; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,308))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,544))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0x44; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,324))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x46; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,326))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,576))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0x56; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,342))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x58; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,344))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,608))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0x68; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,360))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x6a; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,362))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,640))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0x7a; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,378))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x7c; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,380))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,672))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0x8c; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,396))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x8e; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,398))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,704))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0x9e; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,414))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,416))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,736))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0xb0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,432))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xb2; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,434))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,768))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0xc2; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,450))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xc4; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,452))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,800))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0xd4; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,468))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xd6; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,470))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,832))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0xe6; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,486))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xe8; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,488))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,864))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0xf8; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,504))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xfa; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,506))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,896))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0x0a; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,522))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x0c; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,524))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,928))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0x1c; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,540))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x1e; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,542))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,960))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0x2e; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,558))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x30; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,560))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x87; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,992))) (%_% ymm0) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let mldsa_polyz_unpack_17_tmc =
  define_trimmed "mldsa_polyz_unpack_17_tmc" mldsa_polyz_unpack_17_mc;;

let MLDSA_POLYZ_UNPACK_17_EXEC = X86_MK_CORE_EXEC_RULE mldsa_polyz_unpack_17_tmc;;

(* ------------------------------------------------------------------------- *)
(* Coefficient (un)packing helpers shared across the polyz_unpack proofs.    *)
(* ------------------------------------------------------------------------- *)

(* Split ncoeffs d-bit coefficients into chunks of chunk_size. *)
let mk_split_theorem d ncoeffs chunk_size =
  let total = d * chunk_size in
  let nchunks = ncoeffs / chunk_size in
  let d_ty = mk_finty (Num.num_of_int d) in
  let total_ty = mk_finty (Num.num_of_int total) in
  prove(
    subst [mk_small_numeral ncoeffs, `ncoeffs:num`;
           mk_small_numeral chunk_size, `cs:num`;
           mk_small_numeral nchunks, `nc:num`]
    (inst [d_ty, `:D`; total_ty, `:T`]
      `!(l: (D word) list). LENGTH l = ncoeffs ==>
         num_of_wordlist l = num_of_wordlist (MAP ((word:num->T word) o num_of_wordlist)
           (list_of_seq (\i. SUB_LIST (cs * i, cs) l) nc))`),
    REPEAT STRIP_TAC THEN
    UNDISCH_THEN (subst [mk_small_numeral ncoeffs, `n:num`]
      (inst [d_ty, `:D`] `LENGTH (l : (D word) list) = n`)) (fun th ->
       GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
         [MATCH_MP (CONV_RULE NUM_REDUCE_CONV
           (ISPECL [mk_small_numeral chunk_size; mk_small_numeral nchunks;
                    `l:'a list`] SUBLIST_PARTITION)) th]
       THEN ASSUME_TAC th) THEN
    IMP_REWRITE_TAC [CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
      (ISPECL [inst [d_ty, `:D`] `ll: ((D word) list) list`;
               mk_small_numeral chunk_size]
        (INST_TYPE [d_ty, `:N`; total_ty, `:M`] NUM_OF_WORDLIST_FLATTEN))] THEN
    CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
    ASM_REWRITE_TAC[ALL; LENGTH_SUB_LIST] THEN
    ARITH_TAC);;

(* Extract individual d-bit coefficients from a (d*chunk_size)-bit word. *)
let mk_subword_cases d chunk_size =
  let total = d * chunk_size in
  let d_ty = mk_finty (Num.num_of_int d) in
  let total_ty = mk_finty (Num.num_of_int total) in
  let arith_simp =
    let lhs = mk_eq(mk_small_numeral total,
                mk_comb(mk_comb(`( * ):num->num->num`,
                  mk_small_numeral d), `n:num`)) in
    let rhs = mk_eq(`n:num`, mk_small_numeral chunk_size) in
    ARITH_RULE (mk_eq(lhs, rhs)) in
  let meson_simp =
    let n_eq = mk_eq(`n:num`, mk_small_numeral chunk_size) in
    let k_lt_n = mk_comb(mk_comb(`(<):num->num->bool`, `k:num`), `n:num`) in
    let k_lt_cs = mk_comb(mk_comb(`(<):num->num->bool`, `k:num`),
                    mk_small_numeral chunk_size) in
    MESON[] (mk_eq(mk_conj(n_eq, k_lt_n), mk_conj(n_eq, k_lt_cs))) in
  let base =
    let th = INST_TYPE [total_ty, `:KL`; d_ty, `:L`] WORD_SUBWORD_NUM_OF_WORDLIST in
    let th = CONV_RULE(DEPTH_CONV DIMINDEX_CONV) th in
    REWRITE_RULE[arith_simp; meson_simp] th in
  let mk k =
    let th = SPEC (mk_small_numeral k)
      (SPEC (inst [d_ty, `:L`] `ls:(L word)list`) base) in
    CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ARITH] th) in
  map mk (0 -- (chunk_size - 1));;

(* Split a 256-element 32-bit-word list into 32 chunks of 8 (256-bit words),
   used to express the output spec as 32 store-sized pieces. *)
let NUM_OF_WORDLIST_SPLIT_32_256_8 = prove
 (`!(L:(32 word) list). LENGTH L = 256 ==> num_of_wordlist L =
     num_of_wordlist (MAP ((word:num->256 word) o num_of_wordlist)
       (list_of_seq (\i. SUB_LIST(8*i,8) L) 32))`,
  REPEAT STRIP_TAC THEN
  UNDISCH_THEN `LENGTH(L:(32 word)list)=256` (fun th ->
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
      [MATCH_MP (CONV_RULE NUM_REDUCE_CONV
        (ISPECL [`8`;`32`;`L:(32 word)list`] SUBLIST_PARTITION)) th] THEN ASSUME_TAC th) THEN
  IMP_REWRITE_TAC[CONV_RULE(ONCE_DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (ISPECL [`ll:((32 word)list)list`;`8`] (INST_TYPE[`:32`,`:N`;`:256`,`:M`] NUM_OF_WORDLIST_FLATTEN))] THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  ASM_REWRITE_TAC[ALL;LENGTH_SUB_LIST] THEN ARITH_TAC);;

(* MAP commutes with SUB_LIST. *)
let MAP_SUB_LIST = prove
 (`!(f:A->B) p q l. MAP f (SUB_LIST(p,q) l) = SUB_LIST(p,q) (MAP f l)`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(!p q l. P p q l) <=> (!l p q. P p q l)`] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; SUB_LIST_CLAUSES] THEN
  REPEAT GEN_TAC THEN SPEC_TAC(`q:num`,`q:num`) THEN SPEC_TAC(`p:num`,`p:num`) THEN
  MATCH_MP_TAC num_INDUCTION THEN ASM_REWRITE_TAC[SUB_LIST_CLAUSES; MAP] THEN
  REPEAT STRIP_TAC THEN SPEC_TAC(`q:num`,`q:num`) THEN MATCH_MP_TAC num_INDUCTION THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; MAP]);;

(* ------------------------------------------------------------------------- *)
(* D=18 instantiations: 32 chunks of 8 coefficients (144-bit words),         *)
(* one chunk per AVX2 block.                                                 *)
(* ------------------------------------------------------------------------- *)

let NUM_OF_WORDLIST_SPLIT_18_256_8 = mk_split_theorem 18 256 8;;
let WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D18 = mk_subword_cases 18 8;;

(* One 256-bit AVX2 store reassembles 8 zunpack17 coefficients into the       *)
(* num_of_wordlist of the mapped 8-element sublist.                           *)
let POLYZ17_STORE = prove
 (`!sl:(18 word) list. LENGTH sl = 8 ==>
     ((word_join:int128->int128->int256)
      ((word_join:int64->int64->int128)
       ((word_join:int32->int32->int64)
         (zunpack17 (word_subword (word (num_of_wordlist sl):144 word) (126,18)))
         (zunpack17 (word_subword (word (num_of_wordlist sl):144 word) (108,18))))
       ((word_join:int32->int32->int64)
         (zunpack17 (word_subword (word (num_of_wordlist sl):144 word) (90,18)))
         (zunpack17 (word_subword (word (num_of_wordlist sl):144 word) (72,18)))))
      ((word_join:int64->int64->int128)
       ((word_join:int32->int32->int64)
         (zunpack17 (word_subword (word (num_of_wordlist sl):144 word) (54,18)))
         (zunpack17 (word_subword (word (num_of_wordlist sl):144 word) (36,18))))
       ((word_join:int32->int32->int64)
         (zunpack17 (word_subword (word (num_of_wordlist sl):144 word) (18,18)))
         (zunpack17 (word_subword (word (num_of_wordlist sl):144 word) (0,18))))))
     = word(num_of_wordlist (MAP zunpack17 sl))`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D18 THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[num_CONV `8`; num_CONV `7`; num_CONV `6`; num_CONV `5`;
              num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`;
              LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  REWRITE_TAC[EL; HD; TL; num_CONV `7`; num_CONV `6`; num_CONV `5`;
              num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`] THEN
  REWRITE_TAC[EL; HD; TL; num_of_wordlist] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BLAST);;

(* Re-fold the two bytes128 pieces back into subwords of the 144-bit chunk. *)
let X86_BASE_SIMPS_D18 = [
  prove(`word ((t:num) MOD 2 EXP 128) : 128 word = word_subword (word t : 144 word) (0,128)`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_128] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_1; MOD_MOD_REFL] THEN
    REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 = 2 EXP 128`;
                ARITH_RULE `22300745198530623141535718272648361505980416 = 2 EXP 144`] THEN
    SIMP_TAC[MOD_MOD; LE_EXP; ARITH_EQ; ARITH_RULE `128 <= 144`] THEN
    REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);
  prove(`word ((t:num) DIV 2 EXP 16) : 128 word = word_subword (word t : 144 word) (16,128)`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_128] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `22300745198530623141535718272648361505980416 = 2 EXP 144`;
                ARITH_RULE `1461501637330902918203684832716283019655932542976 = 2 EXP 160`] THEN
    REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV)];;

(* Split a 144-bit chunk read into the two bytes128 loads the asm performs   *)
(* (at offsets 0 and 2 within each 18-byte block).                           *)
let READ_MEMORY_WBYTES_SPLIT_144_X86 = prove
 (`t < 2 EXP 144
    ==> (read (memory :> wbytes a) (s:x86state) = (word t : 144 word) <=>
         read (memory :> bytes128 a) s = (word (t MOD 2 EXP 128) : int128) /\
         read (memory :> bytes128 (word_add a (word 2))) s =
           (word (t DIV 2 EXP 16) : int128))`,
  DISCH_TAC THEN
  REWRITE_TAC[BYTES128_WBYTES; GSYM VAL_EQ; VAL_READ_WBYTES; READ_COMPONENT_COMPOSE] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VAL_WORD] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV THENC DEPTH_CONV NUM_MULT_CONV)
                (INST [`2`,`k:num`; `16`,`l:num`] READ_BYTES_SPLIT_ANY)] THEN
  REWRITE_TAC[CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV THENC DEPTH_CONV NUM_MULT_CONV)
    (INST [mk_comb(mk_comb(`word_add:int64->int64->int64`,`a:int64`),`word 2:int64`),`a:int64`;
           `14`,`k:num`; `2`,`l:num`] READ_BYTES_SPLIT_ANY)] THEN
  REWRITE_TAC[CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV THENC DEPTH_CONV NUM_MULT_CONV)
                (INST [`2`,`k:num`; `14`,`l:num`] READ_BYTES_SPLIT_ANY)] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL [`a:int64`; `2`; `read memory (s:x86state)`] READ_BYTES_BOUND) THEN
  MP_TAC(ISPECL [`word_add a (word 2):int64`; `14`; `read memory (s:x86state)`] READ_BYTES_BOUND) THEN
  MP_TAC(ISPECL [`word_add a (word 16):int64`; `2`; `read memory (s:x86state)`] READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `p0 = read (bytes (a,2)) (read memory (s:x86state))` THEN
  ABBREV_TAC `p1 = read (bytes (word_add a (word 2),14)) (read memory (s:x86state))` THEN
  ABBREV_TAC `p2 = read (bytes (word_add a (word 16),2)) (read memory (s:x86state))` THEN
  POP_ASSUM(K ALL_TAC) THEN POP_ASSUM(K ALL_TAC) THEN POP_ASSUM(K ALL_TAC) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `t MOD 22300745198530623141535718272648361505980416 = t` ASSUME_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 = 2 EXP 128`;
                   ARITH_RULE `65536 = 2 EXP 16`;
                   ARITH_RULE `5192296858534827628530496329220096 = 2 EXP 112`] THEN
  SIMP_TAC[MOD_MOD; LE_EXP; ARITH_EQ; ARITH_RULE `16 <= 128`] THEN
  REWRITE_TAC[DIV_MOD; DIV_DIV; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV THEN (CONV_TAC TAUT ORELSE ASM_ARITH_TAC));;

(* ------------------------------------------------------------------------- *)
(* zunpack17 lane folding for the VPSHUFB+VPSRLVD+VPAND+VPSUBD pipeline.      *)
(*                                                                           *)
(* After SIMD_SIMPLIFY each YMM0 lane is                                     *)
(*   word_sub (word 131072) (word_and (word_ushr <bytes> sh) (word 262143))  *)
(* The masked, shifted byte-join selects an 18-bit field of the 128-bit      *)
(* chunk half, so ZPRE17_LANE_CONV rewrites it to                            *)
(*   word_zx (word_subword <half> (off,18))                                  *)
(* via WORD_BLAST, and ZUNPACK17_CORRECT then folds the outer word_sub into  *)
(* zunpack17, giving an atomic lane that VPSUBD/the store handle cheaply.    *)
(* ------------------------------------------------------------------------- *)

let ZPRE17_LANE_CONV tm =
  (* the lane's byte slices come from a single chunk word; find its width *)
  let is_src t = try fst(dest_type(type_of t)) = "word" && is_comb t &&
        name_of(rator t) = "word" &&
        (let w = Num.int_of_num(dest_finty(hd(snd(dest_type(type_of t))))) in
         w = 128 || w = 144)
    with _ -> false in
  let src = find_term is_src tm in
  let srcw = Num.int_of_num(dest_finty(hd(snd(dest_type(type_of src))))) in
  let srcty = mk_finty(Num.num_of_int srcw) in
  (* The masked 18-bit field always begins at one of the eight coefficient    *)
  (* boundaries within a chunk half, so only those offsets are tried (rather   *)
  (* than every offset in 0..130): each candidate needs a full WORD_BLAST, and *)
  (* restricting the list avoids ~500 wasted blasts per block.                 *)
  tryfind (fun off ->
    let goal = mk_eq(tm, mk_comb(`word_zx:18 word->int32`,
      mk_comb(mk_comb(inst[srcty,`:N`] `word_subword:N word->num#num->18 word`, src),
              mk_pair(mk_small_numeral off, `18`)))) in
    WORD_BLAST goal) [0; 18; 36; 54; 72; 90; 108; 126];;

let ZPRE17_FOLD_CONV =
  DEPTH_CONV (fun t ->
    if is_comb t && is_comb(rator t) &&
       (try name_of(rator(rator t)) = "word_and" with _ -> false) &&
       (try rand t = `word 262143:int32` with _ -> false)
    then ZPRE17_LANE_CONV t else failwith "ZPRE17_FOLD_CONV");;

(* Fold the YMM0 register read assumption to a word_join of 8 atomic         *)
(* zunpack17(word_subword ...) lanes.  Targets only a YMM0 read carrying the  *)
(* post-VPSUBD shape (word_sub (word 131072) ...), so it is a cheap no-op on  *)
(* every other step.                                                         *)
let ZUNPACK17_FOLD_TAC (asl,w as gl) =
  let is_target th =
    let c = concl th in
    can (term_match [] `read YMM0 s = x`) c &&
    free_in `word 131072:int32` c in
  (TRY(FIRST_X_ASSUM(fun th ->
    if not(is_target th) then failwith "" else
    ASSUME_TAC(CONV_RULE(RAND_CONV
      (ZPRE17_FOLD_CONV THENC REWRITE_CONV[ZUNPACK17_CORRECT])) th)))) gl;;

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POLYZ_UNPACK_17_CORRECT = prove
 (`!r b (l:(18 word) list) pc.
        aligned 32 r /\
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,1611); (b,576)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_polyz_unpack_17_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [r; b] s /\
                  read(memory :> bytes(b,576)) s = num_of_wordlist l)
             (\s. read RIP s = word(pc + 1610) /\
                  read(memory :> bytes(r,1024)) s = num_of_wordlist (MAP zunpack17 l))
             (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5] ,,
              MAYCHANGE [RAX] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bytes(r,1024)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `b:int64`; `l:(18 word) list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS;
              NONOVERLAPPING_CLAUSES; ALL; fst MLDSA_POLYZ_UNPACK_17_EXEC] THEN
  STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Expand input: 256 coeffs -> 32 chunks of 144-bit words ***)
  UNDISCH_TAC `read(memory :> bytes(b,576)) s0 = num_of_wordlist(l:(18 word) list)` THEN
  IMP_REWRITE_TAC [NUM_OF_WORDLIST_SPLIT_18_256_8] THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC [MAP; o_DEF] THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  STRIP_TAC THEN

  (*** Split each 144-bit chunk into the two bytes128 loads ***)
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match []
       `read (memory :> wbytes a) s = word t`) (concl th)
    then MP_TAC th else NO_TAC)) THEN
  IMP_REWRITE_TAC [READ_MEMORY_WBYTES_SPLIT_144_X86] THEN
  MAP_EVERY (fun n -> SUBGOAL_THEN (subst[mk_small_numeral n,`k:num`]
    `num_of_wordlist (SUB_LIST (8 * k,8) (l : (18 word) list)) < 2 EXP 144`)
     (fun th -> REWRITE_TAC[th]) THENL [
       TRANS_TAC LTE_TRANS (subst[mk_small_numeral n,`k:num`]
                            `2 EXP (dimindex(:18) * LENGTH(SUB_LIST(8*k,8) (l : (18 word) list)))`) THEN
       REWRITE_TAC[NUM_OF_WORDLIST_BOUND] THEN
       REWRITE_TAC[LENGTH_SUB_LIST; DIMINDEX_CONV `dimindex (:18)`] THEN
       ASM_SIMP_TAC [] THEN NUM_REDUCE_TAC;
       ALL_TAC]) (0--31) THEN
  (*** Normalise the high-half load addresses from the nested form           ***)
  (***   word_add (word_add b (word 18k)) (word 2)                           ***)
  (*** to the reduced form word_add b (word (18k+2)) the stepper computes,    ***)
  (*** so each block's high-half load resolves and YMM0 becomes ground before ***)
  (*** the store (otherwise DISCARD_OLDSTATE_TAC silently drops the store).    ***)
  CONV_TAC (GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_ADD_ASSOC_CONSTS] THENC
            TOP_SWEEP_CONV NUM_ADD_CONV) THEN
  REPEAT STRIP_TAC THEN

  (*** Express each chunk's two bytes128 input pieces as subwords of the     ***)
  (*** single 144-bit chunk word, so the per-lane VPSUBD operands compose    ***)
  (*** into a single word_subword and SIMD_SIMPLIFY stays cheap.             ***)
  RULE_ASSUM_TAC(REWRITE_RULE X86_BASE_SIMPS_D18) THEN

  (*** Symbolic execution: simplify each block's lanes, then fold the just- ***)
  (*** computed YMM0 into atomic zunpack17 lanes before it is stored so the  ***)
  (*** store and subsequent steps stay cheap.                               ***)
  MAP_EVERY (fun n ->
    X86_STEPS_TAC MLDSA_POLYZ_UNPACK_17_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC [] THEN
    ZUNPACK17_FOLD_TAC) (1--276) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Fold each 256-bit store into 8 atomic zunpack17 lanes ***)
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(RAND_CONV
     (ZPRE17_FOLD_CONV THENC REWRITE_CONV[ZUNPACK17_CORRECT])))) THEN

  (*** Establish the 32 sublist-length facts the CASES rewrites need ***)
  MAP_EVERY (fun i -> SUBGOAL_THEN
    (subst [mk_small_numeral (8 * i), `i:num`]
      `LENGTH (SUB_LIST (i, 8) (l : (18 word) list)) = 8`) ASSUME_TAC
    THENL [ASM_REWRITE_TAC [LENGTH_SUB_LIST] THEN NUM_REDUCE_TAC; ALL_TAC])
    (0 -- 31) THEN

  (*** Express the spec RHS as 32 chunks and split the 1024-byte output read   ***)
  (*** into 32 matching 256-bit conjuncts.                                     ***)
  SUBGOAL_THEN `LENGTH(MAP zunpack17 (l:(18 word) list)) = 256` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(MAP zunpack17 (l:(18 word) list)) = 256`
    then GEN_REWRITE_TAC RAND_CONV [MATCH_MP NUM_OF_WORDLIST_SPLIT_32_256_8 th] THEN ASSUME_TAC th
    else NO_TAC) THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[MAP; o_DEF; GSYM MAP_SUB_LIST] THEN
  CONV_TAC BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV THEN
  (*** Normalise 8*k indices to literals everywhere, convert the stores to     ***)
  (*** wbytes form, then rewrite each conjunct's spec RHS into the stored      ***)
  (*** word_join shape and discharge it against its store.                     ***)
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
                 REWRITE_RULE[BYTES256_WBYTES]) THEN
  ASM_SIMP_TAC[GSYM POLYZ17_STORE]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine correctness                                                    *)
(* This must be kept in sync with the CBMC specification in                  *)
(* mldsa/src/native/x86_64/src/arith_native_x86_64.h                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POLYZ_UNPACK_17_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r b (l:(18 word) list) pc stackpointer returnaddress.
        aligned 32 r /\
        ALL (nonoverlapping (word pc, LENGTH mldsa_polyz_unpack_17_tmc))
            [(r,1024)] /\
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,LENGTH mldsa_polyz_unpack_17_tmc); (b,576)] /\
        nonoverlapping (stackpointer,8) (r,1024)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_polyz_unpack_17_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  read(memory :> bytes(b,576)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read(memory :> bytes(r,1024)) s = num_of_wordlist (MAP zunpack17 l) /\
                  (!i. i < 256 ==>
                       --(&(2 EXP 17) - &1) <= ival(EL i (MAP zunpack17 l)) /\
                       ival(EL i (MAP zunpack17 l)) <= &(2 EXP 17)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_polyz_unpack_17_tmc
   MLDSA_POLYZ_UNPACK_17_CORRECT THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(18 word) list`; `i:num`] ZUNPACK17_MAP_BOUND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MLDSA_POLYZ_UNPACK_17_SUBROUTINE_CORRECT = prove
 (`!r b (l:(18 word) list) pc stackpointer returnaddress.
        aligned 32 r /\
        ALL (nonoverlapping (word pc, LENGTH mldsa_polyz_unpack_17_mc))
            [(r,1024)] /\
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,LENGTH mldsa_polyz_unpack_17_mc); (b,576)] /\
        nonoverlapping (stackpointer,8) (r,1024)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_polyz_unpack_17_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  read(memory :> bytes(b,576)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read(memory :> bytes(r,1024)) s = num_of_wordlist (MAP zunpack17 l) /\
                  (!i. i < 256 ==>
                       --(&(2 EXP 17) - &1) <= ival(EL i (MAP zunpack17 l)) /\
                       ival(EL i (MAP zunpack17 l)) <= &(2 EXP 17)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLYZ_UNPACK_17_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(* Signature of mldsa_polyz_unpack_17, matching the CBMC specification. The     *)
(* central subroutine_signatures table is populated separately, so it is        *)
(* given inline here.                                                           *)
let mldsa_polyz_unpack_17_signature =
  ([(*args*)
     ("r", "int32_t[static 256]", (*is const?*)"false");
     ("a", "uint8_t[static 576]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "576"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ]);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mldsa_polyz_unpack_17_signature
    (REWRITE_RULE[SOME_FLAGS] MLDSA_POLYZ_UNPACK_17_CORRECT)
    MLDSA_POLYZ_UNPACK_17_EXEC;;

let MLDSA_POLYZ_UNPACK_17_SAFE =
  REWRITE_RULE [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS]
  (time prove
   (full_spec,
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS] THEN
    PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLDSA_POLYZ_UNPACK_17_EXEC));;

let MLDSA_POLYZ_UNPACK_17_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r b (l:(18 word) list) pc stackpointer returnaddress.
          aligned 32 r /\
          ALL (nonoverlapping (word pc, LENGTH mldsa_polyz_unpack_17_tmc))
              [(r,1024)] /\
          LENGTH l = 256 /\
          ALL (nonoverlapping (r,1024))
              [(word pc,LENGTH mldsa_polyz_unpack_17_tmc); (b,576)] /\
          nonoverlapping (stackpointer,8) (r,1024)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_polyz_unpack_17_tmc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; b] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events b r pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [b,576; r,1024; stackpointer,8]
                                               [r,1024; stackpointer,8]))
               (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_polyz_unpack_17_tmc
    MLDSA_POLYZ_UNPACK_17_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLDSA_POLYZ_UNPACK_17_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r b (l:(18 word) list) pc stackpointer returnaddress.
          aligned 32 r /\
          ALL (nonoverlapping (word pc, LENGTH mldsa_polyz_unpack_17_mc))
              [(r,1024)] /\
          LENGTH l = 256 /\
          ALL (nonoverlapping (r,1024))
              [(word pc,LENGTH mldsa_polyz_unpack_17_mc); (b,576)] /\
          nonoverlapping (stackpointer,8) (r,1024)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_polyz_unpack_17_mc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; b] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events b r pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [b,576; r,1024; stackpointer,8]
                                               [r,1024; stackpointer,8]))
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLYZ_UNPACK_17_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let mldsa_polyz_unpack_17_windows_mc = define_from_elf
   "mldsa_polyz_unpack_17_windows_mc" "x86/mldsa/mldsa_polyz_unpack_17.obj";;

let mldsa_polyz_unpack_17_windows_tmc =
  define_trimmed "mldsa_polyz_unpack_17_windows_tmc" mldsa_polyz_unpack_17_windows_mc;;

let MLDSA_POLYZ_UNPACK_17_WINDOWS_TMC_EXEC =
  X86_MK_EXEC_RULE mldsa_polyz_unpack_17_windows_tmc;;

let MLDSA_POLYZ_UNPACK_17_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!r b (l:(18 word) list) pc stackpointer returnaddress.
        aligned 32 r /\
        ALL (nonoverlapping (word pc, LENGTH mldsa_polyz_unpack_17_windows_tmc))
            [(r,1024)] /\
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,LENGTH mldsa_polyz_unpack_17_windows_tmc); (b,576)] /\
        nonoverlapping (word_sub stackpointer (word 16),24) (r,1024) /\
        nonoverlapping (word_sub stackpointer (word 16),16) (b,576) /\
        nonoverlapping (word pc,LENGTH mldsa_polyz_unpack_17_windows_tmc)
                       (word_sub stackpointer (word 16),16)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_polyz_unpack_17_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [r; b] s /\
                  read(memory :> bytes(b,576)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read(memory :> bytes(r,1024)) s = num_of_wordlist (MAP zunpack17 l) /\
                  (!i. i < 256 ==>
                       --(&(2 EXP 17) - &1) <= ival(EL i (MAP zunpack17 l)) /\
                       ival(EL i (MAP zunpack17 l)) <= &(2 EXP 17)))
             (MAYCHANGE [RSP] ,,
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)] ,,
              MAYCHANGE [memory :> bytes(r,1024)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC mldsa_polyz_unpack_17_windows_tmc
      mldsa_polyz_unpack_17_tmc MLDSA_POLYZ_UNPACK_17_CORRECT THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(18 word) list`; `i:num`] ZUNPACK17_MAP_BOUND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MLDSA_POLYZ_UNPACK_17_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!r b (l:(18 word) list) pc stackpointer returnaddress.
        aligned 32 r /\
        ALL (nonoverlapping (word pc, LENGTH mldsa_polyz_unpack_17_windows_mc))
            [(r,1024)] /\
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,LENGTH mldsa_polyz_unpack_17_windows_mc); (b,576)] /\
        nonoverlapping (word_sub stackpointer (word 16),24) (r,1024) /\
        nonoverlapping (word_sub stackpointer (word 16),16) (b,576) /\
        nonoverlapping (word pc,LENGTH mldsa_polyz_unpack_17_windows_mc)
                       (word_sub stackpointer (word 16),16)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_polyz_unpack_17_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [r; b] s /\
                  read(memory :> bytes(b,576)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read(memory :> bytes(r,1024)) s = num_of_wordlist (MAP zunpack17 l) /\
                  (!i. i < 256 ==>
                       --(&(2 EXP 17) - &1) <= ival(EL i (MAP zunpack17 l)) /\
                       ival(EL i (MAP zunpack17 l)) <= &(2 EXP 17)))
             (MAYCHANGE [RSP] ,,
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)] ,,
              MAYCHANGE [memory :> bytes(r,1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLYZ_UNPACK_17_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

(* Windows safety proofs *)

let MLDSA_POLYZ_UNPACK_17_NOIBT_WINDOWS_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r b (l:(18 word) list) pc stackpointer returnaddress.
          aligned 32 r /\
          ALL (nonoverlapping (word pc, LENGTH mldsa_polyz_unpack_17_windows_tmc))
              [(r,1024)] /\
          LENGTH l = 256 /\
          ALL (nonoverlapping (r,1024))
              [(word pc,LENGTH mldsa_polyz_unpack_17_windows_tmc); (b,576)] /\
          nonoverlapping (word_sub stackpointer (word 16),24) (r,1024) /\
          nonoverlapping (word_sub stackpointer (word 16),16) (b,576) /\
          nonoverlapping (word pc,LENGTH mldsa_polyz_unpack_17_windows_tmc)
                         (word_sub stackpointer (word 16),16)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_polyz_unpack_17_windows_tmc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    WINDOWS_C_ARGUMENTS [r; b] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events b r pc (word_sub stackpointer (word 16)) returnaddress /\
                         memaccess_inbounds e2
                           [b,576; r,1024; word_sub stackpointer (word 16),24]
                           [r,1024; word_sub stackpointer (word 16),16]))
               (MAYCHANGE [RSP] ,,
                WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)] ,,
                MAYCHANGE [memory :> bytes(r,1024)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC mldsa_polyz_unpack_17_windows_tmc
    mldsa_polyz_unpack_17_tmc MLDSA_POLYZ_UNPACK_17_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLDSA_POLYZ_UNPACK_17_WINDOWS_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r b (l:(18 word) list) pc stackpointer returnaddress.
          aligned 32 r /\
          ALL (nonoverlapping (word pc, LENGTH mldsa_polyz_unpack_17_windows_mc))
              [(r,1024)] /\
          LENGTH l = 256 /\
          ALL (nonoverlapping (r,1024))
              [(word pc,LENGTH mldsa_polyz_unpack_17_windows_mc); (b,576)] /\
          nonoverlapping (word_sub stackpointer (word 16),24) (r,1024) /\
          nonoverlapping (word_sub stackpointer (word 16),16) (b,576) /\
          nonoverlapping (word pc,LENGTH mldsa_polyz_unpack_17_windows_mc)
                         (word_sub stackpointer (word 16),16)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_polyz_unpack_17_windows_mc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    WINDOWS_C_ARGUMENTS [r; b] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events b r pc (word_sub stackpointer (word 16)) returnaddress /\
                         memaccess_inbounds e2
                           [b,576; r,1024; word_sub stackpointer (word 16),24]
                           [r,1024; word_sub stackpointer (word 16),16]))
               (MAYCHANGE [RSP] ,,
                WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)] ,,
                MAYCHANGE [memory :> bytes(r,1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLYZ_UNPACK_17_NOIBT_WINDOWS_SUBROUTINE_SAFE));;
