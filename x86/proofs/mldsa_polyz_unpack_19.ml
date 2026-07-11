(*
 * Copyright (c) The mldsa-native project authors
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Functional correctness of polyz_unpack_19 (x86_64 AVX2):                  *)
(* Unpack polynomial z with 20-bit packed coefficients (GAMMA1 = 2^19)       *)
(* Maps packed [0, 2^20-1] to signed [-(2^19-1), 2^19] via GAMMA1 - x        *)
(* (ML-DSA-65/87).                                                              *)
(*                                                                           *)
(* The x86 routine builds the shuffle/shift/mask/gamma1 constants inline     *)
(* (VMOVQ/VPINSRQ/VINSERTI128/VPBROADCASTD) and unpacks 8 coefficients per   *)
(* block with VPSHUFB/VPSRLVD/VPAND/VPSUBD.                                  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mldsa_specs.ml";;
needs "x86/proofs/mldsa_utils.ml";;

(**** print_literal_from_elf "x86/mldsa/mldsa_polyz_unpack_19.o";;
 ****)

let mldsa_polyz_unpack_19_mc = define_assert_from_elf
  "mldsa_polyz_unpack_19_mc" "x86/mldsa/mldsa_polyz_unpack_19.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0xb8; 0x00; 0x01; 0x02; 0xff; 0x02; 0x03; 0x04; 0xff;
                           (* MOV (% rax) (Imm64 (word 18375815690981605632)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xc8;
                           (* VMOVQ (%_% xmm1) (% rax) *)
  0x48; 0xb8; 0x05; 0x06; 0x07; 0xff; 0x07; 0x08; 0x09; 0xff;
                           (* MOV (% rax) (Imm64 (word 18377228584898463237)) *)
  0xc4; 0xe3; 0xf1; 0x22; 0xc8; 0x01;
                           (* VPINSRQ (%_% xmm1) (%_% xmm1) (% rax) (Imm8 (word 1)) *)
  0x48; 0xb8; 0x16; 0x17; 0x18; 0xff; 0x18; 0x19; 0x1a; 0xff;
                           (* MOV (% rax) (Imm64 (word 18382032424215779094)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xe8;
                           (* VMOVQ (%_% xmm5) (% rax) *)
  0x48; 0xb8; 0x1b; 0x1c; 0x1d; 0xff; 0x1d; 0x1e; 0x1f; 0xff;
                           (* MOV (% rax) (Imm64 (word 18383445318132636699)) *)
  0xc4; 0xe3; 0xd1; 0x22; 0xe8; 0x01;
                           (* VPINSRQ (%_% xmm5) (%_% xmm5) (% rax) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x75; 0x38; 0xcd; 0x01;
                           (* VINSERTI128 (%_% ymm1) (%_% ymm1) (%_% xmm5) (Imm8 (word 1)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x04; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 17179869184)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xd0;
                           (* VMOVQ (%_% xmm2) (% rax) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x04; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 17179869184)) *)
  0xc4; 0xe3; 0xe9; 0x22; 0xd0; 0x01;
                           (* VPINSRQ (%_% xmm2) (%_% xmm2) (% rax) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x6d; 0x38; 0xd2; 0x01;
                           (* VINSERTI128 (%_% ymm2) (%_% ymm2) (%_% xmm2) (Imm8 (word 1)) *)
  0xb8; 0xff; 0xff; 0x0f; 0x00;
                           (* MOV (% eax) (Imm32 (word 1048575)) *)
  0xc5; 0xf9; 0x6e; 0xd8;  (* VMOVD (%_% xmm3) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xdb;
                           (* VPBROADCASTD (%_% ymm3) (%_% xmm3) *)
  0xb8; 0x00; 0x00; 0x08; 0x00;
                           (* MOV (% eax) (Imm32 (word 524288)) *)
  0xc5; 0xf9; 0x6e; 0xe0;  (* VMOVD (%_% xmm4) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xe4;
                           (* VPBROADCASTD (%_% ymm4) (%_% xmm4) *)
  0xc5; 0xfa; 0x6f; 0x06;  (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,0))) *)
  0xc5; 0xfa; 0x6f; 0x6e; 0x04;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,4))) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc5; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x00; 0xc1;
                           (* VPSHUFB (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xe2; 0x7d; 0x45; 0xc2;
                           (* VPSRLVD (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xdb; 0xc3;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xdd; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x07;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x46; 0x14;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,20))) *)
  0xc5; 0xfa; 0x6f; 0x6e; 0x18;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,24))) *)
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
  0xc5; 0xfa; 0x6f; 0x46; 0x28;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,40))) *)
  0xc5; 0xfa; 0x6f; 0x6e; 0x2c;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,44))) *)
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
  0xc5; 0xfa; 0x6f; 0x46; 0x3c;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,60))) *)
  0xc5; 0xfa; 0x6f; 0x6e; 0x40;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,64))) *)
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
  0xc5; 0xfa; 0x6f; 0x46; 0x50;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,80))) *)
  0xc5; 0xfa; 0x6f; 0x6e; 0x54;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,84))) *)
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
  0xc5; 0xfa; 0x6f; 0x46; 0x64;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,100))) *)
  0xc5; 0xfa; 0x6f; 0x6e; 0x68;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,104))) *)
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
  0xc5; 0xfa; 0x6f; 0x46; 0x78;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,120))) *)
  0xc5; 0xfa; 0x6f; 0x6e; 0x7c;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,124))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0x8c; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,140))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x90; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,144))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,160))) *)
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
  0xc5; 0xfd; 0x7f; 0x87; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0xb4; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,180))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xb8; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,184))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0xc8; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,200))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xcc; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,204))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0xdc; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,220))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,224))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0xf0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,240))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xf4; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,244))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0x04; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,260))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x08; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,264))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0x18; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,280))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x1c; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,284))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0x2c; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,300))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x30; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,304))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,320))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x44; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,324))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0x54; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,340))) *)
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
  0xc5; 0xfd; 0x7f; 0x87; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,544))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0x68; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,360))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x6c; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,364))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0x7c; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,380))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,384))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0x90; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,400))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x94; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,404))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0xa4; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,420))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xa8; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,424))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0xb8; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,440))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xbc; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,444))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0xcc; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,460))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xd0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,464))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,480))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xe4; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,484))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0xf4; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,500))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0xf8; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,504))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0x08; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,520))) *)
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
  0xc5; 0xfd; 0x7f; 0x87; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,832))) (%_% ymm0) *)
  0xc5; 0xfa; 0x6f; 0x86; 0x1c; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,540))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,544))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0x30; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,560))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x34; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,564))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0x44; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,580))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x48; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,584))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0x58; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,600))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x5c; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,604))) *)
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
  0xc5; 0xfa; 0x6f; 0x86; 0x6c; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm0) (Memop Word128 (%% (rsi,620))) *)
  0xc5; 0xfa; 0x6f; 0xae; 0x70; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm5) (Memop Word128 (%% (rsi,624))) *)
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

let mldsa_polyz_unpack_19_tmc =
  define_trimmed "mldsa_polyz_unpack_19_tmc" mldsa_polyz_unpack_19_mc;;

let MLDSA_POLYZ_UNPACK_19_EXEC = X86_MK_CORE_EXEC_RULE mldsa_polyz_unpack_19_tmc;;

(* ------------------------------------------------------------------------- *)
(* Coefficient (un)packing helpers.  These are present in the mldsa-native   *)
(* utils but not (yet) in the in-tree x86/proofs/mldsa_utils.ml, so they are *)
(* defined locally here.                                                     *)
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
(* D=20 instantiations: 32 chunks of 8 coefficients (160-bit words),         *)
(* one chunk per AVX2 block.                                                 *)
(* ------------------------------------------------------------------------- *)

let NUM_OF_WORDLIST_SPLIT_20_256_8 = mk_split_theorem 20 256 8;;
let WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D20 = mk_subword_cases 20 8;;

(* One 256-bit AVX2 store reassembles 8 zunpack19 coefficients into the       *)
(* num_of_wordlist of the mapped 8-element sublist.                           *)
let POLYZ19_STORE = prove
 (`!sl:(20 word) list. LENGTH sl = 8 ==>
     ((word_join:int128->int128->int256)
      ((word_join:int64->int64->int128)
       ((word_join:int32->int32->int64)
         (zunpack19 (word_subword (word (num_of_wordlist sl):160 word) (140,20)))
         (zunpack19 (word_subword (word (num_of_wordlist sl):160 word) (120,20))))
       ((word_join:int32->int32->int64)
         (zunpack19 (word_subword (word (num_of_wordlist sl):160 word) (100,20)))
         (zunpack19 (word_subword (word (num_of_wordlist sl):160 word) (80,20)))))
      ((word_join:int64->int64->int128)
       ((word_join:int32->int32->int64)
         (zunpack19 (word_subword (word (num_of_wordlist sl):160 word) (60,20)))
         (zunpack19 (word_subword (word (num_of_wordlist sl):160 word) (40,20))))
       ((word_join:int32->int32->int64)
         (zunpack19 (word_subword (word (num_of_wordlist sl):160 word) (20,20)))
         (zunpack19 (word_subword (word (num_of_wordlist sl):160 word) (0,20))))))
     = word(num_of_wordlist (MAP zunpack19 sl))`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D20 THEN
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

(* Re-fold the two bytes128 pieces back into subwords of the 160-bit chunk. *)
let X86_BASE_SIMPS_D20 = [
  prove(`word ((t:num) MOD 2 EXP 128) : 128 word = word_subword (word t : 160 word) (0,128)`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_128] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_1; MOD_MOD_REFL] THEN
    REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 = 2 EXP 128`;
                ARITH_RULE `1461501637330902918203684832716283019655932542976 = 2 EXP 160`] THEN
    SIMP_TAC[MOD_MOD; LE_EXP; ARITH_EQ; ARITH_RULE `128 <= 160`] THEN
    REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);
  prove(`word ((t:num) DIV 2 EXP 32) : 128 word = word_subword (word t : 160 word) (32,128)`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_128] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `1461501637330902918203684832716283019655932542976 = 2 EXP 160`;
                ARITH_RULE `6277101735386680763835789423207666416102355444464034512896 = 2 EXP 192`] THEN
    REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV)];;

(* Split a 160-bit chunk read into the two bytes128 loads the asm performs   *)
(* (at offsets 0 and 4 within each 18-byte block).                           *)
let READ_MEMORY_WBYTES_SPLIT_160_X86 = prove
 (`t < 2 EXP 160
    ==> (read (memory :> wbytes a) (s:x86state) = (word t : 160 word) <=>
         read (memory :> bytes128 a) s = (word (t MOD 2 EXP 128) : int128) /\
         read (memory :> bytes128 (word_add a (word 4))) s =
           (word (t DIV 2 EXP 32) : int128))`,
  DISCH_TAC THEN
  REWRITE_TAC[BYTES128_WBYTES; GSYM VAL_EQ; VAL_READ_WBYTES; READ_COMPONENT_COMPOSE] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VAL_WORD] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV THENC DEPTH_CONV NUM_MULT_CONV)
                (INST [`4`,`k:num`; `16`,`l:num`] READ_BYTES_SPLIT_ANY)] THEN
  REWRITE_TAC[CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV THENC DEPTH_CONV NUM_MULT_CONV)
    (INST [mk_comb(mk_comb(`word_add:int64->int64->int64`,`a:int64`),`word 4:int64`),`a:int64`;
           `12`,`k:num`; `4`,`l:num`] READ_BYTES_SPLIT_ANY)] THEN
  REWRITE_TAC[CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV THENC DEPTH_CONV NUM_MULT_CONV)
                (INST [`4`,`k:num`; `12`,`l:num`] READ_BYTES_SPLIT_ANY)] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL [`a:int64`; `4`; `read memory (s:x86state)`] READ_BYTES_BOUND) THEN
  MP_TAC(ISPECL [`word_add a (word 4):int64`; `12`; `read memory (s:x86state)`] READ_BYTES_BOUND) THEN
  MP_TAC(ISPECL [`word_add a (word 16):int64`; `4`; `read memory (s:x86state)`] READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `p0 = read (bytes (a,4)) (read memory (s:x86state))` THEN
  ABBREV_TAC `p1 = read (bytes (word_add a (word 4),12)) (read memory (s:x86state))` THEN
  ABBREV_TAC `p2 = read (bytes (word_add a (word 16),4)) (read memory (s:x86state))` THEN
  POP_ASSUM(K ALL_TAC) THEN POP_ASSUM(K ALL_TAC) THEN POP_ASSUM(K ALL_TAC) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `t MOD 1461501637330902918203684832716283019655932542976 = t` ASSUME_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `1461501637330902918203684832716283019655932542976 = 2 EXP 160`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 = 2 EXP 128`;
                   ARITH_RULE `4294967296 = 2 EXP 32`;
                   ARITH_RULE `79228162514264337593543950336 = 2 EXP 96`] THEN
  SIMP_TAC[MOD_MOD; LE_EXP; ARITH_EQ; ARITH_RULE `32 <= 128`] THEN
  REWRITE_TAC[DIV_MOD; DIV_DIV; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV THEN (CONV_TAC TAUT ORELSE ASM_ARITH_TAC));;

(* ------------------------------------------------------------------------- *)
(* zunpack19 lane folding for the VPSHUFB+VPSRLVD+VPAND+VPSUBD pipeline.      *)
(*                                                                           *)
(* After SIMD_SIMPLIFY each YMM0 lane is                                     *)
(*   word_sub (word 524288) (word_and (word_ushr <bytes> sh) (word 1048575))  *)
(* The masked, shifted byte-join selects a 20-bit field of the 128-bit      *)
(* chunk half, so ZPRE19_LANE_CONV rewrites it to                            *)
(*   word_zx (word_subword <half> (off,20))                                  *)
(* via WORD_BLAST, and ZUNPACK19_CORRECT then folds the outer word_sub into  *)
(* zunpack19, giving an atomic lane that VPSUBD/the store handle cheaply.    *)
(* ------------------------------------------------------------------------- *)

let ZPRE19_LANE_CONV tm =
  (* the lane's byte slices come from a single chunk word; find its width *)
  let is_src t = try fst(dest_type(type_of t)) = "word" && is_comb t &&
        name_of(rator t) = "word" &&
        (let w = Num.int_of_num(dest_finty(hd(snd(dest_type(type_of t))))) in
         w = 128 || w = 160)
    with _ -> false in
  let src = find_term is_src tm in
  let srcw = Num.int_of_num(dest_finty(hd(snd(dest_type(type_of src))))) in
  let srcty = mk_finty(Num.num_of_int srcw) in
  (* The 20-bit fields sit at the eight 20-bit-aligned offsets of the chunk;
     restricting the WORD_BLAST search to these (rather than 0..150) keeps each
     lane's fold cheap. *)
  tryfind (fun off ->
    let goal = mk_eq(tm, mk_comb(`word_zx:20 word->int32`,
      mk_comb(mk_comb(inst[srcty,`:N`] `word_subword:N word->num#num->20 word`, src),
              mk_pair(mk_small_numeral off, `20`)))) in
    WORD_BLAST goal) [0; 20; 40; 60; 80; 100; 120; 140];;

let ZPRE19_FOLD_CONV =
  DEPTH_CONV (fun t ->
    if is_comb t && is_comb(rator t) &&
       (try name_of(rator(rator t)) = "word_and" with _ -> false) &&
       (try rand t = `word 1048575:int32` with _ -> false)
    then ZPRE19_LANE_CONV t else failwith "ZPRE19_FOLD_CONV");;

(* Fold the YMM0 register read assumption to a word_join of 8 atomic         *)
(* zunpack19(word_subword ...) lanes.  Targets only a YMM0 read carrying the  *)
(* post-VPSUBD shape (word_sub (word 524288) ...), so it is a cheap no-op on  *)
(* every other step.                                                         *)
let ZUNPACK19_FOLD_TAC (asl,w as gl) =
  let is_target th =
    let c = concl th in
    can (term_match [] `read YMM0 s = x`) c &&
    can (find_term (fun t -> t = `word 524288:int32`)) c in
  (TRY(FIRST_X_ASSUM(fun th ->
    if not(is_target th) then failwith "" else
    ASSUME_TAC(CONV_RULE(RAND_CONV
      (ZPRE19_FOLD_CONV THENC REWRITE_CONV[ZUNPACK19_CORRECT])) th)))) gl;;

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POLYZ_UNPACK_19_CORRECT = prove
 (`!r b (l:(20 word) list) pc.
        aligned 32 r /\
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,1614); (b,640)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_polyz_unpack_19_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [r; b] s /\
                  read(memory :> bytes(b,640)) s = num_of_wordlist l)
             (\s. read RIP s = word(pc + 1613) /\
                  read(memory :> bytes(r,1024)) s = num_of_wordlist (MAP zunpack19 l))
             (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5] ,,
              MAYCHANGE [RAX] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bytes(r,1024)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `b:int64`; `l:(20 word) list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS;
              NONOVERLAPPING_CLAUSES; ALL; fst MLDSA_POLYZ_UNPACK_19_EXEC] THEN
  STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Expand input: 256 coeffs -> 32 chunks of 160-bit words ***)
  UNDISCH_TAC `read(memory :> bytes(b,640)) s0 = num_of_wordlist(l:(20 word) list)` THEN
  IMP_REWRITE_TAC [NUM_OF_WORDLIST_SPLIT_20_256_8] THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC [MAP; o_DEF] THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  STRIP_TAC THEN

  (*** Split each 160-bit chunk into the two bytes128 loads ***)
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match []
       `read (memory :> wbytes a) s = word t`) (concl th)
    then MP_TAC th else NO_TAC)) THEN
  IMP_REWRITE_TAC [READ_MEMORY_WBYTES_SPLIT_160_X86] THEN
  MAP_EVERY (fun n -> SUBGOAL_THEN (subst[mk_small_numeral n,`k:num`]
    `num_of_wordlist (SUB_LIST (8 * k,8) (l : (20 word) list)) < 2 EXP 160`)
     (fun th -> REWRITE_TAC[th]) THENL [
       TRANS_TAC LTE_TRANS (subst[mk_small_numeral n,`k:num`]
                            `2 EXP (dimindex(:20) * LENGTH(SUB_LIST(8*k,8) (l : (20 word) list)))`) THEN
       REWRITE_TAC[NUM_OF_WORDLIST_BOUND] THEN
       REWRITE_TAC[LENGTH_SUB_LIST; DIMINDEX_CONV `dimindex (:20)`] THEN
       ASM_SIMP_TAC [] THEN NUM_REDUCE_TAC;
       ALL_TAC]) (0--31) THEN
  (*** Normalise the high-half load addresses from the nested form           ***)
  (***   word_add (word_add b (word 20k)) (word 4)                           ***)
  (*** to the reduced form word_add b (word (20k+4)) the stepper computes,    ***)
  (*** so each block's high-half load resolves and YMM0 becomes ground before ***)
  (*** the store (otherwise DISCARD_OLDSTATE_TAC silently drops the store).    ***)
  CONV_TAC (GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_ADD_ASSOC_CONSTS] THENC
            TOP_SWEEP_CONV NUM_ADD_CONV) THEN
  REPEAT STRIP_TAC THEN

  (*** Express each chunk's two bytes128 input pieces as subwords of the     ***)
  (*** single 160-bit chunk word, so the per-lane VPSUBD operands compose    ***)
  (*** into a single word_subword and SIMD_SIMPLIFY stays cheap.             ***)
  RULE_ASSUM_TAC(REWRITE_RULE X86_BASE_SIMPS_D20) THEN

  (*** Symbolic execution: simplify each block's lanes, then fold the just- ***)
  (*** computed YMM0 into atomic zunpack19 lanes before it is stored so the  ***)
  (*** store and subsequent steps stay cheap.                               ***)
  MAP_EVERY (fun n ->
    X86_STEPS_TAC MLDSA_POLYZ_UNPACK_19_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC [] THEN
    ZUNPACK19_FOLD_TAC) (1--276) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Fold each 256-bit store into 8 atomic zunpack19 lanes ***)
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(RAND_CONV
     (ZPRE19_FOLD_CONV THENC REWRITE_CONV[ZUNPACK19_CORRECT])))) THEN

  (*** Establish the 32 sublist-length facts the CASES rewrites need ***)
  MAP_EVERY (fun i -> SUBGOAL_THEN
    (subst [mk_small_numeral (8 * i), `i:num`]
      `LENGTH (SUB_LIST (i, 8) (l : (20 word) list)) = 8`) ASSUME_TAC
    THENL [ASM_REWRITE_TAC [LENGTH_SUB_LIST] THEN NUM_REDUCE_TAC; ALL_TAC])
    (0 -- 31) THEN

  (*** Express the spec RHS as 32 chunks and split the 1024-byte output read   ***)
  (*** into 32 matching 256-bit conjuncts.                                     ***)
  SUBGOAL_THEN `LENGTH(MAP zunpack19 (l:(20 word) list)) = 256` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(MAP zunpack19 (l:(20 word) list)) = 256`
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
  ASM_SIMP_TAC[GSYM POLYZ19_STORE]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine correctness                                                    *)
(* This must be kept in sync with the CBMC specification in                  *)
(* mldsa/src/native/x86_64/src/arith_native_x86_64.h                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POLYZ_UNPACK_19_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r b (l:(20 word) list) pc stackpointer returnaddress.
        aligned 32 r /\
        ALL (nonoverlapping (word pc, LENGTH mldsa_polyz_unpack_19_tmc))
            [(r,1024)] /\
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,LENGTH mldsa_polyz_unpack_19_tmc); (b,640)] /\
        nonoverlapping (stackpointer,8) (r,1024)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_polyz_unpack_19_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  read(memory :> bytes(b,640)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read(memory :> bytes(r,1024)) s = num_of_wordlist (MAP zunpack19 l) /\
                  (!i. i < 256 ==>
                       --(&(2 EXP 19) - &1) <= ival(EL i (MAP zunpack19 l)) /\
                       ival(EL i (MAP zunpack19 l)) <= &(2 EXP 19)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_polyz_unpack_19_tmc
   MLDSA_POLYZ_UNPACK_19_CORRECT THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(20 word) list`; `i:num`] ZUNPACK19_MAP_BOUND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MLDSA_POLYZ_UNPACK_19_SUBROUTINE_CORRECT = prove
 (`!r b (l:(20 word) list) pc stackpointer returnaddress.
        aligned 32 r /\
        ALL (nonoverlapping (word pc, LENGTH mldsa_polyz_unpack_19_mc))
            [(r,1024)] /\
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,LENGTH mldsa_polyz_unpack_19_mc); (b,640)] /\
        nonoverlapping (stackpointer,8) (r,1024)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_polyz_unpack_19_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  read(memory :> bytes(b,640)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read(memory :> bytes(r,1024)) s = num_of_wordlist (MAP zunpack19 l) /\
                  (!i. i < 256 ==>
                       --(&(2 EXP 19) - &1) <= ival(EL i (MAP zunpack19 l)) /\
                       ival(EL i (MAP zunpack19 l)) <= &(2 EXP 19)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLYZ_UNPACK_19_NOIBT_SUBROUTINE_CORRECT));;
(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mldsa_polyz_unpack_19_x86" subroutine_signatures)
    (REWRITE_RULE[SOME_FLAGS] MLDSA_POLYZ_UNPACK_19_CORRECT)
    MLDSA_POLYZ_UNPACK_19_EXEC;;

let MLDSA_POLYZ_UNPACK_19_SAFE =
  REWRITE_RULE [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS]
  (time prove
   (full_spec,
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS] THEN
    PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLDSA_POLYZ_UNPACK_19_EXEC));;

let MLDSA_POLYZ_UNPACK_19_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r b (l:(20 word) list) pc stackpointer returnaddress.
          aligned 32 r /\
          ALL (nonoverlapping (word pc, LENGTH mldsa_polyz_unpack_19_tmc))
              [(r,1024)] /\
          LENGTH l = 256 /\
          ALL (nonoverlapping (r,1024))
              [(word pc,LENGTH mldsa_polyz_unpack_19_tmc); (b,640)] /\
          nonoverlapping (stackpointer,8) (r,1024)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_polyz_unpack_19_tmc /\
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
                         memaccess_inbounds e2 [b,640; r,1024; stackpointer,8]
                                               [r,1024; stackpointer,8]))
               (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_polyz_unpack_19_tmc
    MLDSA_POLYZ_UNPACK_19_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLDSA_POLYZ_UNPACK_19_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r b (l:(20 word) list) pc stackpointer returnaddress.
          aligned 32 r /\
          ALL (nonoverlapping (word pc, LENGTH mldsa_polyz_unpack_19_mc))
              [(r,1024)] /\
          LENGTH l = 256 /\
          ALL (nonoverlapping (r,1024))
              [(word pc,LENGTH mldsa_polyz_unpack_19_mc); (b,640)] /\
          nonoverlapping (stackpointer,8) (r,1024)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_polyz_unpack_19_mc /\
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
                         memaccess_inbounds e2 [b,640; r,1024; stackpointer,8]
                                               [r,1024; stackpointer,8]))
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLYZ_UNPACK_19_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let mldsa_polyz_unpack_19_windows_mc = define_from_elf
   "mldsa_polyz_unpack_19_windows_mc" "x86/mldsa/mldsa_polyz_unpack_19.obj";;

let mldsa_polyz_unpack_19_windows_tmc =
  define_trimmed "mldsa_polyz_unpack_19_windows_tmc" mldsa_polyz_unpack_19_windows_mc;;

let MLDSA_POLYZ_UNPACK_19_WINDOWS_TMC_EXEC =
  X86_MK_EXEC_RULE mldsa_polyz_unpack_19_windows_tmc;;

let MLDSA_POLYZ_UNPACK_19_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!r b (l:(20 word) list) pc stackpointer returnaddress.
        aligned 32 r /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH mldsa_polyz_unpack_19_windows_tmc); (b,640)] /\
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,LENGTH mldsa_polyz_unpack_19_windows_tmc); (b,640)] /\
        nonoverlapping (word_sub stackpointer (word 16),24) (r,1024) /\
        nonoverlapping (word pc,LENGTH mldsa_polyz_unpack_19_windows_tmc)
                       (word_sub stackpointer (word 16),16)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_polyz_unpack_19_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [r; b] s /\
                  read(memory :> bytes(b,640)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read(memory :> bytes(r,1024)) s = num_of_wordlist (MAP zunpack19 l) /\
                  (!i. i < 256 ==>
                       --(&(2 EXP 19) - &1) <= ival(EL i (MAP zunpack19 l)) /\
                       ival(EL i (MAP zunpack19 l)) <= &(2 EXP 19)))
             (MAYCHANGE [RSP] ,,
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)] ,,
              MAYCHANGE [memory :> bytes(r,1024)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC mldsa_polyz_unpack_19_windows_tmc
      mldsa_polyz_unpack_19_tmc MLDSA_POLYZ_UNPACK_19_CORRECT THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(20 word) list`; `i:num`] ZUNPACK19_MAP_BOUND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MLDSA_POLYZ_UNPACK_19_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!r b (l:(20 word) list) pc stackpointer returnaddress.
        aligned 32 r /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH mldsa_polyz_unpack_19_windows_mc); (b,640)] /\
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,LENGTH mldsa_polyz_unpack_19_windows_mc); (b,640)] /\
        nonoverlapping (word_sub stackpointer (word 16),24) (r,1024) /\
        nonoverlapping (word pc,LENGTH mldsa_polyz_unpack_19_windows_mc)
                       (word_sub stackpointer (word 16),16)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_polyz_unpack_19_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [r; b] s /\
                  read(memory :> bytes(b,640)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read(memory :> bytes(r,1024)) s = num_of_wordlist (MAP zunpack19 l) /\
                  (!i. i < 256 ==>
                       --(&(2 EXP 19) - &1) <= ival(EL i (MAP zunpack19 l)) /\
                       ival(EL i (MAP zunpack19 l)) <= &(2 EXP 19)))
             (MAYCHANGE [RSP] ,,
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)] ,,
              MAYCHANGE [memory :> bytes(r,1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLYZ_UNPACK_19_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

(* Windows safety proofs *)

let MLDSA_POLYZ_UNPACK_19_NOIBT_WINDOWS_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r b (l:(20 word) list) pc stackpointer returnaddress.
          aligned 32 r /\
          ALL (nonoverlapping (word_sub stackpointer (word 16),16))
              [(word pc,LENGTH mldsa_polyz_unpack_19_windows_tmc); (b,640)] /\
          LENGTH l = 256 /\
          ALL (nonoverlapping (r,1024))
              [(word pc,LENGTH mldsa_polyz_unpack_19_windows_tmc); (b,640)] /\
          nonoverlapping (word_sub stackpointer (word 16),24) (r,1024) /\
          nonoverlapping (word pc,LENGTH mldsa_polyz_unpack_19_windows_tmc)
                         (word_sub stackpointer (word 16),16)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_polyz_unpack_19_windows_tmc /\
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
                           [b,640; r,1024; word_sub stackpointer (word 16),24]
                           [r,1024; word_sub stackpointer (word 16),16]))
               (MAYCHANGE [RSP] ,,
                WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)] ,,
                MAYCHANGE [memory :> bytes(r,1024)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC mldsa_polyz_unpack_19_windows_tmc
    mldsa_polyz_unpack_19_tmc MLDSA_POLYZ_UNPACK_19_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLDSA_POLYZ_UNPACK_19_WINDOWS_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r b (l:(20 word) list) pc stackpointer returnaddress.
          aligned 32 r /\
          ALL (nonoverlapping (word_sub stackpointer (word 16),16))
              [(word pc,LENGTH mldsa_polyz_unpack_19_windows_mc); (b,640)] /\
          LENGTH l = 256 /\
          ALL (nonoverlapping (r,1024))
              [(word pc,LENGTH mldsa_polyz_unpack_19_windows_mc); (b,640)] /\
          nonoverlapping (word_sub stackpointer (word 16),24) (r,1024) /\
          nonoverlapping (word pc,LENGTH mldsa_polyz_unpack_19_windows_mc)
                         (word_sub stackpointer (word 16),16)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_polyz_unpack_19_windows_mc /\
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
                           [b,640; r,1024; word_sub stackpointer (word 16),24]
                           [r,1024; word_sub stackpointer (word 16),16]))
               (MAYCHANGE [RSP] ,,
                WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)] ,,
                MAYCHANGE [memory :> bytes(r,1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLYZ_UNPACK_19_NOIBT_WINDOWS_SUBROUTINE_SAFE));;
