(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of polynomial coefficients in 12-bit chunks into a byte array.    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(* print_literal_from_elf "x86/mlkem/mlkem_tobytes.o";; *)

let mlkem_tobytes_mc =
  define_assert_from_elf "mlkem_tobytes_mc" "x86/mlkem/mlkem_tobytes.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x01; 0x0d; 0x01; 0x0d;
                           (* MOV (% eax) (Imm32 (word 218172673)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xc5; 0xfd; 0x6f; 0x2e;  (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0xfd; 0x6f; 0x76; 0x20;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0xfd; 0x6f; 0x7e; 0x40;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,64))) *)
  0xc5; 0x7d; 0x6f; 0x46; 0x60;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,96))) *)
  0xc5; 0x7d; 0x6f; 0x8e; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,128))) *)
  0xc5; 0x7d; 0x6f; 0x96; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rsi,160))) *)
  0xc5; 0x7d; 0x6f; 0x9e; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rsi,192))) *)
  0xc5; 0x7d; 0x6f; 0xa6; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rsi,224))) *)
  0xc5; 0xdd; 0x71; 0xf6; 0x0c;
                           (* VPSLLW (%_% ymm4) (%_% ymm6) (Imm8 (word 12)) *)
  0xc5; 0xd5; 0xeb; 0xe4;  (* VPOR (%_% ymm4) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xd5; 0x71; 0xd6; 0x04;
                           (* VPSRLW (%_% ymm5) (%_% ymm6) (Imm8 (word 4)) *)
  0xc5; 0xcd; 0x71; 0xf7; 0x08;
                           (* VPSLLW (%_% ymm6) (%_% ymm7) (Imm8 (word 8)) *)
  0xc5; 0xcd; 0xeb; 0xed;  (* VPOR (%_% ymm5) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd7; 0x08;
                           (* VPSRLW (%_% ymm6) (%_% ymm7) (Imm8 (word 8)) *)
  0xc4; 0xc1; 0x45; 0x71; 0xf0; 0x04;
                           (* VPSLLW (%_% ymm7) (%_% ymm8) (Imm8 (word 4)) *)
  0xc5; 0xc5; 0xeb; 0xf6;  (* VPOR (%_% ymm6) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0x71; 0xf2; 0x0c;
                           (* VPSLLW (%_% ymm7) (%_% ymm10) (Imm8 (word 12)) *)
  0xc5; 0xb5; 0xeb; 0xff;  (* VPOR (%_% ymm7) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xd2; 0x04;
                           (* VPSRLW (%_% ymm8) (%_% ymm10) (Imm8 (word 4)) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf3; 0x08;
                           (* VPSLLW (%_% ymm9) (%_% ymm11) (Imm8 (word 8)) *)
  0xc4; 0x41; 0x35; 0xeb; 0xc0;
                           (* VPOR (%_% ymm8) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd3; 0x08;
                           (* VPSRLW (%_% ymm9) (%_% ymm11) (Imm8 (word 8)) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xf4; 0x04;
                           (* VPSLLW (%_% ymm10) (%_% ymm12) (Imm8 (word 4)) *)
  0xc4; 0x41; 0x2d; 0xeb; 0xc9;
                           (* VPOR (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xe5; 0x72; 0xf5; 0x10;
                           (* VPSLLD (%_% ymm3) (%_% ymm5) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x5d; 0x0e; 0xdb; 0xaa;
                           (* VPBLENDW (%_% ymm3) (%_% ymm4) (%_% ymm3) (Imm8 (word 170)) *)
  0xc5; 0xdd; 0x72; 0xd4; 0x10;
                           (* VPSRLD (%_% ymm4) (%_% ymm4) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x5d; 0x0e; 0xed; 0xaa;
                           (* VPBLENDW (%_% ymm5) (%_% ymm4) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xdd; 0x72; 0xf7; 0x10;
                           (* VPSLLD (%_% ymm4) (%_% ymm7) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x4d; 0x0e; 0xe4; 0xaa;
                           (* VPBLENDW (%_% ymm4) (%_% ymm6) (%_% ymm4) (Imm8 (word 170)) *)
  0xc5; 0xcd; 0x72; 0xd6; 0x10;
                           (* VPSRLD (%_% ymm6) (%_% ymm6) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x4d; 0x0e; 0xff; 0xaa;
                           (* VPBLENDW (%_% ymm7) (%_% ymm6) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x4d; 0x72; 0xf1; 0x10;
                           (* VPSLLD (%_% ymm6) (%_% ymm9) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x3d; 0x0e; 0xf6; 0xaa;
                           (* VPBLENDW (%_% ymm6) (%_% ymm8) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0x72; 0xd0; 0x10;
                           (* VPSRLD (%_% ymm8) (%_% ymm8) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x3d; 0x0e; 0xc9; 0xaa;
                           (* VPBLENDW (%_% ymm9) (%_% ymm8) (%_% ymm9) (Imm8 (word 170)) *)
  0xc5; 0x7e; 0x12; 0xc4;  (* VMOVSLDUP (%_% ymm8) (%_% ymm4) *)
  0xc4; 0x43; 0x65; 0x02; 0xc0; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm3) (%_% ymm8) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x73; 0xd3; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x65; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm3) (%_% ymm4) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xdd;  (* VMOVSLDUP (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm6) (%_% ymm3) (Imm8 (word 170)) *)
  0xc5; 0xcd; 0x73; 0xd6; 0x20;
                           (* VPSRLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xed; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm6) (%_% ymm5) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xf1;
                           (* VMOVSLDUP (%_% ymm6) (%_% ymm9) *)
  0xc4; 0xe3; 0x45; 0x02; 0xf6; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm7) (%_% ymm6) (Imm8 (word 170)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x02; 0xc9; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm7) (%_% ymm9) (Imm8 (word 170)) *)
  0xc5; 0xbd; 0x6c; 0xfb;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0xbd; 0x6d; 0xdb;  (* VPUNPCKHQDQ (%_% ymm3) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x4d; 0x6c; 0xc4;  (* VPUNPCKLQDQ (%_% ymm8) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0x6d; 0xe4;  (* VPUNPCKHQDQ (%_% ymm4) (%_% ymm6) (%_% ymm4) *)
  0xc4; 0xc1; 0x55; 0x6c; 0xf1;
                           (* VPUNPCKLQDQ (%_% ymm6) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x55; 0x6d; 0xc9;
                           (* VPUNPCKHQDQ (%_% ymm9) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc3; 0x45; 0x46; 0xe8; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm7) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x46; 0xc0; 0x31;
                           (* VPERM2I128 (%_% ymm8) (%_% ymm7) (%_% ymm8) (Imm8 (word 49)) *)
  0xc4; 0xe3; 0x4d; 0x46; 0xfb; 0x20;
                           (* VPERM2I128 (%_% ymm7) (%_% ymm6) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x4d; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm6) (%_% ymm3) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x5d; 0x46; 0xf1; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm4) (%_% ymm9) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x5d; 0x46; 0xc9; 0x31;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm4) (%_% ymm9) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x7f; 0x2f;  (* VMOVDQU (Memop Word256 (%% (rdi,0))) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0x7f; 0x20;
                           (* VMOVDQU (Memop Word256 (%% (rdi,32))) (%_% ymm7) *)
  0xc5; 0xfe; 0x7f; 0x77; 0x40;
                           (* VMOVDQU (Memop Word256 (%% (rdi,64))) (%_% ymm6) *)
  0xc5; 0x7e; 0x7f; 0x47; 0x60;
                           (* VMOVDQU (Memop Word256 (%% (rdi,96))) (%_% ymm8) *)
  0xc5; 0xfe; 0x7f; 0x9f; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,128))) (%_% ymm3) *)
  0xc5; 0x7e; 0x7f; 0x8f; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,160))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0xae; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rsi,256))) *)
  0xc5; 0xfd; 0x6f; 0xb6; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,288))) *)
  0xc5; 0xfd; 0x6f; 0xbe; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,320))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,352))) *)
  0xc5; 0x7d; 0x6f; 0x8e; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,384))) *)
  0xc5; 0x7d; 0x6f; 0x96; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rsi,416))) *)
  0xc5; 0x7d; 0x6f; 0x9e; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rsi,448))) *)
  0xc5; 0x7d; 0x6f; 0xa6; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rsi,480))) *)
  0xc5; 0xdd; 0x71; 0xf6; 0x0c;
                           (* VPSLLW (%_% ymm4) (%_% ymm6) (Imm8 (word 12)) *)
  0xc5; 0xd5; 0xeb; 0xe4;  (* VPOR (%_% ymm4) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xd5; 0x71; 0xd6; 0x04;
                           (* VPSRLW (%_% ymm5) (%_% ymm6) (Imm8 (word 4)) *)
  0xc5; 0xcd; 0x71; 0xf7; 0x08;
                           (* VPSLLW (%_% ymm6) (%_% ymm7) (Imm8 (word 8)) *)
  0xc5; 0xcd; 0xeb; 0xed;  (* VPOR (%_% ymm5) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd7; 0x08;
                           (* VPSRLW (%_% ymm6) (%_% ymm7) (Imm8 (word 8)) *)
  0xc4; 0xc1; 0x45; 0x71; 0xf0; 0x04;
                           (* VPSLLW (%_% ymm7) (%_% ymm8) (Imm8 (word 4)) *)
  0xc5; 0xc5; 0xeb; 0xf6;  (* VPOR (%_% ymm6) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0x71; 0xf2; 0x0c;
                           (* VPSLLW (%_% ymm7) (%_% ymm10) (Imm8 (word 12)) *)
  0xc5; 0xb5; 0xeb; 0xff;  (* VPOR (%_% ymm7) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xd2; 0x04;
                           (* VPSRLW (%_% ymm8) (%_% ymm10) (Imm8 (word 4)) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf3; 0x08;
                           (* VPSLLW (%_% ymm9) (%_% ymm11) (Imm8 (word 8)) *)
  0xc4; 0x41; 0x35; 0xeb; 0xc0;
                           (* VPOR (%_% ymm8) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd3; 0x08;
                           (* VPSRLW (%_% ymm9) (%_% ymm11) (Imm8 (word 8)) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xf4; 0x04;
                           (* VPSLLW (%_% ymm10) (%_% ymm12) (Imm8 (word 4)) *)
  0xc4; 0x41; 0x2d; 0xeb; 0xc9;
                           (* VPOR (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xe5; 0x72; 0xf5; 0x10;
                           (* VPSLLD (%_% ymm3) (%_% ymm5) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x5d; 0x0e; 0xdb; 0xaa;
                           (* VPBLENDW (%_% ymm3) (%_% ymm4) (%_% ymm3) (Imm8 (word 170)) *)
  0xc5; 0xdd; 0x72; 0xd4; 0x10;
                           (* VPSRLD (%_% ymm4) (%_% ymm4) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x5d; 0x0e; 0xed; 0xaa;
                           (* VPBLENDW (%_% ymm5) (%_% ymm4) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xdd; 0x72; 0xf7; 0x10;
                           (* VPSLLD (%_% ymm4) (%_% ymm7) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x4d; 0x0e; 0xe4; 0xaa;
                           (* VPBLENDW (%_% ymm4) (%_% ymm6) (%_% ymm4) (Imm8 (word 170)) *)
  0xc5; 0xcd; 0x72; 0xd6; 0x10;
                           (* VPSRLD (%_% ymm6) (%_% ymm6) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x4d; 0x0e; 0xff; 0xaa;
                           (* VPBLENDW (%_% ymm7) (%_% ymm6) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x4d; 0x72; 0xf1; 0x10;
                           (* VPSLLD (%_% ymm6) (%_% ymm9) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x3d; 0x0e; 0xf6; 0xaa;
                           (* VPBLENDW (%_% ymm6) (%_% ymm8) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0x72; 0xd0; 0x10;
                           (* VPSRLD (%_% ymm8) (%_% ymm8) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x3d; 0x0e; 0xc9; 0xaa;
                           (* VPBLENDW (%_% ymm9) (%_% ymm8) (%_% ymm9) (Imm8 (word 170)) *)
  0xc5; 0x7e; 0x12; 0xc4;  (* VMOVSLDUP (%_% ymm8) (%_% ymm4) *)
  0xc4; 0x43; 0x65; 0x02; 0xc0; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm3) (%_% ymm8) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x73; 0xd3; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x65; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm3) (%_% ymm4) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xdd;  (* VMOVSLDUP (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm6) (%_% ymm3) (Imm8 (word 170)) *)
  0xc5; 0xcd; 0x73; 0xd6; 0x20;
                           (* VPSRLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xed; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm6) (%_% ymm5) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xf1;
                           (* VMOVSLDUP (%_% ymm6) (%_% ymm9) *)
  0xc4; 0xe3; 0x45; 0x02; 0xf6; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm7) (%_% ymm6) (Imm8 (word 170)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x02; 0xc9; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm7) (%_% ymm9) (Imm8 (word 170)) *)
  0xc5; 0xbd; 0x6c; 0xfb;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0xbd; 0x6d; 0xdb;  (* VPUNPCKHQDQ (%_% ymm3) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x4d; 0x6c; 0xc4;  (* VPUNPCKLQDQ (%_% ymm8) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0x6d; 0xe4;  (* VPUNPCKHQDQ (%_% ymm4) (%_% ymm6) (%_% ymm4) *)
  0xc4; 0xc1; 0x55; 0x6c; 0xf1;
                           (* VPUNPCKLQDQ (%_% ymm6) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x55; 0x6d; 0xc9;
                           (* VPUNPCKHQDQ (%_% ymm9) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc3; 0x45; 0x46; 0xe8; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm7) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x46; 0xc0; 0x31;
                           (* VPERM2I128 (%_% ymm8) (%_% ymm7) (%_% ymm8) (Imm8 (word 49)) *)
  0xc4; 0xe3; 0x4d; 0x46; 0xfb; 0x20;
                           (* VPERM2I128 (%_% ymm7) (%_% ymm6) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x4d; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm6) (%_% ymm3) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x5d; 0x46; 0xf1; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm4) (%_% ymm9) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x5d; 0x46; 0xc9; 0x31;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm4) (%_% ymm9) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x7f; 0xaf; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,192))) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0xbf; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,224))) (%_% ymm7) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,256))) (%_% ymm6) *)
  0xc5; 0x7e; 0x7f; 0x87; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,288))) (%_% ymm8) *)
  0xc5; 0xfe; 0x7f; 0x9f; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,320))) (%_% ymm3) *)
  0xc5; 0x7e; 0x7f; 0x8f; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,352))) (%_% ymm9) *)
  0xc3                     (* RET *)
];;

let mlkem_tobytes_tmc = define_trimmed "mlkem_tobytes_tmc" mlkem_tobytes_mc;;
let mlkem_tobytes_TMC_EXEC = X86_MK_CORE_EXEC_RULE mlkem_tobytes_tmc;;

let avx_order = new_definition
  `avx_order i = 
    let half = i DIV 128 in
    let offset = i MOD 128 in
    half * 128 + 16 * (offset MOD 8) + (offset DIV 8)`;;

let permute_list = new_definition
  `permute_list l = list_of_seq (\i. EL (avx_order i) l) 256`;;

let BIT_BOUND = BITBLAST_RULE
  `!x:int16. val x < 3329 ==> ~bit 12 x /\ ~bit 13 x /\ ~bit 14 x /\ ~bit 15 x`;;

let MLKEM_TOBYTES_CORRECT = prove(
  `!r a (l:int16 list) pc.
        aligned 32 a /\
        aligned 32 r /\
        nonoverlapping (word pc, 764) (a, 512) /\
        nonoverlapping (word pc, 764) (r, 384) /\
        nonoverlapping (a, 512) (r, 384)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mlkem_tobytes_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a, 512)) s = num_of_wordlist l)
             (\s. read RIP s = word (pc + 764) /\
                  (LENGTH l = 256
                   ==> (!i. i < LENGTH l ==> val(EL i l) < 3329)
                   ==> read(memory :> bytes(r, 384)) s =
                       num_of_wordlist (MAP word_zx (permute_list l):(12 word)list)))
             (MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(r, 384)] ,,
              MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                         ZMM8; ZMM9; ZMM10; ZMM11; ZMM12])`,

  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `l:int16 list`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `init_ymm1:int256` `read YMM1` THEN

  ASM_CASES_TAC `LENGTH(l:int16 list) = 256` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0";
    X86_SIM_TAC mlkem_tobytes_TMC_EXEC (1--135)] THEN

  UNDISCH_TAC
   `read(memory :> bytes(a,512)) s0 = num_of_wordlist(l:int16 list)` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
   [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV LIST_OF_SEQ_CONV))) THEN
  REWRITE_TAC[] THEN
  REPLICATE_TAC 4
   (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
         [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES256_WBYTES] THEN STRIP_TAC THEN

  MAP_EVERY (fun n ->
    X86_STEPS_TAC mlkem_tobytes_TMC_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC[])
   (1--135) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
  CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
  CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
  check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN

  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONV_RULE EXPAND_CASES_CONV) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC (fun th -> try MATCH_MP BIT_BOUND th with Failure _ -> th) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN

  REWRITE_TAC[ARITH_RULE `384 = 8 * 48`] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN
  REWRITE_TAC[permute_list; avx_order] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(funpow 3 RAND_CONV (LIST_OF_SEQ_CONV)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MAP] THEN
  REWRITE_TAC[num_of_wordlist; VAL] THEN

  (*** Now more or less brute-force except avoid creating big numbers ***)

  REWRITE_TAC[bignum_of_wordlist; VAL] THEN
  POP_ASSUM_LIST (fun ths ->
  let dominated = filter (fun th -> 
    can (find_term (fun t -> try fst(dest_const t) = "bit" with _ -> false)) (concl th)) ths in
  MAP_EVERY ASSUME_TAC (rev dominated)) THEN
  CONV_TAC(TOP_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV
   (BIT_WORD_CONV ORELSEC
    GEN_REWRITE_CONV I [BITVAL_CLAUSES; OR_CLAUSES; AND_CLAUSES])) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ABBREV_TAC `twae = &2:real` THEN REAL_ARITH_TAC
);;

let MLKEM_TOBYTES_NOIBT_SUBROUTINE_CORRECT = prove
(`!r a (l:int16 list) pc.
        aligned 32 a /\
        aligned 32 r /\
        nonoverlapping (word pc, LENGTH mlkem_tobytes_tmc) (a, 512) /\
        nonoverlapping (word pc, LENGTH mlkem_tobytes_tmc) (r, 384) /\
        nonoverlapping (a, 512) (r, 384) /\
        nonoverlapping (stackpointer, 8) (r, 512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_tobytes_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a, 512)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (LENGTH l = 256
                   ==> (!i. i < LENGTH l ==> val(EL i l) < 3329)
                   ==> read(memory :> bytes(r, 384)) s =
                       num_of_wordlist (MAP word_zx (permute_list l):(12 word)list)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(r, 384)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_tobytes_tmc MLKEM_TOBYTES_CORRECT);;

let MLKEM_TOBYTES_SUBROUTINE_CORRECT = prove
(`!r a (l:int16 list) pc.
        aligned 32 a /\
        aligned 32 r /\
        nonoverlapping (word pc, LENGTH mlkem_tobytes_mc) (a, 512) /\
        nonoverlapping (word pc, LENGTH mlkem_tobytes_mc) (r, 384) /\
        nonoverlapping (a, 512) (r, 384) /\
        nonoverlapping (stackpointer, 8) (r, 512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_tobytes_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a, 512)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (LENGTH l = 256
                   ==> (!i. i < LENGTH l ==> val(EL i l) < 3329)
                   ==> read(memory :> bytes(r, 384)) s =
                       num_of_wordlist (MAP word_zx (permute_list l):(12 word)list)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(r, 384)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_TOBYTES_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)
(* print_literal_from_elf "x86/mlkem/mlkem_tobytes.obj";; *)

let mlkem_tobytes_windows_mc = define_from_elf
    "mlkem_tobytes_windows_mc" "x86/mlkem/mlkem_tobytes.obj";;

let mlkem_tobytes_windows_tmc = define_trimmed
    "mlkem_tobytes_windows_tmc" mlkem_tobytes_windows_mc;;

let mlkem_tobytes_windows_tmc_EXEC = X86_MK_EXEC_RULE mlkem_tobytes_windows_tmc;;

let MLKEM_TOBYTES_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
(`!r a (l:int16 list) pc stackpointer returnaddress.
        aligned 32 a /\
        aligned 32 r /\
        nonoverlapping (word pc, LENGTH mlkem_tobytes_windows_tmc) (a, 512) /\
        nonoverlapping (word pc, LENGTH mlkem_tobytes_windows_tmc) (r, 384) /\
        nonoverlapping (a, 512) (r, 384) /\
        nonoverlapping (word_sub stackpointer (word 128), 136) (a, 512) /\
        nonoverlapping (word_sub stackpointer (word 128), 136) (r, 384) /\
        nonoverlapping (word pc, LENGTH mlkem_tobytes_windows_tmc)
                       (word_sub stackpointer (word 128), 128)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_tobytes_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a, 512)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (LENGTH l = 256
                   ==> (!i. i < LENGTH l ==> val(EL i l) < 3329)
                   ==> read(memory :> bytes(r, 384)) s =
                       num_of_wordlist (MAP word_zx (permute_list l):(12 word)list)))
              (MAYCHANGE [RSP] ,,
               WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(word_sub stackpointer (word 128), 128)] ,,
               MAYCHANGE [memory :> bytes(r, 384)])`,
  REPLICATE_TAC 4 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 128 THEN
  REPEAT GEN_TAC THEN

  REWRITE_TAC[fst mlkem_tobytes_windows_tmc_EXEC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[WINDOWS_C_ARGUMENTS] THEN
  REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN

  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
  ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
  ENSURES_PRESERVED_TAC "init_xmm6" `ZMM6 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm7" `ZMM7 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm8" `ZMM8 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm9" `ZMM9 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm10" `ZMM10 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm11" `ZMM11 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm12" `ZMM12 :> bottomhalf :> bottomhalf` THEN

  REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
  REWRITE_TAC(map GSYM
    [YMM6;YMM7;YMM8;YMM9;YMM10;YMM11;YMM12]) THEN

  GHOST_INTRO_TAC `init_ymm6:int256` `read YMM6` THEN
  GHOST_INTRO_TAC `init_ymm7:int256` `read YMM7` THEN
  GHOST_INTRO_TAC `init_ymm8:int256` `read YMM8` THEN
  GHOST_INTRO_TAC `init_ymm9:int256` `read YMM9` THEN
  GHOST_INTRO_TAC `init_ymm10:int256` `read YMM10` THEN
  GHOST_INTRO_TAC `init_ymm11:int256` `read YMM11` THEN
  GHOST_INTRO_TAC `init_ymm12:int256` `read YMM12` THEN

  GLOBALIZE_PRECONDITION_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC mlkem_tobytes_windows_tmc_EXEC (1--12) THEN

  MP_TAC(SPECL [`r:int64`; `a:int64`; `l:int16 list`; `pc + 62`]
    MLKEM_TOBYTES_CORRECT) THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN

  X86_BIGSTEP_TAC mlkem_tobytes_windows_tmc_EXEC "s13" THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
     (BYTES_LOADED_SUBPROGRAM_RULE mlkem_tobytes_windows_tmc
     (REWRITE_RULE[BUTLAST_CLAUSES]
      (AP_TERM `BUTLAST:byte list->byte list` mlkem_tobytes_tmc))
     62));
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN

  MAP_EVERY ABBREV_TAC
   [`ymm6_epilog = read YMM6 s13`;
    `ymm7_epilog = read YMM7 s13`;
    `ymm8_epilog = read YMM8 s13`;
    `ymm9_epilog = read YMM9 s13`;
    `ymm10_epilog = read YMM10 s13`;
    `ymm11_epilog = read YMM11 s13`;
    `ymm12_epilog = read YMM12 s13`] THEN

  X86_STEPS_TAC mlkem_tobytes_windows_tmc_EXEC (14--24) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let MLKEM_TOBYTES_WINDOWS_SUBROUTINE_CORRECT = prove
(`!r a (l:int16 list) pc stackpointer returnaddress.
        aligned 32 a /\
        aligned 32 r /\
        nonoverlapping (word pc, LENGTH mlkem_tobytes_windows_mc) (a, 512) /\
        nonoverlapping (word pc, LENGTH mlkem_tobytes_windows_mc) (r, 384) /\
        nonoverlapping (a, 512) (r, 384) /\
        nonoverlapping (word_sub stackpointer (word 128), 136) (a, 512) /\
        nonoverlapping (word_sub stackpointer (word 128), 136) (r, 384) /\
        nonoverlapping (word pc, LENGTH mlkem_tobytes_windows_mc)
                       (word_sub stackpointer (word 128), 128)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_tobytes_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a, 512)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (LENGTH l = 256
                   ==> (!i. i < LENGTH l ==> val(EL i l) < 3329)
                   ==> read(memory :> bytes(r, 384)) s =
                       num_of_wordlist (MAP word_zx (permute_list l):(12 word)list)))
              (MAYCHANGE [RSP] ,,
               WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(word_sub stackpointer (word 128), 128)] ,,
               MAYCHANGE [memory :> bytes(r, 384)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_TOBYTES_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;
