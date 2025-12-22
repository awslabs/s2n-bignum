(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of polynomial coefficients in 12-bit chunks into a byte array.    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(* print_literal_from_elf "x86/mlkem/mlkem_frombytes.o";; *)

let mlkem_frombytes_mc =
  define_assert_from_elf "mlkem_frombytes_mc" "x86/mlkem/mlkem_frombytes.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0xff; 0x0f; 0xff; 0x0f;
                           (* MOV (% eax) (Imm32 (word 268374015)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xc5; 0xfe; 0x6f; 0x26;  (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0xfe; 0x6f; 0x6e; 0x20;
                           (* VMOVDQU (%_% ymm5) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0xfe; 0x6f; 0x76; 0x40;
                           (* VMOVDQU (%_% ymm6) (Memop Word256 (%% (rsi,64))) *)
  0xc5; 0xfe; 0x6f; 0x7e; 0x60;
                           (* VMOVDQU (%_% ymm7) (Memop Word256 (%% (rsi,96))) *)
  0xc5; 0x7e; 0x6f; 0x86; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm8) (Memop Word256 (%% (rsi,128))) *)
  0xc5; 0x7e; 0x6f; 0x8e; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm9) (Memop Word256 (%% (rsi,160))) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xdf; 0x20;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm4) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xff; 0x31;
                           (* VPERM2I128 (%_% ymm7) (%_% ymm4) (%_% ymm7) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x55; 0x46; 0xe0; 0x20;
                           (* VPERM2I128 (%_% ymm4) (%_% ymm5) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x55; 0x46; 0xc0; 0x31;
                           (* VPERM2I128 (%_% ymm8) (%_% ymm5) (%_% ymm8) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xe9; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm6) (%_% ymm9) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x4d; 0x46; 0xc9; 0x31;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm6) (%_% ymm9) (Imm8 (word 49)) *)
  0xc4; 0xc1; 0x65; 0x6c; 0xf0;
                           (* VPUNPCKLQDQ (%_% ymm6) (%_% ymm3) (%_% ymm8) *)
  0xc4; 0x41; 0x65; 0x6d; 0xc0;
                           (* VPUNPCKHQDQ (%_% ymm8) (%_% ymm3) (%_% ymm8) *)
  0xc5; 0xc5; 0x6c; 0xdd;  (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm7) (%_% ymm5) *)
  0xc5; 0xc5; 0x6d; 0xed;  (* VPUNPCKHQDQ (%_% ymm5) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xc1; 0x5d; 0x6c; 0xf9;
                           (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm4) (%_% ymm9) *)
  0xc4; 0x41; 0x5d; 0x6d; 0xc9;
                           (* VPUNPCKHQDQ (%_% ymm9) (%_% ymm4) (%_% ymm9) *)
  0xc5; 0xfe; 0x12; 0xe5;  (* VMOVSLDUP (%_% ymm4) (%_% ymm5) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm6) (%_% ymm4) (Imm8 (word 170)) *)
  0xc5; 0xcd; 0x73; 0xd6; 0x20;
                           (* VPSRLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xed; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm6) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xf7;  (* VMOVSLDUP (%_% ymm6) (%_% ymm7) *)
  0xc4; 0xe3; 0x3d; 0x02; 0xf6; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm8) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x20;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x3d; 0x02; 0xff; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm8) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x7e; 0x12; 0xc1;
                           (* VMOVSLDUP (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x43; 0x65; 0x02; 0xc0; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm3) (%_% ymm8) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x73; 0xd3; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x65; 0x02; 0xc9; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm3) (%_% ymm9) (Imm8 (word 170)) *)
  0xc5; 0xad; 0x72; 0xf7; 0x10;
                           (* VPSLLD (%_% ymm10) (%_% ymm7) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x5d; 0x0e; 0xd2; 0xaa;
                           (* VPBLENDW (%_% ymm10) (%_% ymm4) (%_% ymm10) (Imm8 (word 170)) *)
  0xc5; 0xdd; 0x72; 0xd4; 0x10;
                           (* VPSRLD (%_% ymm4) (%_% ymm4) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x5d; 0x0e; 0xff; 0xaa;
                           (* VPBLENDW (%_% ymm7) (%_% ymm4) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x5d; 0x72; 0xf0; 0x10;
                           (* VPSLLD (%_% ymm4) (%_% ymm8) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x55; 0x0e; 0xe4; 0xaa;
                           (* VPBLENDW (%_% ymm4) (%_% ymm5) (%_% ymm4) (Imm8 (word 170)) *)
  0xc5; 0xd5; 0x72; 0xd5; 0x10;
                           (* VPSRLD (%_% ymm5) (%_% ymm5) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x55; 0x0e; 0xc0; 0xaa;
                           (* VPBLENDW (%_% ymm8) (%_% ymm5) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0x72; 0xf1; 0x10;
                           (* VPSLLD (%_% ymm5) (%_% ymm9) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x4d; 0x0e; 0xed; 0xaa;
                           (* VPBLENDW (%_% ymm5) (%_% ymm6) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xcd; 0x72; 0xd6; 0x10;
                           (* VPSRLD (%_% ymm6) (%_% ymm6) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x4d; 0x0e; 0xc9; 0xaa;
                           (* VPBLENDW (%_% ymm9) (%_% ymm6) (%_% ymm9) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x25; 0x71; 0xd2; 0x0c;
                           (* VPSRLW (%_% ymm11) (%_% ymm10) (Imm8 (word 12)) *)
  0xc5; 0x9d; 0x71; 0xf7; 0x04;
                           (* VPSLLW (%_% ymm12) (%_% ymm7) (Imm8 (word 4)) *)
  0xc4; 0x41; 0x1d; 0xeb; 0xdb;
                           (* VPOR (%_% ymm11) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x2d; 0xdb; 0xd0;  (* VPAND (%_% ymm10) (%_% ymm10) (%_% ymm0) *)
  0xc5; 0x25; 0xdb; 0xd8;  (* VPAND (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xd7; 0x08;
                           (* VPSRLW (%_% ymm12) (%_% ymm7) (Imm8 (word 8)) *)
  0xc5; 0x95; 0x71; 0xf4; 0x08;
                           (* VPSLLW (%_% ymm13) (%_% ymm4) (Imm8 (word 8)) *)
  0xc4; 0x41; 0x15; 0xeb; 0xe4;
                           (* VPOR (%_% ymm12) (%_% ymm13) (%_% ymm12) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x95; 0x71; 0xd4; 0x04;
                           (* VPSRLW (%_% ymm13) (%_% ymm4) (Imm8 (word 4)) *)
  0xc5; 0x15; 0xdb; 0xe8;  (* VPAND (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0xc1; 0x0d; 0x71; 0xd0; 0x0c;
                           (* VPSRLW (%_% ymm14) (%_% ymm8) (Imm8 (word 12)) *)
  0xc5; 0x85; 0x71; 0xf5; 0x04;
                           (* VPSLLW (%_% ymm15) (%_% ymm5) (Imm8 (word 4)) *)
  0xc4; 0x41; 0x05; 0xeb; 0xf6;
                           (* VPOR (%_% ymm14) (%_% ymm15) (%_% ymm14) *)
  0xc5; 0x3d; 0xdb; 0xc0;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc5; 0x0d; 0xdb; 0xf0;  (* VPAND (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0x85; 0x71; 0xd5; 0x08;
                           (* VPSRLW (%_% ymm15) (%_% ymm5) (Imm8 (word 8)) *)
  0xc4; 0xc1; 0x75; 0x71; 0xf1; 0x08;
                           (* VPSLLW (%_% ymm1) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x41; 0x75; 0xeb; 0xff;
                           (* VPOR (%_% ymm15) (%_% ymm1) (%_% ymm15) *)
  0xc5; 0x05; 0xdb; 0xf8;  (* VPAND (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0xc1; 0x75; 0x71; 0xd1; 0x04;
                           (* VPSRLW (%_% ymm1) (%_% ymm9) (Imm8 (word 4)) *)
  0xc5; 0xf5; 0xdb; 0xc8;  (* VPAND (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc5; 0x7d; 0x7f; 0x17;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x5f; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm11) *)
  0xc5; 0x7d; 0x7f; 0x67; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm12) *)
  0xc5; 0x7d; 0x7f; 0x6f; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm13) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0xb7; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm14) *)
  0xc5; 0x7d; 0x7f; 0xbf; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm15) *)
  0xc5; 0xfd; 0x7f; 0x8f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm1) *)
  0xc5; 0xfe; 0x6f; 0xa6; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsi,192))) *)
  0xc5; 0xfe; 0x6f; 0xae; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm5) (Memop Word256 (%% (rsi,224))) *)
  0xc5; 0xfe; 0x6f; 0xb6; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm6) (Memop Word256 (%% (rsi,256))) *)
  0xc5; 0xfe; 0x6f; 0xbe; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm7) (Memop Word256 (%% (rsi,288))) *)
  0xc5; 0x7e; 0x6f; 0x86; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm8) (Memop Word256 (%% (rsi,320))) *)
  0xc5; 0x7e; 0x6f; 0x8e; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm9) (Memop Word256 (%% (rsi,352))) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xdf; 0x20;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm4) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xff; 0x31;
                           (* VPERM2I128 (%_% ymm7) (%_% ymm4) (%_% ymm7) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x55; 0x46; 0xe0; 0x20;
                           (* VPERM2I128 (%_% ymm4) (%_% ymm5) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x55; 0x46; 0xc0; 0x31;
                           (* VPERM2I128 (%_% ymm8) (%_% ymm5) (%_% ymm8) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xe9; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm6) (%_% ymm9) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x4d; 0x46; 0xc9; 0x31;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm6) (%_% ymm9) (Imm8 (word 49)) *)
  0xc4; 0xc1; 0x65; 0x6c; 0xf0;
                           (* VPUNPCKLQDQ (%_% ymm6) (%_% ymm3) (%_% ymm8) *)
  0xc4; 0x41; 0x65; 0x6d; 0xc0;
                           (* VPUNPCKHQDQ (%_% ymm8) (%_% ymm3) (%_% ymm8) *)
  0xc5; 0xc5; 0x6c; 0xdd;  (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm7) (%_% ymm5) *)
  0xc5; 0xc5; 0x6d; 0xed;  (* VPUNPCKHQDQ (%_% ymm5) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xc1; 0x5d; 0x6c; 0xf9;
                           (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm4) (%_% ymm9) *)
  0xc4; 0x41; 0x5d; 0x6d; 0xc9;
                           (* VPUNPCKHQDQ (%_% ymm9) (%_% ymm4) (%_% ymm9) *)
  0xc5; 0xfe; 0x12; 0xe5;  (* VMOVSLDUP (%_% ymm4) (%_% ymm5) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm6) (%_% ymm4) (Imm8 (word 170)) *)
  0xc5; 0xcd; 0x73; 0xd6; 0x20;
                           (* VPSRLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xed; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm6) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xf7;  (* VMOVSLDUP (%_% ymm6) (%_% ymm7) *)
  0xc4; 0xe3; 0x3d; 0x02; 0xf6; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm8) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x20;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x3d; 0x02; 0xff; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm8) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x7e; 0x12; 0xc1;
                           (* VMOVSLDUP (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x43; 0x65; 0x02; 0xc0; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm3) (%_% ymm8) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x73; 0xd3; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x65; 0x02; 0xc9; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm3) (%_% ymm9) (Imm8 (word 170)) *)
  0xc5; 0xad; 0x72; 0xf7; 0x10;
                           (* VPSLLD (%_% ymm10) (%_% ymm7) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x5d; 0x0e; 0xd2; 0xaa;
                           (* VPBLENDW (%_% ymm10) (%_% ymm4) (%_% ymm10) (Imm8 (word 170)) *)
  0xc5; 0xdd; 0x72; 0xd4; 0x10;
                           (* VPSRLD (%_% ymm4) (%_% ymm4) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x5d; 0x0e; 0xff; 0xaa;
                           (* VPBLENDW (%_% ymm7) (%_% ymm4) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x5d; 0x72; 0xf0; 0x10;
                           (* VPSLLD (%_% ymm4) (%_% ymm8) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x55; 0x0e; 0xe4; 0xaa;
                           (* VPBLENDW (%_% ymm4) (%_% ymm5) (%_% ymm4) (Imm8 (word 170)) *)
  0xc5; 0xd5; 0x72; 0xd5; 0x10;
                           (* VPSRLD (%_% ymm5) (%_% ymm5) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x55; 0x0e; 0xc0; 0xaa;
                           (* VPBLENDW (%_% ymm8) (%_% ymm5) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x55; 0x72; 0xf1; 0x10;
                           (* VPSLLD (%_% ymm5) (%_% ymm9) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x4d; 0x0e; 0xed; 0xaa;
                           (* VPBLENDW (%_% ymm5) (%_% ymm6) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xcd; 0x72; 0xd6; 0x10;
                           (* VPSRLD (%_% ymm6) (%_% ymm6) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x4d; 0x0e; 0xc9; 0xaa;
                           (* VPBLENDW (%_% ymm9) (%_% ymm6) (%_% ymm9) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x25; 0x71; 0xd2; 0x0c;
                           (* VPSRLW (%_% ymm11) (%_% ymm10) (Imm8 (word 12)) *)
  0xc5; 0x9d; 0x71; 0xf7; 0x04;
                           (* VPSLLW (%_% ymm12) (%_% ymm7) (Imm8 (word 4)) *)
  0xc4; 0x41; 0x1d; 0xeb; 0xdb;
                           (* VPOR (%_% ymm11) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x2d; 0xdb; 0xd0;  (* VPAND (%_% ymm10) (%_% ymm10) (%_% ymm0) *)
  0xc5; 0x25; 0xdb; 0xd8;  (* VPAND (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xd7; 0x08;
                           (* VPSRLW (%_% ymm12) (%_% ymm7) (Imm8 (word 8)) *)
  0xc5; 0x95; 0x71; 0xf4; 0x08;
                           (* VPSLLW (%_% ymm13) (%_% ymm4) (Imm8 (word 8)) *)
  0xc4; 0x41; 0x15; 0xeb; 0xe4;
                           (* VPOR (%_% ymm12) (%_% ymm13) (%_% ymm12) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x95; 0x71; 0xd4; 0x04;
                           (* VPSRLW (%_% ymm13) (%_% ymm4) (Imm8 (word 4)) *)
  0xc5; 0x15; 0xdb; 0xe8;  (* VPAND (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0xc1; 0x0d; 0x71; 0xd0; 0x0c;
                           (* VPSRLW (%_% ymm14) (%_% ymm8) (Imm8 (word 12)) *)
  0xc5; 0x85; 0x71; 0xf5; 0x04;
                           (* VPSLLW (%_% ymm15) (%_% ymm5) (Imm8 (word 4)) *)
  0xc4; 0x41; 0x05; 0xeb; 0xf6;
                           (* VPOR (%_% ymm14) (%_% ymm15) (%_% ymm14) *)
  0xc5; 0x3d; 0xdb; 0xc0;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc5; 0x0d; 0xdb; 0xf0;  (* VPAND (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0x85; 0x71; 0xd5; 0x08;
                           (* VPSRLW (%_% ymm15) (%_% ymm5) (Imm8 (word 8)) *)
  0xc4; 0xc1; 0x75; 0x71; 0xf1; 0x08;
                           (* VPSLLW (%_% ymm1) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x41; 0x75; 0xeb; 0xff;
                           (* VPOR (%_% ymm15) (%_% ymm1) (%_% ymm15) *)
  0xc5; 0x05; 0xdb; 0xf8;  (* VPAND (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0xc1; 0x75; 0x71; 0xd1; 0x04;
                           (* VPSRLW (%_% ymm1) (%_% ymm9) (Imm8 (word 4)) *)
  0xc5; 0xf5; 0xdb; 0xc8;  (* VPAND (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm11) *)
  0xc5; 0x7d; 0x7f; 0xa7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm12) *)
  0xc5; 0x7d; 0x7f; 0xaf; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm13) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0xb7; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm14) *)
  0xc5; 0x7d; 0x7f; 0xbf; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm15) *)
  0xc5; 0xfd; 0x7f; 0x8f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm1) *)
  0xc3                     (* RET *)
];;

let mlkem_frombytes_tmc = define_trimmed "mlkem_frombytes_tmc" mlkem_frombytes_mc;;
let mlkem_frombytes_TMC_EXEC = X86_MK_CORE_EXEC_RULE mlkem_frombytes_tmc;;

let avx_order = new_definition
  `avx_order i = 
    let half = i DIV 128 in
    let offset = i MOD 128 in
    half * 128 + 16 * (offset MOD 8) + (offset DIV 8)`;;

let permute_list = new_definition
  `permute_list l = list_of_seq (\i. EL (avx_order i) l) 256`;;

let avx_unorder = new_definition
  `avx_unorder i = 
    let half = i DIV 128 in
    let offset = i MOD 128 in
    half * 128 + 8 * (offset MOD 16) + (offset DIV 16)`;;

let unpermute_list = new_definition
  `unpermute_list l = list_of_seq (\i. EL (avx_unorder i) l) 256`;;

let AVX_ORDER_UNORDER = prove(
  `!i. i < 256 ==> avx_order (avx_unorder i) = i`,
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[avx_order; avx_unorder] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

let DIMINDEX_12 = DIMINDEX_CONV `dimindex(:12)`;;

let MLKEM_FROMBYTES_CORRECT = prove(
    `!r a (l:(12 word) list) pc.
        aligned 32 a /\
        aligned 32 r /\
        nonoverlapping (word pc, 818) (a, 384) /\
        nonoverlapping (word pc, 818) (r, 512) /\
        nonoverlapping (a, 384) (r, 512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mlkem_frombytes_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a, 384)) s = num_of_wordlist l)
             (\s. read RIP s = word (pc + 818) /\
                  (LENGTH l = 256
                   ==> read(memory :> bytes(r, 512)) s =
                       num_of_wordlist (MAP word_zx (unpermute_list l):int16 list)))
             (MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(r, 512)] ,,
              MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                         ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15])`,

  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `l:(12 word) list`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN

  (*** Globalize the length assumption via a case split ***)

  ASM_CASES_TAC `LENGTH(l:(12 word) list) = 256` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0";
    X86_SIM_TAC mlkem_frombytes_TMC_EXEC (1--147)] THEN

  (*** Restructure from 12-bit words to 256-bit chunks ***)

  SUBGOAL_THEN
   `read (memory :> bytes(a,dimindex(:32) * 12)) s0 = num_of_wordlist (l:(12 word)list)`
  MP_TAC THENL [ASM_REWRITE_TAC[DIMINDEX_32; ARITH]; ALL_TAC] THEN
  REWRITE_TAC[GSYM NUM_OF_WORDLIST_FROM_MEMORY] THEN
  SUBGOAL_THEN
   `num_of_wordlist (l:(12 word)list) =
    num_of_wordlist
     (list_of_seq
        (\j. let i = j DIV 3 and r = j MOD 3 in
             if r = 0 then word_zx(EL (2 * i) l):byte
             else if r = 2 then word_subword (EL(2 * i + 1) l) (4,8)
             else word_join (word_subword (EL(2 * i + 1) l) (0,4):nybble)
                            (word_subword (EL(2 * i) l) (8,4):nybble))
        384)`
  SUBST1_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LENGTH_EQ_LIST_OF_SEQ]) THEN
    CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
    DISCH_THEN SUBST1_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[num_of_wordlist; VAL; DIMINDEX_8; DIMINDEX_12] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ABBREV_TAC `twae = &2:real` THEN REAL_ARITH_TAC;
    CONV_TAC(LAND_CONV(RAND_CONV
     (ONCE_DEPTH_CONV let_CONV THENC
      ONCE_DEPTH_CONV LIST_OF_SEQ_CONV THENC
      NUM_REDUCE_CONV)))] THEN
  CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV WORDLIST_FROM_MEMORY_CONV))) THEN
  REPLICATE_TAC 5 (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
        [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [pair_wordlist] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_EQ] THEN STRIP_TAC THEN

  (*** Simulate and simplify ***)

  MAP_EVERY (fun n -> X86_STEPS_TAC mlkem_frombytes_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[])
            (1--147) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Final reasoning ***)

  SUBGOAL_THEN `512 = dimindex(:32) * 16` SUBST1_TAC THENL
   [REWRITE_TAC[DIMINDEX_32; ARITH]; 
    REWRITE_TAC[GSYM NUM_OF_WORDLIST_FROM_MEMORY]] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LENGTH_EQ_LIST_OF_SEQ]) THEN
  CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[unpermute_list] THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[avx_unorder; LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[MAP] THEN
  REPLICATE_TAC 4 (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
        [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [pair_wordlist] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_EQ] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let MLKEM_FROMBYTES_NOIBT_SUBROUTINE_CORRECT = prove(
    `!r a (l:(12 word) list) pc.
        aligned 32 a /\
        aligned 32 r /\
        nonoverlapping (word pc, LENGTH mlkem_frombytes_tmc) (a, 384) /\
        nonoverlapping (word pc, LENGTH mlkem_frombytes_tmc) (r, 512) /\
        nonoverlapping (a, 384) (r, 512) /\
        nonoverlapping (stackpointer, 8) (r, 512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_frombytes_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a, 384)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (LENGTH l = 256
                   ==> read(memory :> bytes(r, 512)) s =
                       num_of_wordlist (MAP word_zx (unpermute_list l):int16 list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [RSP] ,, MAYCHANGE [memory :> bytes(r, 512)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_frombytes_tmc MLKEM_FROMBYTES_CORRECT);;

let MLKEM_FROMBYTES_SUBROUTINE_CORRECT = prove(
    `!r a (l:(12 word) list) pc.
        aligned 32 a /\
        aligned 32 r /\
        nonoverlapping (word pc, LENGTH mlkem_frombytes_mc) (a, 384) /\
        nonoverlapping (word pc, LENGTH mlkem_frombytes_mc) (r, 512) /\
        nonoverlapping (a, 384) (r, 512) /\
        nonoverlapping (stackpointer, 8) (r, 512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_frombytes_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a, 384)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (LENGTH l = 256
                   ==> read(memory :> bytes(r, 512)) s =
                       num_of_wordlist (MAP word_zx (unpermute_list l):int16 list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [RSP] ,, MAYCHANGE [memory :> bytes(r, 512)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_FROMBYTES_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)
(* print_literal_from_elf "x86/mlkem/mlkem_frombytes.obj";; *)

let mlkem_frombytes_windows_mc = define_from_elf
    "mlkem_frombytes_windows_mc" "x86/mlkem/mlkem_frombytes.obj";;

let mlkem_frombytes_windows_tmc = define_trimmed
    "mlkem_frombytes_windows_tmc" mlkem_frombytes_windows_mc;;

let mlkem_frombytes_windows_tmc_EXEC = X86_MK_EXEC_RULE mlkem_frombytes_windows_tmc;;

let MLKEM_FROMBYTES_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove(
    `!r a (l:(12 word) list) pc stackpointer returnaddress.
        aligned 32 a /\
        aligned 32 r /\
        nonoverlapping (word pc, LENGTH mlkem_frombytes_windows_tmc) (a, 384) /\
        nonoverlapping (word pc, LENGTH mlkem_frombytes_windows_tmc) (r, 512) /\
        nonoverlapping (a, 384) (r, 512) /\
        nonoverlapping (word_sub stackpointer (word 176), 184) (a, 384) /\
        nonoverlapping (word_sub stackpointer (word 176), 184) (r, 512) /\
        nonoverlapping (word pc, LENGTH mlkem_frombytes_windows_tmc)
                       (word_sub stackpointer (word 176), 176)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_frombytes_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a, 384)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (LENGTH l = 256
                   ==> read(memory :> bytes(r, 512)) s =
                       num_of_wordlist (MAP word_zx (unpermute_list l):int16 list)))
              (MAYCHANGE [RSP] ,,
               WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(word_sub stackpointer (word 176), 176)] ,,
               MAYCHANGE [memory :> bytes(r, 512)])`,
  REPLICATE_TAC 4 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 176 THEN
  REPEAT GEN_TAC THEN

  REWRITE_TAC[fst mlkem_frombytes_windows_tmc_EXEC] THEN
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
  ENSURES_PRESERVED_TAC "init_xmm13" `ZMM13 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm14" `ZMM14 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm15" `ZMM15 :> bottomhalf :> bottomhalf` THEN

  REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
  REWRITE_TAC(map GSYM
    [YMM6;YMM7;YMM8;YMM9;YMM10;YMM11;YMM12;YMM13;YMM14;YMM15]) THEN

  GHOST_INTRO_TAC `init_ymm6:int256` `read YMM6` THEN
  GHOST_INTRO_TAC `init_ymm7:int256` `read YMM7` THEN
  GHOST_INTRO_TAC `init_ymm8:int256` `read YMM8` THEN
  GHOST_INTRO_TAC `init_ymm9:int256` `read YMM9` THEN
  GHOST_INTRO_TAC `init_ymm10:int256` `read YMM10` THEN
  GHOST_INTRO_TAC `init_ymm11:int256` `read YMM11` THEN
  GHOST_INTRO_TAC `init_ymm12:int256` `read YMM12` THEN
  GHOST_INTRO_TAC `init_ymm13:int256` `read YMM13` THEN
  GHOST_INTRO_TAC `init_ymm14:int256` `read YMM14` THEN
  GHOST_INTRO_TAC `init_ymm15:int256` `read YMM15` THEN

  GLOBALIZE_PRECONDITION_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC mlkem_frombytes_windows_tmc_EXEC (1--15) THEN

  MP_TAC(SPECL [`r:int64`; `a:int64`; `l:(12 word) list`; `pc + 92`]
    MLKEM_FROMBYTES_CORRECT) THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN

  X86_BIGSTEP_TAC mlkem_frombytes_windows_tmc_EXEC "s16" THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
     (BYTES_LOADED_SUBPROGRAM_RULE mlkem_frombytes_windows_tmc
     (REWRITE_RULE[BUTLAST_CLAUSES]
      (AP_TERM `BUTLAST:byte list->byte list` mlkem_frombytes_tmc))
     92));
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN

  MAP_EVERY ABBREV_TAC
   [`ymm6_epilog = read YMM6 s16`;
    `ymm7_epilog = read YMM7 s16`;
    `ymm8_epilog = read YMM8 s16`;
    `ymm9_epilog = read YMM9 s16`;
    `ymm10_epilog = read YMM10 s16`;
    `ymm11_epilog = read YMM11 s16`;
    `ymm12_epilog = read YMM12 s16`;
    `ymm13_epilog = read YMM13 s16`;
    `ymm14_epilog = read YMM14 s16`;
    `ymm15_epilog = read YMM15 s16`] THEN

  X86_STEPS_TAC mlkem_frombytes_windows_tmc_EXEC (17--30) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let MLKEM_FROMBYTES_WINDOWS_SUBROUTINE_CORRECT = prove(
    `!r a (l:(12 word) list) pc stackpointer returnaddress.
        aligned 32 a /\
        aligned 32 r /\
        nonoverlapping (word pc, LENGTH mlkem_frombytes_windows_mc) (a, 384) /\
        nonoverlapping (word pc, LENGTH mlkem_frombytes_windows_mc) (r, 512) /\
        nonoverlapping (a, 384) (r, 512) /\
        nonoverlapping (word_sub stackpointer (word 176), 184) (a, 384) /\
        nonoverlapping (word_sub stackpointer (word 176), 184) (r, 512) /\
        nonoverlapping (word pc, LENGTH mlkem_frombytes_windows_mc)
                       (word_sub stackpointer (word 176), 176)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_frombytes_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a, 384)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (LENGTH l = 256
                   ==> read(memory :> bytes(r, 512)) s =
                       num_of_wordlist (MAP word_zx (unpermute_list l):int16 list)))
              (MAYCHANGE [RSP] ,,
               WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(word_sub stackpointer (word 176), 176)] ,,
               MAYCHANGE [memory :> bytes(r, 512)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_FROMBYTES_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;
