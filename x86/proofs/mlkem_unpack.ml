(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of polynomial coefficients in 12-bit chunks into a byte array.    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(* print_literal_from_elf "x86/mlkem/mlkem_unpack.o";; *)

let mlkem_unpack_mc =
  define_assert_from_elf "mlkem_unpack_mc" "x86/mlkem/mlkem_unpack.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xc5; 0xfd; 0x6f; 0x27;  (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x6f; 0x6f; 0x20;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfd; 0x6f; 0x77; 0x40;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfd; 0x6f; 0x7f; 0x60;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,224))) *)
  0xc4; 0xc3; 0x5d; 0x46; 0xd8; 0x20;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm4) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x5d; 0x46; 0xc0; 0x31;
                           (* VPERM2I128 (%_% ymm8) (%_% ymm4) (%_% ymm8) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x55; 0x46; 0xe1; 0x20;
                           (* VPERM2I128 (%_% ymm4) (%_% ymm5) (%_% ymm9) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x55; 0x46; 0xc9; 0x31;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm5) (%_% ymm9) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xea; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm6) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x4d; 0x46; 0xd2; 0x31;
                           (* VPERM2I128 (%_% ymm10) (%_% ymm6) (%_% ymm10) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x45; 0x46; 0xf3; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm7) (%_% ymm11) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm11) (%_% ymm7) (%_% ymm11) (Imm8 (word 49)) *)
  0xc5; 0xe5; 0x6c; 0xfd;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0x6d; 0xed;  (* VPUNPCKHQDQ (%_% ymm5) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xc1; 0x3d; 0x6c; 0xda;
                           (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0x6d; 0xd2;
                           (* VPUNPCKHQDQ (%_% ymm10) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0x5d; 0x6c; 0xc6;  (* VPUNPCKLQDQ (%_% ymm8) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0x6d; 0xf6;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0xc1; 0x35; 0x6c; 0xe3;
                           (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0x6d; 0xdb;
                           (* VPUNPCKHQDQ (%_% ymm11) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x12; 0xc8;
                           (* VMOVSLDUP (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x45; 0x02; 0xc9; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm7) (%_% ymm9) (Imm8 (word 170)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x02; 0xc0; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm7) (%_% ymm8) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xfe;  (* VMOVSLDUP (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xe3; 0x55; 0x02; 0xff; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm5) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xd5; 0x73; 0xd5; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x55; 0x02; 0xf6; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm5) (%_% ymm6) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xec;  (* VMOVSLDUP (%_% ymm5) (%_% ymm4) *)
  0xc4; 0xe3; 0x65; 0x02; 0xed; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm3) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x73; 0xd3; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x65; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm3) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xdb;
                           (* VMOVSLDUP (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xe3; 0x2d; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm10) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x2d; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm10) (%_% ymm11) (Imm8 (word 170)) *)
  0xc5; 0xad; 0x72; 0xf5; 0x10;
                           (* VPSLLD (%_% ymm10) (%_% ymm5) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x35; 0x0e; 0xd2; 0xaa;
                           (* VPBLENDW (%_% ymm10) (%_% ymm9) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x35; 0x72; 0xd1; 0x10;
                           (* VPSRLD (%_% ymm9) (%_% ymm9) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x35; 0x0e; 0xed; 0xaa;
                           (* VPBLENDW (%_% ymm5) (%_% ymm9) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xb5; 0x72; 0xf4; 0x10;
                           (* VPSLLD (%_% ymm9) (%_% ymm4) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x3d; 0x0e; 0xc9; 0xaa;
                           (* VPBLENDW (%_% ymm9) (%_% ymm8) (%_% ymm9) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0x72; 0xd0; 0x10;
                           (* VPSRLD (%_% ymm8) (%_% ymm8) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x3d; 0x0e; 0xe4; 0xaa;
                           (* VPBLENDW (%_% ymm4) (%_% ymm8) (%_% ymm4) (Imm8 (word 170)) *)
  0xc5; 0xbd; 0x72; 0xf3; 0x10;
                           (* VPSLLD (%_% ymm8) (%_% ymm3) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x45; 0x0e; 0xc0; 0xaa;
                           (* VPBLENDW (%_% ymm8) (%_% ymm7) (%_% ymm8) (Imm8 (word 170)) *)
  0xc5; 0xc5; 0x72; 0xd7; 0x10;
                           (* VPSRLD (%_% ymm7) (%_% ymm7) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x45; 0x0e; 0xdb; 0xaa;
                           (* VPBLENDW (%_% ymm3) (%_% ymm7) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x45; 0x72; 0xf3; 0x10;
                           (* VPSLLD (%_% ymm7) (%_% ymm11) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x4d; 0x0e; 0xff; 0xaa;
                           (* VPBLENDW (%_% ymm7) (%_% ymm6) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xcd; 0x72; 0xd6; 0x10;
                           (* VPSRLD (%_% ymm6) (%_% ymm6) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x4d; 0x0e; 0xdb; 0xaa;
                           (* VPBLENDW (%_% ymm11) (%_% ymm6) (%_% ymm11) (Imm8 (word 170)) *)
  0xc5; 0x7d; 0x7f; 0x17;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm10) *)
  0xc5; 0xfd; 0x7f; 0x6f; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm5) *)
  0xc5; 0x7d; 0x7f; 0x4f; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm4) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm8) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm3) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0xa7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,416))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,480))) *)
  0xc4; 0xc3; 0x5d; 0x46; 0xd8; 0x20;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm4) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x5d; 0x46; 0xc0; 0x31;
                           (* VPERM2I128 (%_% ymm8) (%_% ymm4) (%_% ymm8) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x55; 0x46; 0xe1; 0x20;
                           (* VPERM2I128 (%_% ymm4) (%_% ymm5) (%_% ymm9) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x55; 0x46; 0xc9; 0x31;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm5) (%_% ymm9) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xea; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm6) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x4d; 0x46; 0xd2; 0x31;
                           (* VPERM2I128 (%_% ymm10) (%_% ymm6) (%_% ymm10) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x45; 0x46; 0xf3; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm7) (%_% ymm11) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm11) (%_% ymm7) (%_% ymm11) (Imm8 (word 49)) *)
  0xc5; 0xe5; 0x6c; 0xfd;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0x6d; 0xed;  (* VPUNPCKHQDQ (%_% ymm5) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xc1; 0x3d; 0x6c; 0xda;
                           (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0x6d; 0xd2;
                           (* VPUNPCKHQDQ (%_% ymm10) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0x5d; 0x6c; 0xc6;  (* VPUNPCKLQDQ (%_% ymm8) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0x6d; 0xf6;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0xc1; 0x35; 0x6c; 0xe3;
                           (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0x6d; 0xdb;
                           (* VPUNPCKHQDQ (%_% ymm11) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x12; 0xc8;
                           (* VMOVSLDUP (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x45; 0x02; 0xc9; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm7) (%_% ymm9) (Imm8 (word 170)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x02; 0xc0; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm7) (%_% ymm8) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xfe;  (* VMOVSLDUP (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xe3; 0x55; 0x02; 0xff; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm5) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xd5; 0x73; 0xd5; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x55; 0x02; 0xf6; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm5) (%_% ymm6) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xec;  (* VMOVSLDUP (%_% ymm5) (%_% ymm4) *)
  0xc4; 0xe3; 0x65; 0x02; 0xed; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm3) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x73; 0xd3; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x65; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm3) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xdb;
                           (* VMOVSLDUP (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xe3; 0x2d; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm10) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x2d; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm10) (%_% ymm11) (Imm8 (word 170)) *)
  0xc5; 0xad; 0x72; 0xf5; 0x10;
                           (* VPSLLD (%_% ymm10) (%_% ymm5) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x35; 0x0e; 0xd2; 0xaa;
                           (* VPBLENDW (%_% ymm10) (%_% ymm9) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x35; 0x72; 0xd1; 0x10;
                           (* VPSRLD (%_% ymm9) (%_% ymm9) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x35; 0x0e; 0xed; 0xaa;
                           (* VPBLENDW (%_% ymm5) (%_% ymm9) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xb5; 0x72; 0xf4; 0x10;
                           (* VPSLLD (%_% ymm9) (%_% ymm4) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x3d; 0x0e; 0xc9; 0xaa;
                           (* VPBLENDW (%_% ymm9) (%_% ymm8) (%_% ymm9) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0x72; 0xd0; 0x10;
                           (* VPSRLD (%_% ymm8) (%_% ymm8) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x3d; 0x0e; 0xe4; 0xaa;
                           (* VPBLENDW (%_% ymm4) (%_% ymm8) (%_% ymm4) (Imm8 (word 170)) *)
  0xc5; 0xbd; 0x72; 0xf3; 0x10;
                           (* VPSLLD (%_% ymm8) (%_% ymm3) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x45; 0x0e; 0xc0; 0xaa;
                           (* VPBLENDW (%_% ymm8) (%_% ymm7) (%_% ymm8) (Imm8 (word 170)) *)
  0xc5; 0xc5; 0x72; 0xd7; 0x10;
                           (* VPSRLD (%_% ymm7) (%_% ymm7) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x45; 0x0e; 0xdb; 0xaa;
                           (* VPBLENDW (%_% ymm3) (%_% ymm7) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x45; 0x72; 0xf3; 0x10;
                           (* VPSLLD (%_% ymm7) (%_% ymm11) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x4d; 0x0e; 0xff; 0xaa;
                           (* VPBLENDW (%_% ymm7) (%_% ymm6) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xcd; 0x72; 0xd6; 0x10;
                           (* VPSRLD (%_% ymm6) (%_% ymm6) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x4d; 0x0e; 0xdb; 0xaa;
                           (* VPBLENDW (%_% ymm11) (%_% ymm6) (%_% ymm11) (Imm8 (word 170)) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm10) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm5) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm4) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm8) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm3) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm11) *)
  0xc3                     (* RET *)
];;

let mlkem_unpack_tmc = define_trimmed "mlkem_unpack_tmc" mlkem_unpack_mc;;
let mlkem_unpack_TMC_EXEC = X86_MK_CORE_EXEC_RULE mlkem_unpack_tmc;;

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

let MLKEM_UNPACK_CORRECT = prove(
    `!a (l:int16 list) pc.
        aligned 32 a /\
        nonoverlapping (word pc, 754) (a, 512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mlkem_unpack_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [a] s /\
                  read (memory :> bytes(a, 512)) s = num_of_wordlist l)
             (\s. read RIP s = word (pc + 754) /\
                  (LENGTH l = 256
                   ==> read(memory :> bytes(a, 512)) s =
                       num_of_wordlist (unpermute_list l)))
             (MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a, 512)] ,,
              MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
              MAYCHANGE [ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11])`,

  MAP_EVERY X_GEN_TAC [`a:int64`; `l:int16 list`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the length assumption via a case split ***)

  ASM_CASES_TAC `LENGTH(l:int16 list) = 256` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0";
    X86_SIM_TAC mlkem_unpack_TMC_EXEC (1--128)] THEN

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
    X86_STEPS_TAC mlkem_unpack_TMC_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC[])
   (1--128) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
  CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
  CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
  check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN

  REWRITE_TAC[ARITH_RULE `512 = 8 * 64`] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN
  REWRITE_TAC[unpermute_list; avx_unorder] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[num_of_wordlist; VAL] THEN

  REWRITE_TAC[bignum_of_wordlist; VAL] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  CONV_TAC(TOP_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV
   (BIT_WORD_CONV ORELSEC
    GEN_REWRITE_CONV I [BITVAL_CLAUSES; OR_CLAUSES; AND_CLAUSES])) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ABBREV_TAC `twae = &2:real` THEN REAL_ARITH_TAC);;


let MLKEM_UNPACK_NOIBT_SUBROUTINE_CORRECT = prove(
    `!a (l:int16 list) pc.
        aligned 32 a /\
        nonoverlapping (word pc, LENGTH mlkem_unpack_tmc) (a, 512) /\
        nonoverlapping (stackpointer, 8) (a, 512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_unpack_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read (memory :> bytes(a, 512)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (LENGTH l = 256
                   ==> read(memory :> bytes(a, 512)) s =
                       num_of_wordlist (unpermute_list l)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a, 512)])`, 
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_unpack_tmc MLKEM_UNPACK_CORRECT);;

let MLKEM_UNPACK_SUBROUTINE_CORRECT = prove(
    `!a (l:int16 list) pc.
        aligned 32 a /\
        nonoverlapping (word pc, LENGTH mlkem_unpack_mc) (a, 512) /\
        nonoverlapping (stackpointer, 8) (a, 512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_unpack_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read (memory :> bytes(a, 512)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (LENGTH l = 256
                   ==> read(memory :> bytes(a, 512)) s =
                       num_of_wordlist (unpermute_list l)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a, 512)])`, 
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_UNPACK_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)
(* print_literal_from_elf "x86/mlkem/mlkem_unpack.obj";; *)

let mlkem_unpack_windows_mc = define_from_elf
    "mlkem_unpack_windows_mc" "x86/mlkem/mlkem_unpack.obj";;

let mlkem_unpack_windows_tmc = define_trimmed
    "mlkem_unpack_windows_tmc" mlkem_unpack_windows_mc;;

let mlkem_unpack_windows_tmc_EXEC = X86_MK_EXEC_RULE mlkem_unpack_windows_tmc;;

let MLKEM_UNPACK_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove(
    `!a (l:int16 list) pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc, LENGTH mlkem_unpack_windows_tmc) (a, 512) /\
        nonoverlapping (word_sub stackpointer (word 176), 184) (a, 512) /\
        nonoverlapping (word pc, LENGTH mlkem_unpack_windows_tmc)
                       (word_sub stackpointer (word 176), 176)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (mlkem_unpack_windows_tmc) /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [a] s /\
                  read (memory :> bytes(a, 512)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (LENGTH l = 256
                   ==> read(memory :> bytes(a, 512)) s =
                       num_of_wordlist (unpermute_list l)))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE [memory :> bytes(a, 512)] ,,
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 176), 176)])`,
  REPLICATE_TAC 3 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 176 THEN
  REPEAT GEN_TAC THEN

  REWRITE_TAC[fst mlkem_unpack_windows_tmc_EXEC] THEN
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
  X86_STEPS_TAC mlkem_unpack_windows_tmc_EXEC (1--15) THEN

  MP_TAC(SPECL [`a:int64`; `l:int16 list`; `pc + 92`]
    MLKEM_UNPACK_CORRECT) THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN

  X86_BIGSTEP_TAC mlkem_unpack_windows_tmc_EXEC "s16" THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
     (BYTES_LOADED_SUBPROGRAM_RULE mlkem_unpack_windows_tmc
     (REWRITE_RULE[BUTLAST_CLAUSES]
      (AP_TERM `BUTLAST:byte list->byte list` mlkem_unpack_tmc))
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

  X86_STEPS_TAC mlkem_unpack_windows_tmc_EXEC (17--30) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let MLKEM_UNPACK_WINDOWS_SUBROUTINE_CORRECT = prove(
    `!a (l:int16 list) pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc, LENGTH mlkem_unpack_windows_mc) (a, 512) /\
        nonoverlapping (word_sub stackpointer (word 176), 184) (a, 512) /\
        nonoverlapping (word pc, LENGTH mlkem_unpack_windows_mc)
                       (word_sub stackpointer (word 176), 176)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (mlkem_unpack_windows_mc) /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [a] s /\
                  read (memory :> bytes(a, 512)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (LENGTH l = 256
                   ==> read(memory :> bytes(a, 512)) s =
                       num_of_wordlist (unpermute_list l)))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE [memory :> bytes(a, 512)] ,,
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 176), 176)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_UNPACK_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;
