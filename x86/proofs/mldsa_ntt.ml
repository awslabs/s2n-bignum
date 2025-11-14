(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA Forward number theoretic transform.                                *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(*** print_literal_from_elf "x86/mldsa/mldsa_ntt.o";;
 ***)
let mldsa_ntt_mc = define_assert_from_elf "mldsa_ntt_mc" "x86/mldsa/mldsa_ntt.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xc5; 0xfd; 0x6f; 0x06;  (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rsi,0))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x84; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,132))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x24; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1316))) *)
  0xc5; 0xfd; 0x6f; 0x27;  (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,512))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,640))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,768))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,896))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x35; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe1;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x35; 0x28; 0xca;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xcc; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xe1;
                           (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x55; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xcd;
                           (* VPADDD (%_% ymm9) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf2;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xfb;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x88; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,136))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x28; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1320))) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x5d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0xfe; 0xe6;  (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x45; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe7;  (* VMOVSHDUP (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x45; 0x28; 0xfa;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x45; 0x02; 0xfc; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe7;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm7) *)
  0xc5; 0xd5; 0xfe; 0xef;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xfd;
                           (* VPADDD (%_% ymm7) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x8c; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,140))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x2c; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1324))) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xc2;
                           (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfe; 0xcb;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x7f; 0x27;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,512))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,640))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,768))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,896))) (%_% ymm11) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x84; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,132))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x24; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1316))) *)
  0xc5; 0xfd; 0x6f; 0x67; 0x20;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,416))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,544))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,672))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,800))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,928))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x35; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe1;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x35; 0x28; 0xca;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xcc; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xe1;
                           (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x55; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xcd;
                           (* VPADDD (%_% ymm9) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf2;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xfb;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x88; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,136))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x28; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1320))) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x5d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0xfe; 0xe6;  (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x45; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe7;  (* VMOVSHDUP (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x45; 0x28; 0xfa;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x45; 0x02; 0xfc; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe7;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm7) *)
  0xc5; 0xd5; 0xfe; 0xef;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xfd;
                           (* VPADDD (%_% ymm7) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x8c; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,140))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x2c; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1324))) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xc2;
                           (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfe; 0xcb;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,544))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,672))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,800))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,928))) (%_% ymm11) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x84; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,132))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x24; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1316))) *)
  0xc5; 0xfd; 0x6f; 0x67; 0x40;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,576))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,704))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,832))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,960))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x35; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe1;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x35; 0x28; 0xca;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xcc; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xe1;
                           (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x55; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xcd;
                           (* VPADDD (%_% ymm9) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf2;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xfb;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x88; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,136))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x28; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1320))) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x5d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0xfe; 0xe6;  (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x45; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe7;  (* VMOVSHDUP (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x45; 0x28; 0xfa;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x45; 0x02; 0xfc; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe7;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm7) *)
  0xc5; 0xd5; 0xfe; 0xef;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xfd;
                           (* VPADDD (%_% ymm7) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x8c; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,140))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x2c; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1324))) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xc2;
                           (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfe; 0xcb;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,576))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,704))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,832))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,960))) (%_% ymm11) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x84; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,132))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x24; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1316))) *)
  0xc5; 0xfd; 0x6f; 0x67; 0x60;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,224))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,480))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,608))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,736))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,864))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,992))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x35; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe1;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x35; 0x28; 0xca;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xcc; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xe1;
                           (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x55; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xcd;
                           (* VPADDD (%_% ymm9) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf2;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xfb;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x88; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,136))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x28; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1320))) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x5d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0xfe; 0xe6;  (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x45; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe7;  (* VMOVSHDUP (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x45; 0x28; 0xfa;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x45; 0x02; 0xfc; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe7;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm7) *)
  0xc5; 0xd5; 0xfe; 0xef;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xfd;
                           (* VPADDD (%_% ymm7) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x8c; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,140))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x2c; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1324))) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xc2;
                           (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfe; 0xcb;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,608))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,736))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,864))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,992))) (%_% ymm11) *)
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
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x90; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,144))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x30; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1328))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x35; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe1;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x35; 0x28; 0xca;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xcc; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xe1;
                           (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x55; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xcd;
                           (* VPADDD (%_% ymm9) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf2;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xfb;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
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
  0xc5; 0xfd; 0x6f; 0x8e; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,160))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1344))) *)
  0xc4; 0x62; 0x55; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe5;  (* VMOVSHDUP (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x55; 0x28; 0xea;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc3; 0x55; 0x02; 0xec; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x65; 0xfa; 0xe5;  (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0xfe; 0xdd;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xed;
                           (* VPADDD (%_% ymm5) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xc2;
                           (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x5d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0xfe; 0xe6;  (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfe; 0xcb;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
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
  0xc5; 0xfd; 0x6f; 0x8e; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,288))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1472))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xf8;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm6) *)
  0xc5; 0xd5; 0xfe; 0xee;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x65; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm4) *)
  0xc5; 0xe5; 0xfe; 0xdc;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xfe; 0xd3;
                           (* VPADDD (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xd5;
                           (* VPSUBD (%_% ymm10) (%_% ymm10) (%_% ymm13) *)
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
  0xc5; 0xfd; 0x6f; 0x8e; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,416))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1600))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x55; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe5;  (* VMOVSHDUP (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x55; 0x28; 0xea;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc3; 0x55; 0x02; 0xec; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x35; 0xfa; 0xe5;  (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm5) *)
  0xc5; 0x35; 0xfe; 0xcd;  (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xed;
                           (* VPADDD (%_% ymm5) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x3d; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xfe; 0xc4;  (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x65; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe3;  (* VMOVSHDUP (%_% ymm12) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x65; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc3; 0x65; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x45; 0xfa; 0xe3;  (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xfe; 0xfb;  (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm3) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm11) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf3;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,544))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1728))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x45; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe7;  (* VMOVSHDUP (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x45; 0x28; 0xfa;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x45; 0x02; 0xfc; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x35; 0xfa; 0xe7;  (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm7) *)
  0xc5; 0x35; 0xfe; 0xcf;  (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xfd;
                           (* VPADDD (%_% ymm7) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x3d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm6) *)
  0xc5; 0x3d; 0xfe; 0xc6;  (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,672))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1856))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x65; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe3;  (* VMOVSHDUP (%_% ymm12) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x65; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc3; 0x65; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe3;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm3) *)
  0xc5; 0xd5; 0xfe; 0xeb;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm3) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm11) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe3;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,800))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1984))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x41; 0x35; 0xfe; 0xc8;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,928))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2112))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x45; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm6) *)
  0xc5; 0xc5; 0xfe; 0xfe;  (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x20; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1056))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2240))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xd5; 0xfe; 0xec;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xa0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1184))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2368))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x65; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc1; 0x65; 0xfe; 0xdb;
                           (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc5; 0x7d; 0x7f; 0x0f;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x47; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm8) *)
  0xc5; 0xfd; 0x7f; 0x7f; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm7) *)
  0xc5; 0xfd; 0x7f; 0x77; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm3) *)
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
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x94; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,148))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x34; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1332))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x35; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe1;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x35; 0x28; 0xca;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xcc; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xe1;
                           (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x55; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xcd;
                           (* VPADDD (%_% ymm9) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf2;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xfb;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
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
  0xc5; 0xfd; 0x6f; 0x8e; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,192))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x60; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1376))) *)
  0xc4; 0x62; 0x55; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe5;  (* VMOVSHDUP (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x55; 0x28; 0xea;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc3; 0x55; 0x02; 0xec; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x65; 0xfa; 0xe5;  (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0xfe; 0xdd;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xed;
                           (* VPADDD (%_% ymm5) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xc2;
                           (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x5d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0xfe; 0xe6;  (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfe; 0xcb;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
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
  0xc5; 0xfd; 0x6f; 0x8e; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,320))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xe0; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1504))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xf8;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm6) *)
  0xc5; 0xd5; 0xfe; 0xee;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x65; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm4) *)
  0xc5; 0xe5; 0xfe; 0xdc;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xfe; 0xd3;
                           (* VPADDD (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xd5;
                           (* VPSUBD (%_% ymm10) (%_% ymm10) (%_% ymm13) *)
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
  0xc5; 0xfd; 0x6f; 0x8e; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,448))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x60; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1632))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x55; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe5;  (* VMOVSHDUP (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x55; 0x28; 0xea;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc3; 0x55; 0x02; 0xec; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x35; 0xfa; 0xe5;  (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm5) *)
  0xc5; 0x35; 0xfe; 0xcd;  (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xed;
                           (* VPADDD (%_% ymm5) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x3d; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xfe; 0xc4;  (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x65; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe3;  (* VMOVSHDUP (%_% ymm12) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x65; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc3; 0x65; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x45; 0xfa; 0xe3;  (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xfe; 0xfb;  (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm3) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm11) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf3;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,576))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xe0; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1760))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x45; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe7;  (* VMOVSHDUP (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x45; 0x28; 0xfa;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x45; 0x02; 0xfc; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x35; 0xfa; 0xe7;  (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm7) *)
  0xc5; 0x35; 0xfe; 0xcf;  (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xfd;
                           (* VPADDD (%_% ymm7) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x3d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm6) *)
  0xc5; 0x3d; 0xfe; 0xc6;  (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,704))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x60; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1888))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x65; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe3;  (* VMOVSHDUP (%_% ymm12) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x65; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc3; 0x65; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe3;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm3) *)
  0xc5; 0xd5; 0xfe; 0xeb;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm3) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm11) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe3;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,832))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xe0; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2016))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x41; 0x35; 0xfe; 0xc8;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,960))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x60; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2144))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x45; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm6) *)
  0xc5; 0xc5; 0xfe; 0xfe;  (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x40; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1088))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xe0; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2272))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xd5; 0xfe; 0xec;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xc0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1216))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x60; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2400))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x65; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc1; 0x65; 0xfe; 0xdb;
                           (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm8) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm7) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0xa7; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,512))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,544))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,576))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,608))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,640))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,672))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,704))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,736))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x98; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,152))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x38; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1336))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x35; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe1;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x35; 0x28; 0xca;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xcc; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xe1;
                           (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x55; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xcd;
                           (* VPADDD (%_% ymm9) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf2;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xfb;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
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
  0xc5; 0xfd; 0x6f; 0x8e; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,224))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1408))) *)
  0xc4; 0x62; 0x55; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe5;  (* VMOVSHDUP (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x55; 0x28; 0xea;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc3; 0x55; 0x02; 0xec; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x65; 0xfa; 0xe5;  (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0xfe; 0xdd;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xed;
                           (* VPADDD (%_% ymm5) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xc2;
                           (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x5d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0xfe; 0xe6;  (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfe; 0xcb;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
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
  0xc5; 0xfd; 0x6f; 0x8e; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,352))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1536))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xf8;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm6) *)
  0xc5; 0xd5; 0xfe; 0xee;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x65; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm4) *)
  0xc5; 0xe5; 0xfe; 0xdc;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xfe; 0xd3;
                           (* VPADDD (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xd5;
                           (* VPSUBD (%_% ymm10) (%_% ymm10) (%_% ymm13) *)
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
  0xc5; 0xfd; 0x6f; 0x8e; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,480))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1664))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x55; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe5;  (* VMOVSHDUP (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x55; 0x28; 0xea;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc3; 0x55; 0x02; 0xec; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x35; 0xfa; 0xe5;  (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm5) *)
  0xc5; 0x35; 0xfe; 0xcd;  (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xed;
                           (* VPADDD (%_% ymm5) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x3d; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xfe; 0xc4;  (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x65; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe3;  (* VMOVSHDUP (%_% ymm12) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x65; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc3; 0x65; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x45; 0xfa; 0xe3;  (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xfe; 0xfb;  (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm3) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm11) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf3;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,608))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1792))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x45; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe7;  (* VMOVSHDUP (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x45; 0x28; 0xfa;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x45; 0x02; 0xfc; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x35; 0xfa; 0xe7;  (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm7) *)
  0xc5; 0x35; 0xfe; 0xcf;  (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xfd;
                           (* VPADDD (%_% ymm7) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x3d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm6) *)
  0xc5; 0x3d; 0xfe; 0xc6;  (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,736))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1920))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x65; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe3;  (* VMOVSHDUP (%_% ymm12) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x65; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc3; 0x65; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe3;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm3) *)
  0xc5; 0xd5; 0xfe; 0xeb;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm3) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm11) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe3;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,864))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2048))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x41; 0x35; 0xfe; 0xc8;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,992))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2176))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x45; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm6) *)
  0xc5; 0xc5; 0xfe; 0xfe;  (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x60; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1120))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2304))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xd5; 0xfe; 0xec;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xe0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1248))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2432))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x65; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc1; 0x65; 0xfe; 0xdb;
                           (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,512))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,544))) (%_% ymm8) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,576))) (%_% ymm7) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,608))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,640))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,672))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,704))) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,736))) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0xa7; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,768))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,800))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,832))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,864))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,896))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,928))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,960))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,992))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x9c; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,156))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x3c; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1340))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x35; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe1;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x35; 0x28; 0xca;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xcc; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xe1;
                           (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x55; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xcd;
                           (* VPADDD (%_% ymm9) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf2;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xfb;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
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
  0xc5; 0xfd; 0x6f; 0x8e; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,256))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1440))) *)
  0xc4; 0x62; 0x55; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe5;  (* VMOVSHDUP (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x55; 0x28; 0xea;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc3; 0x55; 0x02; 0xec; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x65; 0xfa; 0xe5;  (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0xfe; 0xdd;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xed;
                           (* VPADDD (%_% ymm5) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xc2;
                           (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x5d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0xfe; 0xe6;  (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfe; 0xcb;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
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
  0xc5; 0xfd; 0x6f; 0x8e; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,384))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x20; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1568))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xf8;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm6) *)
  0xc5; 0xd5; 0xfe; 0xee;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x65; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm4) *)
  0xc5; 0xe5; 0xfe; 0xdc;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xfe; 0xd3;
                           (* VPADDD (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xd5;
                           (* VPSUBD (%_% ymm10) (%_% ymm10) (%_% ymm13) *)
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
  0xc5; 0xfd; 0x6f; 0x8e; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,512))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1696))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x55; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe5;  (* VMOVSHDUP (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x55; 0x28; 0xea;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc3; 0x55; 0x02; 0xec; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x35; 0xfa; 0xe5;  (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm5) *)
  0xc5; 0x35; 0xfe; 0xcd;  (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xed;
                           (* VPADDD (%_% ymm5) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x3d; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xfe; 0xc4;  (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x65; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe3;  (* VMOVSHDUP (%_% ymm12) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x65; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc3; 0x65; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x45; 0xfa; 0xe3;  (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xfe; 0xfb;  (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm3) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm11) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf3;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,640))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x20; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1824))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x45; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe7;  (* VMOVSHDUP (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x45; 0x28; 0xfa;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x45; 0x02; 0xfc; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x35; 0xfa; 0xe7;  (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm7) *)
  0xc5; 0x35; 0xfe; 0xcf;  (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xfd;
                           (* VPADDD (%_% ymm7) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x3d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm6) *)
  0xc5; 0x3d; 0xfe; 0xc6;  (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,768))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1952))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x65; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe3;  (* VMOVSHDUP (%_% ymm12) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x65; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc3; 0x65; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe3;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm3) *)
  0xc5; 0xd5; 0xfe; 0xeb;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm3) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm11) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe3;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,896))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x20; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2080))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x41; 0x35; 0xfe; 0xc8;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x00; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1024))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2208))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x45; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm6) *)
  0xc5; 0xc5; 0xfe; 0xfe;  (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x80; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1152))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x20; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2336))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xd5; 0xfe; 0xec;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x00; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1280))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2464))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x65; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc1; 0x65; 0xfe; 0xdb;
                           (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,768))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,800))) (%_% ymm8) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,832))) (%_% ymm7) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,864))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,896))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,928))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,960))) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,992))) (%_% ymm11) *)
  0xc3                     (* RET *)
];;

let mldsa_ntt_tmc = define_trimmed "mldsa_ntt_tmc" mldsa_ntt_mc;;
let MLDSA_NTT_TMC_EXEC = X86_MK_CORE_EXEC_RULE mldsa_ntt_tmc;;

(* ------------------------------------------------------------------------- *)
(* Data tables that are assumed in the precondition.                         *)
(* ------------------------------------------------------------------------- *)

(*** ML-DSA NTT zeta array: 624 elements total
 *** - [0-31]: ML-DSA constants (q=8380417, qinv=58728449, etc.)
 *** - [32-39]: Initial twiddle factors
 *** - [40-367]: 4x replicated twiddles for SIMD (82 unique values × 4 copies)
 *** - [368-623]: Final twiddle section with 2x replication (128 unique values × 2 copies)
 *** Follows bit-reversed indexing per FIPS 204 Appendix B with AVX2 optimization
 ***)
let mldsa_complete_qdata = define
 `mldsa_complete_qdata:int list =
   [
   &8380417; &8380417; &8380417; &8380417; &8380417; &8380417; &8380417; &8380417;
   &58728449; &58728449; &58728449; &58728449; &58728449; &58728449; &58728449; &58728449;
   -- &8395782; -- &8395782; -- &8395782; -- &8395782; -- &8395782; -- &8395782; -- &8395782; -- &8395782;
   &41978; &41978; &41978; &41978; &41978; &41978; &41978; &41978;
   -- &151046689;
   &1830765815; -- &1929875198; -- &1927777021; &1640767044; &1477910808; &1612161320; &1640734244; &308362795;
   &308362795; &308362795; &308362795; -- &1815525077; -- &1815525077; -- &1815525077; -- &1815525077;
   -- &1374673747; -- &1374673747; -- &1374673747; -- &1374673747; -- &1091570561; -- &1091570561; -- &1091570561;
   -- &1091570561; -- &1929495947; -- &1929495947; -- &1929495947; -- &1929495947; &515185417; &515185417;
   &515185417; &515185417; -- &285697463; -- &285697463; -- &285697463; -- &285697463; &625853735; &625853735;
   &625853735; &625853735; &1727305304; &1727305304; &2082316400; &2082316400; -- &1364982364; -- &1364982364;
   &858240904; &858240904; &1806278032; &1806278032; &222489248; &222489248; -- &346752664; -- &346752664;
   &684667771; &684667771; &1654287830; &1654287830; -- &878576921; -- &878576921; -- &1257667337; -- &1257667337;
   -- &748618600; -- &748618600; &329347125; &329347125; &1837364258; &1837364258; -- &1443016191; -- &1443016191;
   -- &1170414139; -- &1170414139; -- &1846138265; -- &1631226336; -- &1404529459; &1838055109; &1594295555;
   -- &1076973524; -- &1898723372; -- &594436433; -- &202001019; -- &475984260; -- &561427818; &1797021249;
   -- &1061813248; &2059733581; -- &1661512036; -- &1104976547; -- &1750224323; -- &901666090; &418987550;
   &1831915353; -- &1925356481; &992097815; &879957084; &2024403852; &1484874664; -- &1636082790; -- &285388938;
   -- &1983539117; -- &1495136972; -- &950076368; -- &1714807468; -- &952438995; -- &1574918427; &1350681039;
   -- &2143979939; &1599739335; -- &1285853323; -- &993005454; -- &1440787840; &568627424; -- &783134478;
   -- &588790216; &289871779; -- &1262003603; &2135294594; -- &1018755525; -- &889861155; &1665705315; &1321868265;
   &1225434135; -- &1784632064; &666258756; &675310538; -- &1555941048; -- &1999506068; -- &1499481951;
   -- &695180180; -- &1375177022; &1777179795; &334803717; -- &178766299; -- &518252220; &1957047970; &1146323031;
   -- &654783359; -- &1974159335; &1651689966; &140455867; -- &1039411342; &1955560694; &1529189038;
   -- &2131021878; -- &247357819; &1518161567; -- &86965173; &1708872713; &1787797779; &1638590967; -- &120646188;
   -- &1669960606; -- &916321552; &1155548552; &2143745726; &1210558298; -- &1261461890; -- &318346816; &628664287;
   -- &1729304568; &1422575624; &1424130038; -- &1185330464; &235321234; &168022240; &1206536194; &985155484;
   -- &894060583; -- &898413; -- &1363460238; -- &605900043; &2027833504; &14253662; &1014493059; &863641633;
   &1819892093; &2124962073; -- &1223601433; -- &1920467227; -- &1637785316; -- &1536588520; &694382729;
   &235104446; -- &1045062172; &831969619; -- &300448763; &756955444; -- &260312805; &1554794072; &1339088280;
   -- &2040058690; -- &853476187; -- &2047270596; -- &1723816713; -- &1591599803; -- &440824168; &1119856484;
   &1544891539; &155290192; -- &973777462; &991903578; &912367099; -- &44694137; &1176904444; -- &421552614;
   -- &818371958; &1747917558; -- &325927722; &908452108; &1851023419; -- &1176751719; -- &1354528380; -- &72690498;
   -- &314284737; &985022747; &963438279; -- &1078959975; &604552167; -- &1021949428; &608791570; &173440395;
   -- &2126092136; -- &1316619236; -- &1039370342; &6087993; -- &110126092; &565464272; -- &1758099917; -- &1600929361;
   &879867909; -- &1809756372; &400711272; &1363007700; &30313375; -- &326425360; &1683520342; -- &517299994;
   &2027935492; -- &1372618620; &128353682; -- &1123881663; &137583815; -- &635454918; -- &642772911; &45766801;
   &671509323; -- &2070602178; &419615363; &1216882040; -- &270590488; -- &1276805128; &371462360; -- &1357098057;
   -- &384158533; &827959816; -- &596344473; &702390549; -- &279505433; -- &260424530; -- &71875110; -- &1208667171;
   -- &1499603926; &2036925262; -- &540420426; &746144248; -- &1420958686; &2032221021; &1904936414; &1257750362;
   &1926727420; &1931587462; &1258381762; &885133339; &1629985060; &1967222129; &6363718; -- &1287922800;
   &1136965286; &1779436847; &1116720494; &1042326957; &1405999311; &713994583; &940195359; -- &1542497137;
   &2061661095; -- &883155599; &1726753853; -- &1547952704; &394851342; &283780712; &776003547; &1123958025;
   &201262505; &1934038751; &374860238;
   -- &3975713; &25847; -- &2608894; -- &518909; &237124; -- &777960; -- &876248; &466468; &1826347; &1826347; &1826347;
   &1826347; &2353451; &2353451; &2353451; &2353451; -- &359251; -- &359251; -- &359251; -- &359251; -- &2091905;
   -- &2091905; -- &2091905; -- &2091905; &3119733; &3119733; &3119733; &3119733; -- &2884855; -- &2884855; -- &2884855;
   -- &2884855; &3111497; &3111497; &3111497; &3111497; &2680103; &2680103; &2680103; &2680103; &2725464;
   &2725464; &1024112; &1024112; -- &1079900; -- &1079900; &3585928; &3585928; -- &549488; -- &549488; -- &1119584;
   -- &1119584; &2619752; &2619752; -- &2108549; -- &2108549; -- &2118186; -- &2118186; -- &3859737; -- &3859737;
   -- &1399561; -- &1399561; -- &3277672; -- &3277672; &1757237; &1757237; -- &19422; -- &19422; &4010497; &4010497;
   &280005; &280005; &2706023; &95776; &3077325; &3530437; -- &1661693; -- &3592148; -- &2537516; &3915439;
   -- &3861115; -- &3043716; &3574422; -- &2867647; &3539968; -- &300467; &2348700; -- &539299; -- &1699267;
   -- &1643818; &3505694; -- &3821735; &3507263; -- &2140649; -- &1600420; &3699596; &811944; &531354; &954230;
   &3881043; &3900724; -- &2556880; &2071892; -- &2797779; -- &3930395; -- &3677745; -- &1452451; &2176455;
   -- &1257611; -- &4083598; -- &3190144; -- &3632928; &3412210; &2147896; -- &2967645; -- &411027; -- &671102;
   -- &22981; -- &381987; &1852771; -- &3343383; &508951; &44288; &904516; -- &3724342; &1653064; &2389356;
   &759969; &189548; &3159746; -- &2409325; &1315589; &1285669; -- &812732; -- &3019102; -- &3628969; -- &1528703;
   -- &3041255; &3475950; -- &1585221; &1939314; -- &1000202; -- &3157330; &126922; -- &983419; &2715295;
   -- &3693493; -- &2477047; -- &1228525; -- &1308169; &1349076; -- &1430430; &264944; &3097992; -- &1100098;
   &3958618; -- &8578; -- &3249728; -- &210977; -- &1316856; -- &3553272; -- &1851402; -- &177440; &1341330;
   -- &1584928; -- &1439742; -- &3881060; &3839961; &2091667; -- &3342478; &266997; -- &3520352; &900702;
   &495491; -- &655327; -- &3556995; &342297; &3437287; &2842341; &4055324; -- &3767016; -- &2994039; -- &1333058;
   -- &451100; -- &1279661; &1500165; -- &542412; -- &2584293; -- &2013608; &1957272; -- &3183426; &810149;
   -- &3038916; &2213111; -- &426683; -- &1667432; -- &2939036; &183443; -- &554416; &3937738; &3407706;
   &2244091; &2434439; -- &3759364; &1859098; -- &1613174; -- &3122442; -- &525098; &286988; -- &3342277;
   &2691481; &1247620; &1250494; &1869119; &1237275; &1312455; &1917081; &777191; -- &2831860; -- &3724270;
   &2432395; &3369112; &162844; &1652634; &3523897; -- &975884; &1723600; -- &1104333; -- &2235985; -- &976891;
   &3919660; &1400424; &2316500; -- &2446433; -- &1235728; -- &1197226; &909542; -- &43260; &2031748; -- &768622;
   -- &2437823; &1735879; -- &2590150; &2486353; &2635921; &1903435; -- &3318210; &3306115; -- &2546312;
   &2235880; -- &1671176; &594136; &2454455; &185531; &1616392; -- &3694233; &3866901; &1717735; -- &1803090;
   -- &260646; -- &420899; &1612842; -- &48306; -- &846154; &3817976; -- &3562462; &3513181; -- &3193378;
   &819034; -- &522500; &3207046; -- &3595838; &4108315; &203044; &1265009; &1595974; -- &3548272; -- &1050970;
   -- &1430225; -- &1962642; -- &1374803; &3406031; -- &1846953; -- &3776993; -- &164721; -- &1207385; &3014001;
   -- &1799107; &269760; &472078; &1910376; -- &3833893; -- &2286327; -- &3545687; -- &1362209; &1976782
   ]`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(***
 *** Currently, there is a discrepency when compiling the asmb on x86 machines vs Arm
 *** As such, the produced mldsa_ntt_tmc has different lengths. When on ARM 0x3049
 *** when on x86 0x3079.
 ***)

let MLDSA_NTT_CORRECT = prove
  (`!a zetas (zetas_list:int32 list) x pc.
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (word pc,0x3079) (a, 1024) /\
    nonoverlapping (word pc,0x3079) (zetas, 2496) /\
    nonoverlapping (a, 1024) (zetas, 2496)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST mldsa_ntt_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [a; zetas] s /\
              wordlist_from_memory(zetas,624) s = MAP (iword: int -> 32 word) mldsa_complete_qdata /\
              (!i. i < 256 ==> abs(ival(x i)) <= &8380416) /\
              !i. i < 256
                  ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                      x i)
          (\s. read RIP s = word(pc + 0x3078) /\
              (!i. i < 256
                        ==> let zi =
                      read(memory :> bytes32(word_add a (word(4 * i)))) s in
                      (ival zi == mldsa_forward_ntt (ival o x) i) (mod &8380417) /\
                      abs(ival zi) <= &42035261))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [ZMM0; ZMM1; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
          MAYCHANGE [RAX] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(a,1024)])`,

(*** Setup - introduce variables and break down assumptions ***)
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `zetas:int64`; `zetas_list:int32 list`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

(*** Pull out the bounds assumption since we don't need to expand it
 *** until much later, and it keeps things a bit smaller and simpler
 ***)

  GLOBALIZE_PRECONDITION_TAC THEN

(*** But do expand all the input[i] = x i assumptions ***)

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN

  REWRITE_TAC [SOME_FLAGS; fst MLDSA_NTT_TMC_EXEC] THEN

  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `init_ymm1:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `init_ymm2:int256` `read YMM2` THEN

  ENSURES_INIT_TAC "s0" THEN

(*** First restructure all the loads from the a pointer ***)

  MP_TAC(end_itlist CONJ (map (fun n ->
    READ_MEMORY_MERGE_CONV 3 (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add a (word n))) s0`)) (0--31))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN STRIP_TAC THEN

(*** Expand the qdata table ***)

  FIRST_X_ASSUM(MP_TAC o CONV_RULE (LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  REWRITE_TAC[mldsa_complete_qdata; MAP; CONS_11] THEN
  STRIP_TAC THEN

(*** Restructure zeta entries, as before but with WORD_REDUCE_CONV to simplify ***)

  MP_TAC(end_itlist CONJ (map (fun n ->
    READ_MEMORY_MERGE_CONV 3 (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add zetas (word n))) s0`)) (0--77))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN STRIP_TAC THEN

(*** We've thrown away some of the 32-bit words that are used in
 *** broadcast instructions. We could have written a more refined
 *** alternative to DISCARD_MATCHING_ASSUMPTIONS above.
 *** But here we just recreate them: select the two memory
 *** assumptions we want to break apart, then split them up.
 ***)

  FIRST_ASSUM(MP_TAC o check
   (can (term_match [] `read (memory :> bytes256 (word_add zetas (word 128))) s0 = xxx`) o concl)) THEN
  FIRST_ASSUM(MP_TAC o check
   (can (term_match [] `read (memory :> bytes256 (word_add zetas (word 1312))) s0 = xxx`) o concl)) THEN
  REPLICATE_TAC 2
   (CONV_TAC(LAND_CONV(READ_MEMORY_SPLIT_CONV 3)) THEN
    CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN STRIP_TAC) THEN

(*** Do the entire simulation (very slow!) ****)

  MAP_EVERY (fun n -> X86_STEPS_TAC MLDSA_NTT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[mldsa_montmul; WORD_ADD_MLDSA_MONTMUL;
                      WORD_ADD_MLDSA_MONTMUL_ALT; WORD_SUB_MLDSA_MONTMUL])
        (1--2337) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

(**** Reverse the restructuring by splitting the 256-bit words up ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN

(*** Expand the cases in the conclusion (leave the let-terms for now)***)

  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[INT_ABS_BOUNDS; WORD_ADD_0] THEN

(*** Rewrite with assumptions then throw them away ***)

  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s2337" THEN

(*** Remove one other non-arithmetical oddity ***)

  REWRITE_TAC[WORD_BLAST `word_subword (x:int64) (0,64) = x`] THEN
  REWRITE_TAC[WORD_BLAST
   `word_subword (word_ushr (word_join (h:int32) (l:int32):int64) 32) (0,32) =
    h`] THEN

(*** Try splitting into 256 subgoals and applying CONGBOUND ***)

  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  REPEAT(GEN_REWRITE_TAC I
   [TAUT `p /\ q /\ r /\ s <=> (p /\ q /\ r) /\ s`] THEN CONJ_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o CONV_RULE EXPAND_CASES_CONV) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCH_THEN(fun aboth ->
    W(MP_TAC o GEN_CONGBOUND_RULE (CONJUNCTS aboth) o
      rand o lhand o rator o lhand o snd)) THEN
  (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [REWRITE_TAC[INVERSE_MOD_CONV `inverse_mod 8380417 4294967296`] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
    CONV_TAC(ONCE_DEPTH_CONV MLDSA_FORWARD_NTT_CONV) THEN
    REWRITE_TAC[GSYM INT_REM_EQ; o_THM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC[INT_REM_EQ] THEN
    REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC;
    MATCH_MP_TAC(INT_ARITH
     `l':int <= l /\ u <= u'
      ==> l <= x /\ x <= u ==> l' <= x /\ x <= u'`) THEN
    CONV_TAC INT_REDUCE_CONV]));;

(* ------------------------------------------------------------------------- *)
(* Subroutine correctness theorems.                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NTT_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a zetas (zetas_list:int32 list) x pc stackpointer returnaddress.
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (word pc,LENGTH mldsa_ntt_tmc) (a, 1024) /\
    nonoverlapping (word pc,LENGTH mldsa_ntt_tmc) (zetas, 2496) /\
    nonoverlapping (a, 1024) (zetas, 2496) /\
    nonoverlapping (stackpointer,8) (a, 1024) /\
    nonoverlapping (stackpointer,8) (zetas, 2496)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_ntt_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [a; zetas] s /\
              wordlist_from_memory(zetas,624) s = MAP (iword: int -> 32 word) mldsa_complete_qdata /\
              (!i. i < 256 ==> abs(ival(x i)) <= &8380416) /\
              !i. i < 256
                  ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                      x i)
          (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (!i. i < 256
                        ==> let zi =
                      read(memory :> bytes32(word_add a (word(4 * i)))) s in
                      (ival zi == mldsa_forward_ntt (ival o x) i) (mod &8380417) /\
                      abs(ival zi) <= &42035261))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(a,1024)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_ntt_tmc (CONV_RULE TWEAK_CONV MLDSA_NTT_CORRECT));;

let MLDSA_NTT_SUBROUTINE_CORRECT = prove
 (`!a zetas (zetas_list:int32 list) x pc stackpointer returnaddress.
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (word pc,LENGTH mldsa_ntt_mc) (a, 1024) /\
    nonoverlapping (word pc,LENGTH mldsa_ntt_mc) (zetas, 2496) /\
    nonoverlapping (a, 1024) (zetas, 2496) /\
    nonoverlapping (stackpointer,8) (a, 1024) /\
    nonoverlapping (stackpointer,8) (zetas, 2496)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_ntt_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [a; zetas] s /\
              wordlist_from_memory(zetas,624) s = MAP (iword: int -> 32 word) mldsa_complete_qdata /\
              (!i. i < 256 ==> abs(ival(x i)) <= &8380416) /\
              !i. i < 256
                  ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                      x i)
          (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (!i. i < 256
                        ==> let zi =
                      read(memory :> bytes32(word_add a (word(4 * i)))) s in
                      (ival zi == mldsa_forward_ntt (ival o x) i) (mod &8380417) /\
                      abs(ival zi) <= &42035261))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(a,1024)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
  (CONV_RULE TWEAK_CONV MLDSA_NTT_NOIBT_SUBROUTINE_CORRECT)));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let mldsa_ntt_windows_mc = define_from_elf
    "mldsa_ntt_windows_mc" "x86/mldsa/mldsa_ntt.obj";;

let mldsa_ntt_windows_tmc = define_trimmed
    "mldsa_ntt_windows_tmc" mldsa_ntt_windows_mc;;

let MLDSA_NTT_WINDOWS_TMC_EXEC = X86_MK_EXEC_RULE mldsa_ntt_windows_tmc;;

let MLDSA_NTT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a zetas (zetas_list:int32 list) x pc stackpointer returnaddress.
        aligned 32 a /\
        aligned 32 zetas /\
        nonoverlapping (word pc,LENGTH mldsa_ntt_windows_tmc) (a, 1024) /\
        nonoverlapping (word pc,LENGTH mldsa_ntt_windows_tmc) (zetas, 2496) /\
        nonoverlapping (a, 1024) (zetas, 2496) /\
        nonoverlapping (word_sub stackpointer (word 176),184) (a, 1024) /\
        nonoverlapping (word_sub stackpointer (word 176),176) (zetas, 2496) /\
        nonoverlapping (word pc,LENGTH mldsa_ntt_windows_tmc)
                       (word_sub stackpointer (word 176),176)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) mldsa_ntt_windows_tmc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a; zetas] s /\
                   wordlist_from_memory(zetas,624) s = MAP (iword: int -> 32 word) mldsa_complete_qdata /\
                   (!i. i < 256 ==> abs(ival(x i)) <= &8380416) /\
                   !i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           x i)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   (!i. i < 256
                             ==> let zi =
                           read(memory :> bytes32(word_add a (word(4 * i)))) s in
                           (ival zi == mldsa_forward_ntt (ival o x) i) (mod &8380417) /\
                           abs(ival zi) <= &42035261))
              (MAYCHANGE [RSP] ,,
               WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(word_sub stackpointer (word 176),176)] ,,
               MAYCHANGE [memory :> bytes(a,1024)])`,

(*** Expand away the wordlist_from_memory ****)
  CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN

(*** Handle initial quantifiers and set up stack offset management ***)
  REPLICATE_TAC 5 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 176 THEN REPEAT GEN_TAC THEN

(*** Set up basic Windows ABI framework and rewrite with Windows calling convention ***)
  REWRITE_TAC[fst MLDSA_NTT_WINDOWS_TMC_EXEC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[WINDOWS_C_ARGUMENTS] THEN
  REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN

(*** Set up register preservation for Windows ABI compliance
 *** Windows ABI requires preserving RDI, RSI, and XMM6-XMM15 across function calls ***)
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

(*** Handle the ZMM/YMM register notation conversion ***)
  REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
  REWRITE_TAC(map GSYM
    [YMM6;YMM7;YMM8;YMM9;YMM10;YMM11;YMM12;YMM13;YMM14;YMM15]) THEN

(*** Introduce ghost variables for initial XMM register values
 *** These will track the register states for restoration in the epilogue ***)
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

(*** Globalize preconditions and substitute preserved register values ***)
  GLOBALIZE_PRECONDITION_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN

(*** Initialize execution and simulate the prologue (register saves)
 *** Steps 1-15 cover the Windows prologue that saves XMM registers to stack ***)
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLDSA_NTT_WINDOWS_TMC_EXEC (1--15) THEN

(*** Apply the main Unix correctness theorem to the core NTT computation ***)
  MP_TAC(SPECL [`a:int64`; `zetas:int64`; `zetas_list:int32 list`; `x:num->int32`; `pc + 92`]
    MLDSA_NTT_CORRECT) THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN

(*** Expand wordlist_from_memory again ****)
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV)) THEN

(*** Expand MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ****)
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN

(*** Execute the main NTT computation as a single big step
 *** This handles the core algorithm while preserving the register save/restore wrapper ***)
  X86_BIGSTEP_TAC MLDSA_NTT_WINDOWS_TMC_EXEC "s16" THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
     (BYTES_LOADED_SUBPROGRAM_RULE mldsa_ntt_windows_tmc
     (REWRITE_RULE[BUTLAST_CLAUSES]
      (AP_TERM `BUTLAST:byte list->byte list` mldsa_ntt_tmc))
     92));
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN

(*** Capture the final YMM register states after main computation ***)
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

(*** Simulate the epilogue (register restoration and return)
 *** Steps 17-30 cover the Windows epilogue that restores XMM registers from stack ***)
  X86_STEPS_TAC MLDSA_NTT_WINDOWS_TMC_EXEC (17--30) THEN

(*** Handle the MAYCHANGE clauses for ZMM register components ***)
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN

(***Finalize the proof by establishing the final state conditions ***)
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let MLDSA_NTT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a zetas (zetas_list:int32 list) x pc stackpointer returnaddress.
        aligned 32 a /\
        aligned 32 zetas /\
        nonoverlapping (word pc,LENGTH mldsa_ntt_windows_mc) (a, 1024) /\
        nonoverlapping (word pc,LENGTH mldsa_ntt_windows_mc) (zetas, 2496) /\
        nonoverlapping (a, 1024) (zetas, 2496) /\
        nonoverlapping (word_sub stackpointer (word 176),184) (a, 1024) /\
        nonoverlapping (word_sub stackpointer (word 176),176) (zetas, 2496) /\
        nonoverlapping (word pc,LENGTH mldsa_ntt_windows_mc)
                       (word_sub stackpointer (word 176),176)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) mldsa_ntt_windows_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a; zetas] s /\
                   wordlist_from_memory(zetas,624) s = MAP (iword: int -> 32 word) mldsa_complete_qdata /\
                   (!i. i < 256 ==> abs(ival(x i)) <= &8380416) /\
                   !i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           x i)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   (!i. i < 256
                             ==> let zi =
                           read(memory :> bytes32(word_add a (word(4 * i)))) s in
                           (ival zi == mldsa_forward_ntt (ival o x) i) (mod &8380417) /\
                           abs(ival zi) <= &42035261))
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 176),176)] ,,
              MAYCHANGE [memory :> bytes(a,1024)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
  (CONV_RULE TWEAK_CONV MLDSA_NTT_NOIBT_WINDOWS_SUBROUTINE_CORRECT)));;
