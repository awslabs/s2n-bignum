(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of polynomial coefficients producing centered remainders.       *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "x86/mldsa/mldsa_poly_reduce.o";;
 ****)

let mldsa_poly_reduce_mc = define_assert_from_elf "mldsa_poly_reduce_mc" "x86/mldsa/mldsa_poly_reduce.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x01; 0xe0; 0x7f; 0x00;
                           (* MOV (% eax) (Imm32 (word 8380417)) *)
  0x66; 0x0f; 0x6e; 0xc0;  (* MOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0x00; 0x00; 0x40; 0x00;
                           (* MOV (% eax) (Imm32 (word 4194304)) *)
  0x66; 0x0f; 0x6e; 0xc8;  (* MOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
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
  0xc5; 0x5d; 0xfe; 0xe1;  (* VPADDD (%_% ymm12) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x55; 0xfe; 0xe9;  (* VPADDD (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x4d; 0xfe; 0xf1;  (* VPADDD (%_% ymm14) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x45; 0xfe; 0xf9;  (* VPADDD (%_% ymm15) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x72; 0xe4; 0x17;
                           (* VPSRAD (%_% ymm12) (%_% ymm12) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x15; 0x72; 0xe5; 0x17;
                           (* VPSRAD (%_% ymm13) (%_% ymm13) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x0d; 0x72; 0xe6; 0x17;
                           (* VPSRAD (%_% ymm14) (%_% ymm14) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x05; 0x72; 0xe7; 0x17;
                           (* VPSRAD (%_% ymm15) (%_% ymm15) (Imm8 (word 23)) *)
  0xc4; 0x62; 0x1d; 0x40; 0xe0;
                           (* VPMULLD (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x62; 0x15; 0x40; 0xe8;
                           (* VPMULLD (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x40; 0xf0;
                           (* VPMULLD (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x62; 0x05; 0x40; 0xf8;
                           (* VPMULLD (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe4;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf6;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xff;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm15) *)
  0xc5; 0x3d; 0xfe; 0xe1;  (* VPADDD (%_% ymm12) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x35; 0xfe; 0xe9;  (* VPADDD (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x2d; 0xfe; 0xf1;  (* VPADDD (%_% ymm14) (%_% ymm10) (%_% ymm1) *)
  0xc5; 0x25; 0xfe; 0xf9;  (* VPADDD (%_% ymm15) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x72; 0xe4; 0x17;
                           (* VPSRAD (%_% ymm12) (%_% ymm12) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x15; 0x72; 0xe5; 0x17;
                           (* VPSRAD (%_% ymm13) (%_% ymm13) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x0d; 0x72; 0xe6; 0x17;
                           (* VPSRAD (%_% ymm14) (%_% ymm14) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x05; 0x72; 0xe7; 0x17;
                           (* VPSRAD (%_% ymm15) (%_% ymm15) (Imm8 (word 23)) *)
  0xc4; 0x62; 0x1d; 0x40; 0xe0;
                           (* VPMULLD (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x62; 0x15; 0x40; 0xe8;
                           (* VPMULLD (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x40; 0xf0;
                           (* VPMULLD (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x62; 0x05; 0x40; 0xf8;
                           (* VPMULLD (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xd6;
                           (* VPSUBD (%_% ymm10) (%_% ymm10) (%_% ymm14) *)
  0xc4; 0x41; 0x25; 0xfa; 0xdf;
                           (* VPSUBD (%_% ymm11) (%_% ymm11) (%_% ymm15) *)
  0xc5; 0xfd; 0x7f; 0x27;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x6f; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0x77; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0x7f; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm10) *)
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
  0xc5; 0x5d; 0xfe; 0xe1;  (* VPADDD (%_% ymm12) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x55; 0xfe; 0xe9;  (* VPADDD (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x4d; 0xfe; 0xf1;  (* VPADDD (%_% ymm14) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x45; 0xfe; 0xf9;  (* VPADDD (%_% ymm15) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x72; 0xe4; 0x17;
                           (* VPSRAD (%_% ymm12) (%_% ymm12) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x15; 0x72; 0xe5; 0x17;
                           (* VPSRAD (%_% ymm13) (%_% ymm13) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x0d; 0x72; 0xe6; 0x17;
                           (* VPSRAD (%_% ymm14) (%_% ymm14) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x05; 0x72; 0xe7; 0x17;
                           (* VPSRAD (%_% ymm15) (%_% ymm15) (Imm8 (word 23)) *)
  0xc4; 0x62; 0x1d; 0x40; 0xe0;
                           (* VPMULLD (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x62; 0x15; 0x40; 0xe8;
                           (* VPMULLD (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x40; 0xf0;
                           (* VPMULLD (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x62; 0x05; 0x40; 0xf8;
                           (* VPMULLD (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe4;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf6;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xff;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm15) *)
  0xc5; 0x3d; 0xfe; 0xe1;  (* VPADDD (%_% ymm12) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x35; 0xfe; 0xe9;  (* VPADDD (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x2d; 0xfe; 0xf1;  (* VPADDD (%_% ymm14) (%_% ymm10) (%_% ymm1) *)
  0xc5; 0x25; 0xfe; 0xf9;  (* VPADDD (%_% ymm15) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x72; 0xe4; 0x17;
                           (* VPSRAD (%_% ymm12) (%_% ymm12) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x15; 0x72; 0xe5; 0x17;
                           (* VPSRAD (%_% ymm13) (%_% ymm13) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x0d; 0x72; 0xe6; 0x17;
                           (* VPSRAD (%_% ymm14) (%_% ymm14) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x05; 0x72; 0xe7; 0x17;
                           (* VPSRAD (%_% ymm15) (%_% ymm15) (Imm8 (word 23)) *)
  0xc4; 0x62; 0x1d; 0x40; 0xe0;
                           (* VPMULLD (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x62; 0x15; 0x40; 0xe8;
                           (* VPMULLD (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x40; 0xf0;
                           (* VPMULLD (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x62; 0x05; 0x40; 0xf8;
                           (* VPMULLD (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xd6;
                           (* VPSUBD (%_% ymm10) (%_% ymm10) (%_% ymm14) *)
  0xc4; 0x41; 0x25; 0xfa; 0xdf;
                           (* VPSUBD (%_% ymm11) (%_% ymm11) (%_% ymm15) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm10) *)
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
  0xc5; 0x5d; 0xfe; 0xe1;  (* VPADDD (%_% ymm12) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x55; 0xfe; 0xe9;  (* VPADDD (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x4d; 0xfe; 0xf1;  (* VPADDD (%_% ymm14) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x45; 0xfe; 0xf9;  (* VPADDD (%_% ymm15) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x72; 0xe4; 0x17;
                           (* VPSRAD (%_% ymm12) (%_% ymm12) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x15; 0x72; 0xe5; 0x17;
                           (* VPSRAD (%_% ymm13) (%_% ymm13) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x0d; 0x72; 0xe6; 0x17;
                           (* VPSRAD (%_% ymm14) (%_% ymm14) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x05; 0x72; 0xe7; 0x17;
                           (* VPSRAD (%_% ymm15) (%_% ymm15) (Imm8 (word 23)) *)
  0xc4; 0x62; 0x1d; 0x40; 0xe0;
                           (* VPMULLD (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x62; 0x15; 0x40; 0xe8;
                           (* VPMULLD (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x40; 0xf0;
                           (* VPMULLD (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x62; 0x05; 0x40; 0xf8;
                           (* VPMULLD (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe4;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf6;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xff;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm15) *)
  0xc5; 0x3d; 0xfe; 0xe1;  (* VPADDD (%_% ymm12) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x35; 0xfe; 0xe9;  (* VPADDD (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x2d; 0xfe; 0xf1;  (* VPADDD (%_% ymm14) (%_% ymm10) (%_% ymm1) *)
  0xc5; 0x25; 0xfe; 0xf9;  (* VPADDD (%_% ymm15) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x72; 0xe4; 0x17;
                           (* VPSRAD (%_% ymm12) (%_% ymm12) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x15; 0x72; 0xe5; 0x17;
                           (* VPSRAD (%_% ymm13) (%_% ymm13) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x0d; 0x72; 0xe6; 0x17;
                           (* VPSRAD (%_% ymm14) (%_% ymm14) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x05; 0x72; 0xe7; 0x17;
                           (* VPSRAD (%_% ymm15) (%_% ymm15) (Imm8 (word 23)) *)
  0xc4; 0x62; 0x1d; 0x40; 0xe0;
                           (* VPMULLD (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x62; 0x15; 0x40; 0xe8;
                           (* VPMULLD (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x40; 0xf0;
                           (* VPMULLD (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x62; 0x05; 0x40; 0xf8;
                           (* VPMULLD (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xd6;
                           (* VPSUBD (%_% ymm10) (%_% ymm10) (%_% ymm14) *)
  0xc4; 0x41; 0x25; 0xfa; 0xdf;
                           (* VPSUBD (%_% ymm11) (%_% ymm11) (%_% ymm15) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,512))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,544))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,576))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,608))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,640))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,672))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,704))) (%_% ymm10) *)
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
  0xc5; 0x5d; 0xfe; 0xe1;  (* VPADDD (%_% ymm12) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x55; 0xfe; 0xe9;  (* VPADDD (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x4d; 0xfe; 0xf1;  (* VPADDD (%_% ymm14) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x45; 0xfe; 0xf9;  (* VPADDD (%_% ymm15) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x72; 0xe4; 0x17;
                           (* VPSRAD (%_% ymm12) (%_% ymm12) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x15; 0x72; 0xe5; 0x17;
                           (* VPSRAD (%_% ymm13) (%_% ymm13) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x0d; 0x72; 0xe6; 0x17;
                           (* VPSRAD (%_% ymm14) (%_% ymm14) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x05; 0x72; 0xe7; 0x17;
                           (* VPSRAD (%_% ymm15) (%_% ymm15) (Imm8 (word 23)) *)
  0xc4; 0x62; 0x1d; 0x40; 0xe0;
                           (* VPMULLD (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x62; 0x15; 0x40; 0xe8;
                           (* VPMULLD (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x40; 0xf0;
                           (* VPMULLD (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x62; 0x05; 0x40; 0xf8;
                           (* VPMULLD (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe4;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf6;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xff;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm15) *)
  0xc5; 0x3d; 0xfe; 0xe1;  (* VPADDD (%_% ymm12) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x35; 0xfe; 0xe9;  (* VPADDD (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x2d; 0xfe; 0xf1;  (* VPADDD (%_% ymm14) (%_% ymm10) (%_% ymm1) *)
  0xc5; 0x25; 0xfe; 0xf9;  (* VPADDD (%_% ymm15) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x72; 0xe4; 0x17;
                           (* VPSRAD (%_% ymm12) (%_% ymm12) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x15; 0x72; 0xe5; 0x17;
                           (* VPSRAD (%_% ymm13) (%_% ymm13) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x0d; 0x72; 0xe6; 0x17;
                           (* VPSRAD (%_% ymm14) (%_% ymm14) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x05; 0x72; 0xe7; 0x17;
                           (* VPSRAD (%_% ymm15) (%_% ymm15) (Imm8 (word 23)) *)
  0xc4; 0x62; 0x1d; 0x40; 0xe0;
                           (* VPMULLD (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x62; 0x15; 0x40; 0xe8;
                           (* VPMULLD (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x40; 0xf0;
                           (* VPMULLD (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x62; 0x05; 0x40; 0xf8;
                           (* VPMULLD (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc4;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xd6;
                           (* VPSUBD (%_% ymm10) (%_% ymm10) (%_% ymm14) *)
  0xc4; 0x41; 0x25; 0xfa; 0xdf;
                           (* VPSUBD (%_% ymm11) (%_% ymm11) (%_% ymm15) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,768))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,800))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,832))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,864))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,896))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,928))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,960))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,992))) (%_% ymm11) *)
  0xc3                     (* RET *)
];;

let mldsa_poly_reduce_tmc = define_trimmed "mldsa_poly_reduce_tmc" mldsa_poly_reduce_mc;;
let MLDSA_POLY_REDUCE_TMC_EXEC = X86_MK_CORE_EXEC_RULE mldsa_poly_reduce_tmc;;

(* ------------------------------------------------------------------------- *)
(* Complete structured proof                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_REDUCE_CORRECT = prove
 (`!a x pc.
        aligned 32 a /\
        nonoverlapping (word pc,0x482) (a, 1024)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_poly_reduce_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                          x i)
             (\s. read RIP s = word(pc + 0x482) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes32
                                 (word_add a (word(4 * i)))) s) =
                          ival(mldsa_barred (x i)))
             (MAYCHANGE [RIP] ,, MAYCHANGE [ZMM0; ZMM1; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
              MAYCHANGE [RAX] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bytes(a,1024)])`,

  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int32`; `pc:num`] THEN

  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; fst MLDSA_POLY_REDUCE_TMC_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Manually expand the cases in the hypotheses ***)

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN

  REWRITE_TAC [SOME_FLAGS; fst MLDSA_POLY_REDUCE_TMC_EXEC] THEN

  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `init_ymm1:int256` `read YMM1` THEN

  ENSURES_INIT_TAC "s0" THEN

  (*** Restructure memory to match 256-bit loads ***)

  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 3
              (subst[mk_small_numeral(32*n),`n:num`]
                    `read (memory :> bytes256(word_add a (word n))) s0`))
              (0--31))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
  STRIP_TAC THEN

  (let lemma = WORD_BLAST `(word_zx:int256->int128) x = word_subword x (0,128)` in
   MAP_EVERY (fun n ->
      X86_STEPS_TAC MLDSA_POLY_REDUCE_TMC_EXEC [n] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[lemma]) THEN
      SIMD_SIMPLIFY_TAC[mldsa_barred])
             (1--198)) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Reverse the restructuring by splitting the 256-bit words back to 32-bit ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
     CONV_RULE(SIMD_SIMPLIFY_CONV[mldsa_barred]) o
     CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
     check (can (term_match [] `read qqq s198:int256 = xxx`) o concl))) THEN

  (*** Now the result is just a replicated instance of our lemma ***)

  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_STATE_TAC "s198" THEN
  REWRITE_TAC[GSYM mldsa_barred]);;

let MLDSA_POLY_REDUCE_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mldsa_poly_reduce_tmc) (a,1024) /\
        nonoverlapping (stackpointer,8) (a,1024)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_poly_reduce_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                          x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes32
                                 (word_add a (word(4 * i)))) s) =
                          ival(mldsa_barred (x i)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_poly_reduce_tmc MLDSA_REDUCE_CORRECT);;

let MLDSA_POLY_REDUCE_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mldsa_poly_reduce_mc) (a,1024) /\
        nonoverlapping (stackpointer,8) (a,1024)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_poly_reduce_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                          x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes32
                                 (word_add a (word(4 * i)))) s) =
                          ival(mldsa_barred (x i)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLY_REDUCE_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* General lemmas to eventually put elsewhere.                               *)
(* ------------------------------------------------------------------------- *)

let READ_ZMM_BOTTOM_QUARTER = prove
 (`!zmmx:(S,512 word)component s.
     read (zmmx :> bottomhalf :> bottomhalf) s = word_zx (read zmmx s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bottomhalf; READ_SUBWORD] THEN
  REWRITE_TAC[DIMINDEX_512; DIMINDEX_256; DIMINDEX_128] THEN
  CONV_TAC WORD_BLAST);;

let READ_ZMM_BOTTOM_QUARTER' = prove
 (`!zmmx:(S,512 word)component s.
     read (zmmx :> bottomhalf :> bottomhalf) s =
     word_zx (read (zmmx :> zerotop_256) s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bottomhalf; READ_SUBWORD;
              READ_ZEROTOP_256] THEN
  REWRITE_TAC[DIMINDEX_512; DIMINDEX_256; DIMINDEX_128] THEN
  CONV_TAC WORD_BLAST);;

let MAYCHANGE_ZMM_QUARTER = prove
 (`MAYCHANGE [ZMM6] =
   MAYCHANGE [ZMM6 :> tophalf] ,,
   MAYCHANGE [ZMM6 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM6 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [ZMM7] =
   MAYCHANGE [ZMM7 :> tophalf] ,,
   MAYCHANGE [ZMM7 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM7 :> bottomhalf :> bottomhalf] /\
  MAYCHANGE [ZMM8] =
   MAYCHANGE [ZMM8 :> tophalf] ,,
   MAYCHANGE [ZMM8 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM8 :> bottomhalf :> bottomhalf] /\
  MAYCHANGE [ZMM9] =
   MAYCHANGE [ZMM9 :> tophalf] ,,
   MAYCHANGE [ZMM9 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM9 :> bottomhalf :> bottomhalf] /\
  MAYCHANGE [ZMM10] =
   MAYCHANGE [ZMM10 :> tophalf] ,,
   MAYCHANGE [ZMM10 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM10 :> bottomhalf :> bottomhalf] /\
  MAYCHANGE [ZMM11] =
   MAYCHANGE [ZMM11 :> tophalf] ,,
   MAYCHANGE [ZMM11 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM11 :> bottomhalf :> bottomhalf] /\
  MAYCHANGE [ZMM12] =
   MAYCHANGE [ZMM12 :> tophalf] ,,
   MAYCHANGE [ZMM12 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM12 :> bottomhalf :> bottomhalf] /\
  MAYCHANGE [ZMM13] =
   MAYCHANGE [ZMM13 :> tophalf] ,,
   MAYCHANGE [ZMM13 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM13 :> bottomhalf :> bottomhalf] /\
  MAYCHANGE [ZMM14] =
   MAYCHANGE [ZMM14 :> tophalf] ,,
   MAYCHANGE [ZMM14 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM14 :> bottomhalf :> bottomhalf] /\
  MAYCHANGE [ZMM15] =
   MAYCHANGE [ZMM15 :> tophalf] ,,
   MAYCHANGE [ZMM15 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM15 :> bottomhalf :> bottomhalf]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MAYCHANGE_SING] THEN
  (W(MP_TAC o PART_MATCH (rand o rand) ASSIGNS_TOPHALF_BOTTOMHALF o
    lhand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC VALID_COMPONENT_CONV ; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (rand o rand) ASSIGNS_TOPHALF_BOTTOMHALF o
    lhand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC VALID_COMPONENT_CONV ; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[COMPONENT_COMPOSE_ASSOC]));;

let MAYCHANGE_YMM_SSE_QUARTER = prove
 (`MAYCHANGE [YMM6_SSE] =
   MAYCHANGE [ZMM6 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM6 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM7_SSE] =
   MAYCHANGE [ZMM7 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM7 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM8_SSE] =
   MAYCHANGE [ZMM8 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM8 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM9_SSE] =
   MAYCHANGE [ZMM9 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM9 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM10_SSE] =
   MAYCHANGE [ZMM10 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM10 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM11_SSE] =
   MAYCHANGE [ZMM11 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM11 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM12_SSE] =
   MAYCHANGE [ZMM12 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM12 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM13_SSE] =
   MAYCHANGE [ZMM13 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM13 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM14_SSE] =
   MAYCHANGE [ZMM14 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM14 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM15_SSE] =
   MAYCHANGE [ZMM15 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM15 :> bottomhalf :> bottomhalf]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bottom_256; YMM6_SSE; YMM7_SSE; YMM8_SSE; YMM9_SSE;
    YMM10_SSE; YMM11_SSE; YMM12_SSE; YMM13_SSE;
    YMM14_SSE; YMM15_SSE] THEN
  CONV_TAC SYM_CONV THEN
  REWRITE_TAC[MAYCHANGE_SING; COMPONENT_COMPOSE_ASSOC] THEN
  MATCH_MP_TAC ASSIGNS_TOPHALF_BOTTOMHALF THEN
  CONV_TAC VALID_COMPONENT_CONV);;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let mldsa_poly_reduce_windows_mc = define_from_elf
   "mldsa_poly_reduce_windows_mc" "x86/mldsa/mldsa_poly_reduce.obj";;

let mldsa_poly_reduce_windows_tmc =
  define_trimmed "mldsa_poly_reduce_windows_tmc" mldsa_poly_reduce_windows_mc;;

let MLDSA_POLY_REDUCE_WINDOWS_TMC_EXEC =
  X86_MK_EXEC_RULE mldsa_poly_reduce_windows_tmc;;

let MLDSA_POLY_REDUCE_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mldsa_poly_reduce_windows_tmc) (a,1024) /\
        nonoverlapping (word_sub stackpointer (word 176),184) (a,1024) /\
        nonoverlapping (word pc,LENGTH mldsa_poly_reduce_windows_tmc)
                       (word_sub stackpointer (word 176),176)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) mldsa_poly_reduce_windows_tmc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a] s /\
                   !i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           x i)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   !i. i < 256
                       ==> ival(read(memory :> bytes32
                                  (word_add a (word(4 * i)))) s) =
                           ival(mldsa_barred (x i)))
              (MAYCHANGE [RSP] ,,
               WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(word_sub stackpointer (word 176),176)] ,,
               MAYCHANGE [memory :> bytes(a,1024)])`,
  REPLICATE_TAC 3 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 176 THEN REPEAT GEN_TAC THEN

  REWRITE_TAC[fst MLDSA_POLY_REDUCE_WINDOWS_TMC_EXEC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[WINDOWS_C_ARGUMENTS] THEN
  REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN

  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
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
  X86_STEPS_TAC MLDSA_POLY_REDUCE_WINDOWS_TMC_EXEC (1--13) THEN

  MP_TAC(SPECL [`a:int64`; `x:num->int32`; `pc + 81`]
    MLDSA_REDUCE_CORRECT) THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN

  X86_BIGSTEP_TAC MLDSA_POLY_REDUCE_WINDOWS_TMC_EXEC "s14" THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
     (BYTES_LOADED_SUBPROGRAM_RULE mldsa_poly_reduce_windows_tmc
     (REWRITE_RULE[BUTLAST_CLAUSES]
      (AP_TERM `BUTLAST:byte list->byte list` mldsa_poly_reduce_tmc))
     81));
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN

  MAP_EVERY ABBREV_TAC
   [`ymm6_epilog = read YMM6 s14`;
    `ymm7_epilog = read YMM7 s14`;
    `ymm8_epilog = read YMM8 s14`;
    `ymm9_epilog = read YMM9 s14`;
    `ymm10_epilog = read YMM10 s14`;
    `ymm11_epilog = read YMM11 s14`;
    `ymm12_epilog = read YMM12 s14`;
    `ymm13_epilog = read YMM13 s14`;
    `ymm14_epilog = read YMM14 s14`;
    `ymm15_epilog = read YMM15 s14`] THEN

  X86_STEPS_TAC MLDSA_POLY_REDUCE_WINDOWS_TMC_EXEC (15--27) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let MLDSA_POLY_REDUCE_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mldsa_poly_reduce_windows_mc) (a,1024) /\
        nonoverlapping (word_sub stackpointer (word 176),184) (a,1024) /\
        nonoverlapping (word pc,LENGTH mldsa_poly_reduce_windows_mc)
                       (word_sub stackpointer (word 176),176)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) mldsa_poly_reduce_windows_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a] s /\
                   !i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           x i)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   !i. i < 256
                       ==> ival(read(memory :> bytes32
                                  (word_add a (word(4 * i)))) s) =
                           ival(mldsa_barred (x i)))
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 176),176)] ,,
              MAYCHANGE [memory :> bytes(a,1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLY_REDUCE_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;
