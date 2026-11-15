(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f1600 permutation for SHA3, with AVX2, of original design.         *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/keccak_spec.ml";;
needs "x86/proofs/utils/keccak_avx2.ml";;

(**** print_literal_relocs_from_elf
        ~map_symbol_name:(fun s -> if s = "WHOLE_READONLY"
                                   then "sha3_keccak_f1600_alt2_data"
                                   else s ^ "_data")
        "x86/sha3/sha3_keccak_f1600_alt2.o";;
 ****)

(*** The rotation table after the code (in .rodata) is read RIP-relatively
 *** through rax, so the code is a function of pc and the address of the
 *** table, sha3_keccak_f1600_alt2_data
 ***)

let sha3_keccak_f1600_alt2_mc,(sha3_keccak_f1600_alt2_data::_) =
  define_assert_relocs_from_elf
   ~map_symbol_name:(fun s -> if s = "WHOLE_READONLY"
                              then "sha3_keccak_f1600_alt2_data"
                              else s ^ "_data")
   "sha3_keccak_f1600_alt2_mc" "x86/sha3/sha3_keccak_f1600_alt2.o"
(fun b ADDR -> [b[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x8d; 0x05]; ADDR ("sha3_keccak_f1600_alt2_data",(-4)); b[
                           (* LEA (% rax)
(Riprel (word_sx (iword (&sha3_keccak_f1600_alt2_data - (&pc + &11))))) *)
  0xc4; 0xe2; 0x7d; 0x59; 0x07;
                           (* VPBROADCASTQ (%_% ymm0) (Memop Quadword (%% (rdi,0))) *)
  0xc5; 0xfe; 0x6f; 0x4f; 0x08;
                           (* VMOVDQU (%_% ymm1) (Memop Word256 (%% (rdi,8))) *)
  0xc5; 0xfa; 0x7e; 0x57; 0x30;
                           (* VMOVQ (%_% xmm2) (Memop Quadword (%% (rdi,48))) *)
  0xc4; 0xe3; 0xe9; 0x22; 0x57; 0x60; 0x01;
                           (* VPINSRQ (%_% xmm2) (%_% xmm2) (Memop Quadword (%% (rdi,96))) (Imm8 (word 1)) *)
  0xc5; 0xfa; 0x7e; 0xbf; 0x90; 0x00; 0x00; 0x00;
                           (* VMOVQ (%_% xmm7) (Memop Quadword (%% (rdi,144))) *)
  0xc4; 0xe3; 0xc1; 0x22; 0xbf; 0xc0; 0x00; 0x00; 0x00; 0x01;
                           (* VPINSRQ (%_% xmm7) (%_% xmm7) (Memop Quadword (%% (rdi,192))) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x6d; 0x38; 0xd7; 0x01;
                           (* VINSERTI128 (%_% ymm2) (%_% ymm2) (%_% xmm7) (Imm8 (word 1)) *)
  0xc5; 0xfa; 0x7e; 0x5f; 0x58;
                           (* VMOVQ (%_% xmm3) (Memop Quadword (%% (rdi,88))) *)
  0xc4; 0xe3; 0xe1; 0x22; 0x9f; 0xb0; 0x00; 0x00; 0x00; 0x01;
                           (* VPINSRQ (%_% xmm3) (%_% xmm3) (Memop Quadword (%% (rdi,176))) (Imm8 (word 1)) *)
  0xc5; 0xfa; 0x7e; 0x7f; 0x40;
                           (* VMOVQ (%_% xmm7) (Memop Quadword (%% (rdi,64))) *)
  0xc4; 0xe3; 0xc1; 0x22; 0xbf; 0x98; 0x00; 0x00; 0x00; 0x01;
                           (* VPINSRQ (%_% xmm7) (%_% xmm7) (Memop Quadword (%% (rdi,152))) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x65; 0x38; 0xdf; 0x01;
                           (* VINSERTI128 (%_% ymm3) (%_% ymm3) (%_% xmm7) (Imm8 (word 1)) *)
  0xc5; 0xfa; 0x7e; 0xa7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rdi,128))) *)
  0xc4; 0xe3; 0xd9; 0x22; 0x67; 0x38; 0x01;
                           (* VPINSRQ (%_% xmm4) (%_% xmm4) (Memop Quadword (%% (rdi,56))) (Imm8 (word 1)) *)
  0xc5; 0xfa; 0x7e; 0xbf; 0xb8; 0x00; 0x00; 0x00;
                           (* VMOVQ (%_% xmm7) (Memop Quadword (%% (rdi,184))) *)
  0xc4; 0xe3; 0xc1; 0x22; 0x7f; 0x70; 0x01;
                           (* VPINSRQ (%_% xmm7) (%_% xmm7) (Memop Quadword (%% (rdi,112))) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe7; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm7) (Imm8 (word 1)) *)
  0xc5; 0xfa; 0x7e; 0xaf; 0xa8; 0x00; 0x00; 0x00;
                           (* VMOVQ (%_% xmm5) (Memop Quadword (%% (rdi,168))) *)
  0xc4; 0xe3; 0xd1; 0x22; 0xaf; 0x88; 0x00; 0x00; 0x00; 0x01;
                           (* VPINSRQ (%_% xmm5) (%_% xmm5) (Memop Quadword (%% (rdi,136))) (Imm8 (word 1)) *)
  0xc5; 0xfa; 0x7e; 0x7f; 0x68;
                           (* VMOVQ (%_% xmm7) (Memop Quadword (%% (rdi,104))) *)
  0xc4; 0xe3; 0xc1; 0x22; 0x7f; 0x48; 0x01;
                           (* VPINSRQ (%_% xmm7) (%_% xmm7) (Memop Quadword (%% (rdi,72))) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x55; 0x38; 0xef; 0x01;
                           (* VINSERTI128 (%_% ymm5) (%_% ymm5) (%_% xmm7) (Imm8 (word 1)) *)
  0xc5; 0xfa; 0x7e; 0x77; 0x28;
                           (* VMOVQ (%_% xmm6) (Memop Quadword (%% (rdi,40))) *)
  0xc4; 0xe3; 0xc9; 0x22; 0x77; 0x50; 0x01;
                           (* VPINSRQ (%_% xmm6) (%_% xmm6) (Memop Quadword (%% (rdi,80))) (Imm8 (word 1)) *)
  0xc5; 0xfa; 0x7e; 0x7f; 0x78;
                           (* VMOVQ (%_% xmm7) (Memop Quadword (%% (rdi,120))) *)
  0xc4; 0xe3; 0xc1; 0x22; 0xbf; 0xa0; 0x00; 0x00; 0x00; 0x01;
                           (* VPINSRQ (%_% xmm7) (%_% xmm7) (Memop Quadword (%% (rdi,160))) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xb9; 0x18; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 24)) *)
  0x66; 0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0xc5; 0xcd; 0x6c; 0xfe;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm6) (%_% ymm6) *)
  0xc5; 0x75; 0xef; 0xc2;  (* VPXOR (%_% ymm8) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x65; 0xef; 0xcc;  (* VPXOR (%_% ymm9) (%_% ymm3) (%_% ymm4) *)
  0xc4; 0x62; 0x7d; 0x59; 0x16;
                           (* VPBROADCASTQ (%_% ymm10) (Memop Quadword (%% (rsi,0))) *)
  0xc5; 0x4d; 0x6d; 0xde;  (* VPUNPCKHQDQ (%_% ymm11) (%_% ymm6) (%_% ymm6) *)
  0xc5; 0x3d; 0xef; 0xc5;  (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0xc1; 0x45; 0xef; 0xfb;
                           (* VPXOR (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x63; 0xfd; 0x00; 0xcf; 0x4e;
                           (* VPERMQ (%_% ymm9) (%_% ymm7) (Imm8 (word 78)) *)
  0xc4; 0xc1; 0x25; 0x73; 0xd0; 0x3f;
                           (* VPSRLQ (%_% ymm11) (%_% ymm8) (Imm8 (word 63)) *)
  0xc4; 0x41; 0x3d; 0xd4; 0xe0;
                           (* VPADDQ (%_% ymm12) (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x41; 0x25; 0xeb; 0xdc;
                           (* VPOR (%_% ymm11) (%_% ymm11) (%_% ymm12) *)
  0xc4; 0x43; 0xfd; 0x00; 0xe0; 0x90;
                           (* VPERMQ (%_% ymm12) (%_% ymm8) (Imm8 (word 144)) *)
  0xc4; 0x43; 0xfd; 0x00; 0xeb; 0x39;
                           (* VPERMQ (%_% ymm13) (%_% ymm11) (Imm8 (word 57)) *)
  0xc4; 0xc1; 0x45; 0xef; 0xf9;
                           (* VPXOR (%_% ymm7) (%_% ymm7) (%_% ymm9) *)
  0xc4; 0x43; 0xfd; 0x00; 0xcb; 0x00;
                           (* VPERMQ (%_% ymm9) (%_% ymm11) (Imm8 (word 0)) *)
  0xc5; 0xc5; 0xef; 0xf8;  (* VPXOR (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc4; 0x43; 0xfd; 0x00; 0xc0; 0xff;
                           (* VPERMQ (%_% ymm8) (%_% ymm8) (Imm8 (word 255)) *)
  0xc5; 0xa5; 0x73; 0xd7; 0x3f;
                           (* VPSRLQ (%_% ymm11) (%_% ymm7) (Imm8 (word 63)) *)
  0xc5; 0x45; 0xd4; 0xf7;  (* VPADDQ (%_% ymm14) (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xe3; 0x1d; 0x02; 0xff; 0x03;
                           (* VPBLENDD (%_% ymm7) (%_% ymm12) (%_% ymm7) (Imm8 (word 3)) *)
  0xc4; 0x41; 0x25; 0xeb; 0xde;
                           (* VPOR (%_% ymm11) (%_% ymm11) (%_% ymm14) *)
  0xc4; 0x43; 0x15; 0x02; 0xdb; 0xc0;
                           (* VPBLENDD (%_% ymm11) (%_% ymm13) (%_% ymm11) (Imm8 (word 192)) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0xc1; 0x45; 0xef; 0xfb;
                           (* VPXOR (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x4d; 0xef; 0xc8;
                           (* VPXOR (%_% ymm9) (%_% ymm6) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xef; 0xc0;
                           (* VPXOR (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc5; 0x65; 0xef; 0xdf;  (* VPXOR (%_% ymm11) (%_% ymm3) (%_% ymm7) *)
  0xc5; 0x55; 0xef; 0xe7;  (* VPXOR (%_% ymm12) (%_% ymm5) (%_% ymm7) *)
  0xc5; 0x75; 0xef; 0xef;  (* VPXOR (%_% ymm13) (%_% ymm1) (%_% ymm7) *)
  0xc4; 0x62; 0x9d; 0x45; 0xb0; 0x20; 0x01; 0x00; 0x00;
                           (* VPSRLVQ (%_% ymm14) (%_% ymm12) (Memop Word256 (%% (rax,288))) *)
  0xc4; 0x62; 0x9d; 0x47; 0xa0; 0x00; 0x01; 0x00; 0x00;
                           (* VPSLLVQ (%_% ymm12) (%_% ymm12) (Memop Word256 (%% (rax,256))) *)
  0xc5; 0x5d; 0xef; 0xff;  (* VPXOR (%_% ymm15) (%_% ymm4) (%_% ymm7) *)
  0xc4; 0xe2; 0xb5; 0x47; 0x80; 0x40; 0x01; 0x00; 0x00;
                           (* VPSLLVQ (%_% ymm0) (%_% ymm9) (Memop Word256 (%% (rax,320))) *)
  0xc4; 0xe2; 0xa5; 0x45; 0x88; 0xa0; 0x00; 0x00; 0x00;
                           (* VPSRLVQ (%_% ymm1) (%_% ymm11) (Memop Word256 (%% (rax,160))) *)
  0xc4; 0x41; 0x1d; 0xeb; 0xe6;
                           (* VPOR (%_% ymm12) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0x62; 0xb5; 0x45; 0x88; 0x60; 0x01; 0x00; 0x00;
                           (* VPSRLVQ (%_% ymm9) (%_% ymm9) (Memop Word256 (%% (rax,352))) *)
  0xc4; 0x62; 0xa5; 0x47; 0x98; 0x80; 0x00; 0x00; 0x00;
                           (* VPSLLVQ (%_% ymm11) (%_% ymm11) (Memop Word256 (%% (rax,128))) *)
  0xc4; 0x43; 0xfd; 0x00; 0xe4; 0x1b;
                           (* VPERMQ (%_% ymm12) (%_% ymm12) (Imm8 (word 27)) *)
  0xc4; 0x41; 0x7d; 0xeb; 0xc9;
                           (* VPOR (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc5; 0x25; 0xeb; 0xd9;  (* VPOR (%_% ymm11) (%_% ymm11) (%_% ymm1) *)
  0xc5; 0xed; 0xef; 0xff;  (* VPXOR (%_% ymm7) (%_% ymm2) (%_% ymm7) *)
  0xc4; 0x43; 0xfd; 0x00; 0xc9; 0x8d;
                           (* VPERMQ (%_% ymm9) (%_% ymm9) (Imm8 (word 141)) *)
  0xc4; 0x62; 0x95; 0x45; 0x70; 0x20;
                           (* VPSRLVQ (%_% ymm14) (%_% ymm13) (Memop Word256 (%% (rax,32))) *)
  0xc4; 0x62; 0x95; 0x47; 0x28;
                           (* VPSLLVQ (%_% ymm13) (%_% ymm13) (Memop Word256 (%% (rax,0))) *)
  0xc4; 0x43; 0xfd; 0x00; 0xdb; 0x8d;
                           (* VPERMQ (%_% ymm11) (%_% ymm11) (Imm8 (word 141)) *)
  0xc4; 0xe2; 0x85; 0x45; 0x80; 0xe0; 0x00; 0x00; 0x00;
                           (* VPSRLVQ (%_% ymm0) (%_% ymm15) (Memop Word256 (%% (rax,224))) *)
  0xc4; 0x62; 0x85; 0x47; 0xb8; 0xc0; 0x00; 0x00; 0x00;
                           (* VPSLLVQ (%_% ymm15) (%_% ymm15) (Memop Word256 (%% (rax,192))) *)
  0xc4; 0x41; 0x15; 0xeb; 0xee;
                           (* VPOR (%_% ymm13) (%_% ymm13) (%_% ymm14) *)
  0xc5; 0x05; 0xeb; 0xf0;  (* VPOR (%_% ymm14) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0x43; 0xfd; 0x00; 0xed; 0x72;
                           (* VPERMQ (%_% ymm13) (%_% ymm13) (Imm8 (word 114)) *)
  0xc4; 0x43; 0x1d; 0x02; 0xfe; 0x03;
                           (* VPBLENDD (%_% ymm15) (%_% ymm12) (%_% ymm14) (Imm8 (word 3)) *)
  0xc4; 0xc3; 0x1d; 0x02; 0xc6; 0xc0;
                           (* VPBLENDD (%_% ymm0) (%_% ymm12) (%_% ymm14) (Imm8 (word 192)) *)
  0xc4; 0xc3; 0x35; 0x02; 0xcb; 0xc0;
                           (* VPBLENDD (%_% ymm1) (%_% ymm9) (%_% ymm11) (Imm8 (word 192)) *)
  0xc4; 0xc3; 0x1d; 0x02; 0xd6; 0x0c;
                           (* VPBLENDD (%_% ymm2) (%_% ymm12) (%_% ymm14) (Imm8 (word 12)) *)
  0xc4; 0xc3; 0x35; 0x02; 0xdb; 0x30;
                           (* VPBLENDD (%_% ymm3) (%_% ymm9) (%_% ymm11) (Imm8 (word 48)) *)
  0xc4; 0xc3; 0x35; 0x02; 0xe3; 0x03;
                           (* VPBLENDD (%_% ymm4) (%_% ymm9) (%_% ymm11) (Imm8 (word 3)) *)
  0xc4; 0xe2; 0xc5; 0x47; 0x68; 0x40;
                           (* VPSLLVQ (%_% ymm5) (%_% ymm7) (Memop Word256 (%% (rax,64))) *)
  0xc4; 0x43; 0x1d; 0x02; 0xe6; 0x30;
                           (* VPBLENDD (%_% ymm12) (%_% ymm12) (%_% ymm14) (Imm8 (word 48)) *)
  0xc4; 0x43; 0x35; 0x02; 0xcb; 0x0c;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm11) (Imm8 (word 12)) *)
  0xc4; 0xe2; 0xc5; 0x45; 0x78; 0x60;
                           (* VPSRLVQ (%_% ymm7) (%_% ymm7) (Memop Word256 (%% (rax,96))) *)
  0xc4; 0x63; 0x6d; 0x02; 0xd9; 0xf0;
                           (* VPBLENDD (%_% ymm11) (%_% ymm2) (%_% ymm1) (Imm8 (word 240)) *)
  0xc4; 0x63; 0x1d; 0x02; 0xe4; 0x0f;
                           (* VPBLENDD (%_% ymm12) (%_% ymm12) (%_% ymm4) (Imm8 (word 15)) *)
  0xc4; 0x63; 0x7d; 0x02; 0xf3; 0x33;
                           (* VPBLENDD (%_% ymm14) (%_% ymm0) (%_% ymm3) (Imm8 (word 51)) *)
  0xc4; 0x43; 0x05; 0x02; 0xc9; 0xcc;
                           (* VPBLENDD (%_% ymm9) (%_% ymm15) (%_% ymm9) (Imm8 (word 204)) *)
  0xc5; 0xd5; 0xeb; 0xff;  (* VPOR (%_% ymm7) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0x41; 0x15; 0xdf; 0xfb;
                           (* VPANDN (%_% ymm15) (%_% ymm13) (%_% ymm11) *)
  0xc4; 0xc1; 0x1d; 0xdf; 0xc5;
                           (* VPANDN (%_% ymm0) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x35; 0xdf; 0xcc;
                           (* VPANDN (%_% ymm1) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc1; 0x0d; 0xdf; 0xd1;
                           (* VPANDN (%_% ymm2) (%_% ymm14) (%_% ymm9) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xdf; 0x3e;
                           (* VPERMQ (%_% ymm3) (%_% ymm7) (Imm8 (word 62)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe7; 0xf9;
                           (* VPERMQ (%_% ymm4) (%_% ymm7) (Imm8 (word 249)) *)
  0xc5; 0xa5; 0xef; 0xd2;  (* VPXOR (%_% ymm2) (%_% ymm11) (%_% ymm2) *)
  0xc5; 0x8d; 0xef; 0xc9;  (* VPXOR (%_% ymm1) (%_% ymm14) (%_% ymm1) *)
  0xc4; 0x41; 0x1d; 0xef; 0xe7;
                           (* VPXOR (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc5; 0x35; 0xef; 0xc8;  (* VPXOR (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0x63; 0x6d; 0x02; 0xf9; 0x30;
                           (* VPBLENDD (%_% ymm15) (%_% ymm2) (%_% ymm1) (Imm8 (word 48)) *)
  0xc4; 0xc3; 0x35; 0x02; 0xc4; 0x0c;
                           (* VPBLENDD (%_% ymm0) (%_% ymm9) (%_% ymm12) (Imm8 (word 12)) *)
  0xc4; 0xc3; 0x35; 0x02; 0xec; 0x03;
                           (* VPBLENDD (%_% ymm5) (%_% ymm9) (%_% ymm12) (Imm8 (word 3)) *)
  0xc4; 0xc3; 0x35; 0x02; 0xf4; 0x30;
                           (* VPBLENDD (%_% ymm6) (%_% ymm9) (%_% ymm12) (Imm8 (word 48)) *)
  0xc4; 0x41; 0x25; 0xdf; 0xde;
                           (* VPANDN (%_% ymm11) (%_% ymm11) (%_% ymm14) *)
  0xc4; 0x43; 0x5d; 0x02; 0xf0; 0xc0;
                           (* VPBLENDD (%_% ymm14) (%_% ymm4) (%_% ymm8) (Imm8 (word 192)) *)
  0xc4; 0xc3; 0x65; 0x02; 0xd8; 0x30;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm8) (Imm8 (word 48)) *)
  0xc4; 0xe3; 0x6d; 0x02; 0xe1; 0x03;
                           (* VPBLENDD (%_% ymm4) (%_% ymm2) (%_% ymm1) (Imm8 (word 3)) *)
  0xc4; 0x63; 0x05; 0x02; 0xfd; 0x0f;
                           (* VPBLENDD (%_% ymm15) (%_% ymm15) (%_% ymm5) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x15; 0xef; 0xdb;
                           (* VPXOR (%_% ymm11) (%_% ymm13) (%_% ymm11) *)
  0xc4; 0x63; 0x6d; 0x02; 0xe9; 0xc0;
                           (* VPBLENDD (%_% ymm13) (%_% ymm2) (%_% ymm1) (Imm8 (word 192)) *)
  0xc4; 0xe3; 0x5d; 0x02; 0xc0; 0xcc;
                           (* VPBLENDD (%_% ymm0) (%_% ymm4) (%_% ymm0) (Imm8 (word 204)) *)
  0xc4; 0xe3; 0x6d; 0x02; 0xc9; 0x0c;
                           (* VPBLENDD (%_% ymm1) (%_% ymm2) (%_% ymm1) (Imm8 (word 12)) *)
  0xc4; 0x63; 0x15; 0x02; 0xee; 0x33;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm6) (Imm8 (word 51)) *)
  0xc5; 0x8d; 0xdf; 0xd3;  (* VPANDN (%_% ymm2) (%_% ymm14) (%_% ymm3) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe0; 0x72;
                           (* VPERMQ (%_% ymm4) (%_% ymm0) (Imm8 (word 114)) *)
  0xc4; 0xc3; 0xfd; 0x00; 0xdd; 0x8d;
                           (* VPERMQ (%_% ymm3) (%_% ymm13) (Imm8 (word 141)) *)
  0xc4; 0x43; 0x35; 0x02; 0xcc; 0xc0;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm12) (Imm8 (word 192)) *)
  0xc5; 0x45; 0xef; 0xe2;  (* VPXOR (%_% ymm12) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0xc3; 0xfd; 0x00; 0xef; 0x1b;
                           (* VPERMQ (%_% ymm5) (%_% ymm15) (Imm8 (word 27)) *)
  0xc4; 0xc3; 0x75; 0x02; 0xd1; 0xf0;
                           (* VPBLENDD (%_% ymm2) (%_% ymm1) (%_% ymm9) (Imm8 (word 240)) *)
  0xc4; 0xc1; 0x45; 0xdf; 0xfe;
                           (* VPANDN (%_% ymm7) (%_% ymm7) (%_% ymm14) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xff; 0x00;
                           (* VPERMQ (%_% ymm7) (%_% ymm7) (Imm8 (word 0)) *)
  0xc5; 0xbd; 0xef; 0xff;  (* VPXOR (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0xc1; 0x45; 0xef; 0xc2;
                           (* VPXOR (%_% ymm0) (%_% ymm7) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0xe1;  (* VMOVDQA (%_% ymm1) (%_% ymm12) *)
  0xc5; 0x7d; 0x7f; 0xde;  (* VMOVDQA (%_% ymm6) (%_% ymm11) *)
  0x0f; 0x1f; 0x44; 0x00; 0x00;
                           (* NOP_N (Memop Doubleword (%%% (rax,0,rax))) *)
  0x48; 0x83; 0xc6; 0x08;  (* ADD (% rsi) (Imm8 (word 8)) *)
  0xff; 0xc9;              (* DEC (% ecx) *)
  0x0f; 0x85; 0xb4; 0xfd; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294966708)) *)
  0xc5; 0xf9; 0xd6; 0x07;  (* VMOVQ (Memop Quadword (%% (rdi,0))) (%_% xmm0) *)
  0xc5; 0xfe; 0x7f; 0x4f; 0x08;
                           (* VMOVDQU (Memop Word256 (%% (rdi,8))) (%_% ymm1) *)
  0xc5; 0xf9; 0xd6; 0x57; 0x30;
                           (* VMOVQ (Memop Quadword (%% (rdi,48))) (%_% xmm2) *)
  0xc4; 0xe3; 0xf9; 0x16; 0x57; 0x60; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,96))) (%_% xmm2) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x7d; 0x39; 0xd7; 0x01;
                           (* VEXTRACTI128 (%_% xmm7) (%_% ymm2) (Imm8 (word 1)) *)
  0xc5; 0xf9; 0xd6; 0xbf; 0x90; 0x00; 0x00; 0x00;
                           (* VMOVQ (Memop Quadword (%% (rdi,144))) (%_% xmm7) *)
  0xc4; 0xe3; 0xf9; 0x16; 0xbf; 0xc0; 0x00; 0x00; 0x00; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,192))) (%_% xmm7) (Imm8 (word 1)) *)
  0xc5; 0xf9; 0xd6; 0x5f; 0x58;
                           (* VMOVQ (Memop Quadword (%% (rdi,88))) (%_% xmm3) *)
  0xc4; 0xe3; 0xf9; 0x16; 0x9f; 0xb0; 0x00; 0x00; 0x00; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,176))) (%_% xmm3) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x7d; 0x39; 0xdf; 0x01;
                           (* VEXTRACTI128 (%_% xmm7) (%_% ymm3) (Imm8 (word 1)) *)
  0xc5; 0xf9; 0xd6; 0x7f; 0x40;
                           (* VMOVQ (Memop Quadword (%% (rdi,64))) (%_% xmm7) *)
  0xc4; 0xe3; 0xf9; 0x16; 0xbf; 0x98; 0x00; 0x00; 0x00; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,152))) (%_% xmm7) (Imm8 (word 1)) *)
  0xc5; 0xf9; 0xd6; 0xa7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVQ (Memop Quadword (%% (rdi,128))) (%_% xmm4) *)
  0xc4; 0xe3; 0xf9; 0x16; 0x67; 0x38; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,56))) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x7d; 0x39; 0xe7; 0x01;
                           (* VEXTRACTI128 (%_% xmm7) (%_% ymm4) (Imm8 (word 1)) *)
  0xc5; 0xf9; 0xd6; 0xbf; 0xb8; 0x00; 0x00; 0x00;
                           (* VMOVQ (Memop Quadword (%% (rdi,184))) (%_% xmm7) *)
  0xc4; 0xe3; 0xf9; 0x16; 0x7f; 0x70; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,112))) (%_% xmm7) (Imm8 (word 1)) *)
  0xc5; 0xf9; 0xd6; 0xaf; 0xa8; 0x00; 0x00; 0x00;
                           (* VMOVQ (Memop Quadword (%% (rdi,168))) (%_% xmm5) *)
  0xc4; 0xe3; 0xf9; 0x16; 0xaf; 0x88; 0x00; 0x00; 0x00; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,136))) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x7d; 0x39; 0xef; 0x01;
                           (* VEXTRACTI128 (%_% xmm7) (%_% ymm5) (Imm8 (word 1)) *)
  0xc5; 0xf9; 0xd6; 0x7f; 0x68;
                           (* VMOVQ (Memop Quadword (%% (rdi,104))) (%_% xmm7) *)
  0xc4; 0xe3; 0xf9; 0x16; 0x7f; 0x48; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,72))) (%_% xmm7) (Imm8 (word 1)) *)
  0xc5; 0xf9; 0xd6; 0x77; 0x28;
                           (* VMOVQ (Memop Quadword (%% (rdi,40))) (%_% xmm6) *)
  0xc4; 0xe3; 0xf9; 0x16; 0x77; 0x50; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,80))) (%_% xmm6) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x7d; 0x39; 0xf7; 0x01;
                           (* VEXTRACTI128 (%_% xmm7) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xf9; 0xd6; 0x7f; 0x78;
                           (* VMOVQ (Memop Quadword (%% (rdi,120))) (%_% xmm7) *)
  0xc4; 0xe3; 0xf9; 0x16; 0xbf; 0xa0; 0x00; 0x00; 0x00; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,160))) (%_% xmm7) (Imm8 (word 1)) *)
  0xc5; 0xf8; 0x77;        (* VZEROUPPER *)
  0xc3                     (* RET *)
]]);;

let sha3_keccak_f1600_alt2_tmc =
  define_trimmed "sha3_keccak_f1600_alt2_tmc" sha3_keccak_f1600_alt2_mc;;

let SHA3_KECCAK_F1600_ALT2_TMC_EXEC =
  X86_MK_EXEC_RULE sha3_keccak_f1600_alt2_tmc;;

(* ------------------------------------------------------------------------- *)
(* The layout of the state in the registers, as in the comment of the code:  *)
(* A[0][0] in all four quadwords of ymm0, the lanes (t, m t) of the line m   *)
(* in ymm1 + m (m = 0-4) and the lanes (0, t) in ymm6, for t = 1-4 from the  *)
(* low quadword up (the lanes are EL (5 * y + x) l for A[y][x]).             *)
(* ------------------------------------------------------------------------- *)

let keccak_alt2_regs = define
 `keccak_alt2_regs (l:int64 list) =
   [word_join (word_join (EL 0 l) (EL 0 l):int128)
              (word_join (EL 0 l) (EL 0 l):int128):int256;
    word_join (word_join (EL 4 l) (EL 3 l):int128)
              (word_join (EL 2 l) (EL 1 l):int128);
    word_join (word_join (EL 24 l) (EL 18 l):int128)
              (word_join (EL 12 l) (EL 6 l):int128);
    word_join (word_join (EL 19 l) (EL 8 l):int128)
              (word_join (EL 22 l) (EL 11 l):int128);
    word_join (word_join (EL 14 l) (EL 23 l):int128)
              (word_join (EL 7 l) (EL 16 l):int128);
    word_join (word_join (EL 9 l) (EL 13 l):int128)
              (word_join (EL 17 l) (EL 21 l):int128);
    word_join (word_join (EL 20 l) (EL 15 l):int128)
              (word_join (EL 10 l) (EL 5 l):int128)]`;;

(* ------------------------------------------------------------------------- *)
(* The rotation table.                                                       *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK_F1600_ALT2_DATA = prove
 (`bytes_loaded s (word tab) sha3_keccak_f1600_alt2_data <=>
   read (memory :> bytes(word tab,384)) s =
   num_of_bytelist sha3_keccak_f1600_alt2_data`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES;
    CONV_RULE (RAND_CONV LENGTH_CONV)
     (AP_TERM `LENGTH:byte list->num` sha3_keccak_f1600_alt2_data)]);;

let SHA3_KECCAK_F1600_ALT2_DATA_NUM =
  (REWRITE_CONV[sha3_keccak_f1600_alt2_data; num_of_bytelist] THENC
   WORD_REDUCE_CONV THENC NUM_REDUCE_CONV)
  `num_of_bytelist sha3_keccak_f1600_alt2_data`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK_F1600_ALT2_CORRECT = prove
 (`!a rc A pc tab.
      riprel32_within_bounds tab (pc + 7) /\
      nonoverlapping (a,200) (word pc,0x3e6) /\
      nonoverlapping (a,200) (word tab,384) /\
      nonoverlapping (a,200) (rc,192)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (sha3_keccak_f1600_alt2_tmc pc tab) /\
                read RIP s = word pc /\
                bytes_loaded s (word tab) sha3_keccak_f1600_alt2_data /\
                C_ARGUMENTS [a; rc] s /\
                wordlist_from_memory(rc,24) s = round_constants /\
                wordlist_from_memory(a,25) s = A)
           (\s. read RIP s = word(pc + 0x3e5) /\
                wordlist_from_memory(a,25) s = keccak 24 A)
           (MAYCHANGE [RIP; RAX; RCX; RSI] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                       ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14;
                       ZMM15] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(a,200)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `rc:int64`; `A:int64 list`; `pc:num`; `tab:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SHA3_KECCAK_F1600_ALT2_DATA;
              SHA3_KECCAK_F1600_ALT2_DATA_NUM] THEN
  ASM_CASES_TAC `LENGTH(A:int64 list) = 25` THENL
   [ALL_TAC;
    ENSURES_INIT_TAC "s0" THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:int64 list->num`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]] THEN

  (*** The invariant: the state after i rounds in the registers ***)

  ENSURES_WHILE_PUP_TAC `24` `pc + 0xdc` `pc + 0x322`
   `\i s. (read RDI s = a /\
           read RSI s = word_add rc (word(8 * i)) /\
           read RAX s = word tab /\
           read RCX s = word(24 - i) /\
           read (memory :> bytes (word tab,384)) s =
           num_of_bytelist sha3_keccak_f1600_alt2_data /\
           wordlist_from_memory(rc,24) s = round_constants /\
           [read YMM0 s; read YMM1 s; read YMM2 s; read YMM3 s;
            read YMM4 s; read YMM5 s; read YMM6 s] =
           keccak_alt2_regs (keccak i A)) /\
          (read ZF s <=> i = 24)` THEN
  REWRITE_TAC[SHA3_KECCAK_F1600_ALT2_DATA_NUM] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    (*** The initialization: the gathering of the state ***)

    REWRITE_TAC[round_constants;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(a,25) s:int64 list`] THEN
    MP_TAC(ISPEC `A:int64 list` LENGTH_EQ_25) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [th]) THEN
    REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC; keccak] THEN
    ENSURES_INIT_TAC "s0" THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 2
      `read (memory :> bytes256(word_add a (word 8))) s0`) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MAP_EVERY (fun n -> X86_STEPS_TAC SHA3_KECCAK_F1600_ALT2_TMC_EXEC [n] THEN
                        KECCAK_AVX2_SIMPLIFY_TAC) (1--31) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[keccak_alt2_regs; CONS_11] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    IMP_REWRITE_TAC[RIP_REL_ADDR_FOLD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[WORD_ADD] THEN
    REPEAT CONJ_TAC THEN BITBLAST_TAC;

    (*** A round: the lanes x<k> of the state, the round constant and the
     *** rows of the tables, the simulation with the lanes abbreviated,
     *** then each lane of the new state
     ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC; keccak] THEN
    MP_TAC(ISPECL [`A:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[keccak_alt2_regs; keccak_round] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[CONS_11] THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[round_constants; CONS_11] o
      CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV) o
      check (can (term_match [] `wordlist_from_memory(rc,24) s = l`) o
             concl)) THEN
    SUBGOAL_THEN
     `read (memory :> bytes64(word_add rc (word(8 * i)))) s0 =
      EL i round_constants`
    ASSUME_TAC THENL
     [UNDISCH_TAC `i < 24` THEN SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[round_constants; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    KECCAK_AVX2_TABLE_TAC THEN
    MAP_EVERY (fun k ->
      ABBREV_TAC(mk_eq(mk_var("x"^string_of_int k,`:int64`),
        vsubst [mk_small_numeral k,`k:num`] `EL k (keccak i A):int64`)))
     (0--24) THEN
    (fun gl -> keccak_avx2_lanes := 0; ALL_TAC gl) THEN
    MAP_EVERY (fun n -> X86_STEPS_TAC SHA3_KECCAK_F1600_ALT2_TMC_EXEC [n] THEN
                        KECCAK_AVX2_SIMPLIFY_TAC THEN
                        KECCAK_AVX2_LANE_ABBREV_TAC n) (1--106) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[round_constants; CONS_11;
      WORDLIST_FROM_MEMORY_CONV
       `wordlist_from_memory(rc,24) s106:int64 list`] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
    ASM_SIMP_TAC[KECCAK_AVX2_COUNTER] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    REWRITE_TAC[KECCAK_AVX2_JOIN_EQ; GSYM CONJ_ASSOC] THEN
    KECCAK_AVX2_EXPAND_TAC THEN
    REPEAT CONJ_TAC THEN KECCAK_BITBLAST_TAC;

    (*** The backward branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[keccak_alt2_regs; round_constants; CONS_11;
      WORDLIST_FROM_MEMORY_CONV
       `wordlist_from_memory(rc,24) s:int64 list`] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC SHA3_KECCAK_F1600_ALT2_TMC_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The scattering of the state ***)

    REWRITE_TAC[keccak_alt2_regs; round_constants; CONS_11;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(a,25) s:int64 list`] THEN
    MP_TAC(ISPECL [`A:int64 list`; `24`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[CONS_11] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC SHA3_KECCAK_F1600_ALT2_TMC_EXEC (1--29) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN BITBLAST_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the IBT landing pad.               *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK_F1600_ALT2_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a rc A pc tab stackpointer returnaddress.
      riprel32_within_bounds tab (pc + 7) /\
      nonoverlapping (a,200) (word pc,0x3e6) /\
      nonoverlapping (a,200) (word tab,384) /\
      nonoverlapping (a,200) (rc,192) /\
      nonoverlapping (a,200) (stackpointer,8)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (sha3_keccak_f1600_alt2_tmc pc tab) /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                bytes_loaded s (word tab) sha3_keccak_f1600_alt2_data /\
                C_ARGUMENTS [a; rc] s /\
                wordlist_from_memory(rc,24) s = round_constants /\
                wordlist_from_memory(a,25) s = A)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                wordlist_from_memory(a,25) s = keccak 24 A)
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(a,200)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  REWRITE_TAC[SHA3_KECCAK_F1600_ALT2_DATA] THEN CONV_TAC TWEAK_CONV THEN
  X86_ADD_RETURN_NOSTACK_TAC SHA3_KECCAK_F1600_ALT2_TMC_EXEC
   (CONV_RULE TWEAK_CONV
     (REWRITE_RULE[SHA3_KECCAK_F1600_ALT2_DATA]
       SHA3_KECCAK_F1600_ALT2_CORRECT)));;

(*** The code with the landing pad is the trimmed code after it, whose
 *** reference to the table is relative to pc + 4
 ***)

let SHA3_KECCAK_F1600_ALT2_MC_BRIDGE = prove
 (`!pc tab.
        sha3_keccak_f1600_alt2_mc pc tab =
        APPEND [word 0xf3:byte; word 0x0f; word 0x1e; word 0xfa]
               (sha3_keccak_f1600_alt2_tmc (pc + 4) tab)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sha3_keccak_f1600_alt2_mc; sha3_keccak_f1600_alt2_tmc;
              APPEND] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  REWRITE_TAC[INT_ARITH `&pc + &11:int = (&pc + &4) + &7`]);;

let SHA3_KECCAK_F1600_ALT2_SUBROUTINE_CORRECT = prove
 (`!a rc A pc tab stackpointer returnaddress.
      riprel32_within_bounds tab (pc + 11) /\
      nonoverlapping (a,200) (word pc,0x3ea) /\
      nonoverlapping (a,200) (word tab,384) /\
      nonoverlapping (a,200) (rc,192) /\
      nonoverlapping (a,200) (stackpointer,8)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (sha3_keccak_f1600_alt2_mc pc tab) /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                bytes_loaded s (word tab) sha3_keccak_f1600_alt2_data /\
                C_ARGUMENTS [a; rc] s /\
                wordlist_from_memory(rc,24) s = round_constants /\
                wordlist_from_memory(a,25) s = A)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                wordlist_from_memory(a,25) s = keccak 24 A)
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(a,200)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   ~bridge:(Some SHA3_KECCAK_F1600_ALT2_MC_BRIDGE)
   (CONV_RULE TWEAK_CONV SHA3_KECCAK_F1600_ALT2_NOIBT_SUBROUTINE_CORRECT)));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(*** Not yet in the library, so not in subroutine_signatures, but its
 *** signature is that of sha3_keccak_f1600_alt
 ***)

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word tab:int64`,`384`]
    ~keep_maychanges:true
    (assoc "sha3_keccak_f1600_alt" subroutine_signatures)
    SHA3_KECCAK_F1600_ALT2_CORRECT
    SHA3_KECCAK_F1600_ALT2_TMC_EXEC;;

(*** The events are those of the gathering, of each of the 24 rounds and of
 *** the scattering
 ***)

let SHA3_KECCAK_F1600_ALT2_SAFE = time prove
 (`exists f_events.
    forall e a rc pc tab.
        riprel32_within_bounds tab (pc + 7) /\
        nonoverlapping (a,200) (word pc,998) /\
        nonoverlapping (a,200) (word tab,384) /\
        nonoverlapping (a,200) (rc,192)
        ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   (sha3_keccak_f1600_alt2_tmc pc tab) /\
                 read RIP s = word pc /\
                 bytes_loaded s (word tab) sha3_keccak_f1600_alt2_data /\
                 C_ARGUMENTS [a; rc] s /\
                 read events s = e)
            (\s. read RIP s = word (pc + 997) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a tab pc /\
                      memaccess_inbounds e2 [a,200; rc,192; word tab,384]
                      [a,200]))
            (MAYCHANGE [RIP; RAX; RCX; RSI] ,,
             MAYCHANGE
             [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9;
              ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes (a,200)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rc:int64) (a:int64) (tab:num) (pc:num).
      APPEND (f_ev_epil rc a tab pc)
             (APPEND (ENUMERATEL 24 (\i. f_ev_loop rc a tab pc i))
                     (f_ev_prol rc a tab pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `rc:int64`; `pc:num`; `tab:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `24` `pc + 0xdc` `pc + 0x328`
   `\i s. read RDI s = a /\
          read RSI s = word_add rc (word(8 * i)) /\
          read RAX s = word tab /\
          read RCX s = word(24 - i)` THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false SHA3_KECCAK_F1600_ALT2_TMC_EXEC (1--31) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    REPEAT(CONJ_TAC THENL [KECCAK_AVX2_FOLD_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false SHA3_KECCAK_F1600_ALT2_TMC_EXEC (1--107) THEN
    ASM_SIMP_TAC[KECCAK_AVX2_COUNTER; KECCAK_AVX2_BRANCH] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false SHA3_KECCAK_F1600_ALT2_TMC_EXEC (1--28) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let SHA3_KECCAK_F1600_ALT2_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e a rc pc tab stackpointer returnaddress.
        riprel32_within_bounds tab (pc + 7) /\
        nonoverlapping (a,200) (word pc,998) /\
        nonoverlapping (a,200) (word tab,384) /\
        nonoverlapping (a,200) (rc,192) /\
        nonoverlapping (a,200) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   (sha3_keccak_f1600_alt2_tmc pc tab) /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 bytes_loaded s (word tab) sha3_keccak_f1600_alt2_data /\
                 C_ARGUMENTS [a; rc] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a tab pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192; word tab,384; stackpointer,8]
                      [a,200; stackpointer,8]))
            (\s s'. true)`,
  REWRITE_TAC[SHA3_KECCAK_F1600_ALT2_DATA] THEN
  X86_ADD_RETURN_NOSTACK_TAC SHA3_KECCAK_F1600_ALT2_TMC_EXEC
   (REWRITE_RULE[SHA3_KECCAK_F1600_ALT2_DATA] SHA3_KECCAK_F1600_ALT2_SAFE) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let SHA3_KECCAK_F1600_ALT2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e a rc pc tab stackpointer returnaddress.
        riprel32_within_bounds tab (pc + 11) /\
        nonoverlapping (a,200) (word pc,1002) /\
        nonoverlapping (a,200) (word tab,384) /\
        nonoverlapping (a,200) (rc,192) /\
        nonoverlapping (a,200) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) (sha3_keccak_f1600_alt2_mc pc tab) /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 bytes_loaded s (word tab) sha3_keccak_f1600_alt2_data /\
                 C_ARGUMENTS [a; rc] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a tab pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192; word tab,384; stackpointer,8]
                      [a,200; stackpointer,8]))
            (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   ~bridge:(Some SHA3_KECCAK_F1600_ALT2_MC_BRIDGE)
   SHA3_KECCAK_F1600_ALT2_NOIBT_SUBROUTINE_SAFE));;
