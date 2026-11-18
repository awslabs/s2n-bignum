(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Check that bytes encode polynomials with reduced coefficients.            *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "x86/proofs/utils/mlkem_bytes.ml";;
needs "x86/proofs/utils/mlkem_lanes.ml";;

(**** print_literal_from_elf "x86/mlkem/mlkem_check_encoding.o";;
 ****)

let mlkem_check_encoding_mc = define_assert_from_elf
  "mlkem_check_encoding_mc" "x86/mlkem/mlkem_check_encoding.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x00; 0x0d; 0x00; 0x0d;
                           (* MOV (% eax) (Imm32 (word 218107136)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0xff; 0x0f; 0xff; 0x0f;
                           (* MOV (% eax) (Imm32 (word 268374015)) *)
  0xc5; 0xf9; 0x6e; 0xe8;  (* VMOVD (%_% xmm5) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xed;
                           (* VPBROADCASTD (%_% ymm5) (%_% xmm5) *)
  0x48; 0xb8; 0x00; 0x01; 0x01; 0x02; 0x03; 0x04; 0x04; 0x05;
                           (* MOV (% rax) (Imm64 (word 361418281061515520)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xf0;
                           (* VMOVQ (%_% xmm6) (% rax) *)
  0x48; 0xb8; 0x06; 0x07; 0x07; 0x08; 0x09; 0x0a; 0x0a; 0x0b;
                           (* MOV (% rax) (Imm64 (word 795459318089975558)) *)
  0xc4; 0xe3; 0xc9; 0x22; 0xf0; 0x01;
                           (* VPINSRQ (%_% xmm6) (%_% xmm6) (% rax) (Imm8 (word 1)) *)
  0x48; 0xb8; 0x04; 0x05; 0x05; 0x06; 0x07; 0x08; 0x08; 0x09;
                           (* MOV (% rax) (Imm64 (word 650778972413822212)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xf8;
                           (* VMOVQ (%_% xmm7) (% rax) *)
  0x48; 0xb8; 0x0a; 0x0b; 0x0b; 0x0c; 0x0d; 0x0e; 0x0e; 0x0f;
                           (* MOV (% rax) (Imm64 (word 1084820009442282250)) *)
  0xc4; 0xe3; 0xc1; 0x22; 0xf8; 0x01;
                           (* VPINSRQ (%_% xmm7) (%_% xmm7) (% rax) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xc5; 0xd9; 0xef; 0xe4;  (* VPXOR (%_% xmm4) (%_% xmm4) (%_% xmm4) *)
  0x48; 0x85; 0xf6;        (* TEST (% rsi) (% rsi) *)
  0x0f; 0x84; 0xce; 0x02; 0x00; 0x00;
                           (* JE (Imm32 (word 718)) *)
  0xc5; 0xfa; 0x6f; 0x0f;  (* VMOVDQU (%_% xmm1) (Memop Word128 (%% (rdi,0))) *)
  0xc4; 0xe3; 0x75; 0x38; 0x4f; 0x08; 0x01;
                           (* VINSERTI128 (%_% ymm1) (%_% ymm1) (Memop Word128 (%% (rdi,8)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x75; 0x00; 0xce;
                           (* VPSHUFB (%_% ymm1) (%_% ymm1) (%_% ymm6) *)
  0xc5; 0xed; 0x71; 0xd1; 0x04;
                           (* VPSRLW (%_% ymm2) (%_% ymm1) (Imm8 (word 4)) *)
  0xc5; 0xf5; 0xdb; 0xcd;  (* VPAND (%_% ymm1) (%_% ymm1) (%_% ymm5) *)
  0xc4; 0xe3; 0x75; 0x0e; 0xca; 0xaa;
                           (* VPBLENDW (%_% ymm1) (%_% ymm1) (%_% ymm2) (Imm8 (word 170)) *)
  0xc5; 0xf5; 0x65; 0xc8;  (* VPCMPGTW (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xfa; 0x6f; 0x5f; 0x18;
                           (* VMOVDQU (%_% xmm3) (Memop Word128 (%% (rdi,24))) *)
  0xc4; 0xe3; 0x65; 0x38; 0x5f; 0x20; 0x01;
                           (* VINSERTI128 (%_% ymm3) (%_% ymm3) (Memop Word128 (%% (rdi,32)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x65; 0x00; 0xde;
                           (* VPSHUFB (%_% ymm3) (%_% ymm3) (%_% ymm6) *)
  0xc5; 0xc5; 0x71; 0xd3; 0x04;
                           (* VPSRLW (%_% ymm7) (%_% ymm3) (Imm8 (word 4)) *)
  0xc5; 0xe5; 0xdb; 0xdd;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xe3; 0x65; 0x0e; 0xdf; 0xaa;
                           (* VPBLENDW (%_% ymm3) (%_% ymm3) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x65; 0xd8;  (* VPCMPGTW (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe3;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xfa; 0x6f; 0x4f; 0x30;
                           (* VMOVDQU (%_% xmm1) (Memop Word128 (%% (rdi,48))) *)
  0xc4; 0xe3; 0x75; 0x38; 0x4f; 0x38; 0x01;
                           (* VINSERTI128 (%_% ymm1) (%_% ymm1) (Memop Word128 (%% (rdi,56)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x75; 0x00; 0xce;
                           (* VPSHUFB (%_% ymm1) (%_% ymm1) (%_% ymm6) *)
  0xc5; 0xed; 0x71; 0xd1; 0x04;
                           (* VPSRLW (%_% ymm2) (%_% ymm1) (Imm8 (word 4)) *)
  0xc5; 0xf5; 0xdb; 0xcd;  (* VPAND (%_% ymm1) (%_% ymm1) (%_% ymm5) *)
  0xc4; 0xe3; 0x75; 0x0e; 0xca; 0xaa;
                           (* VPBLENDW (%_% ymm1) (%_% ymm1) (%_% ymm2) (Imm8 (word 170)) *)
  0xc5; 0xf5; 0x65; 0xc8;  (* VPCMPGTW (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xfa; 0x6f; 0x5f; 0x48;
                           (* VMOVDQU (%_% xmm3) (Memop Word128 (%% (rdi,72))) *)
  0xc4; 0xe3; 0x65; 0x38; 0x5f; 0x50; 0x01;
                           (* VINSERTI128 (%_% ymm3) (%_% ymm3) (Memop Word128 (%% (rdi,80)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x65; 0x00; 0xde;
                           (* VPSHUFB (%_% ymm3) (%_% ymm3) (%_% ymm6) *)
  0xc5; 0xc5; 0x71; 0xd3; 0x04;
                           (* VPSRLW (%_% ymm7) (%_% ymm3) (Imm8 (word 4)) *)
  0xc5; 0xe5; 0xdb; 0xdd;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xe3; 0x65; 0x0e; 0xdf; 0xaa;
                           (* VPBLENDW (%_% ymm3) (%_% ymm3) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x65; 0xd8;  (* VPCMPGTW (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe3;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xfa; 0x6f; 0x4f; 0x60;
                           (* VMOVDQU (%_% xmm1) (Memop Word128 (%% (rdi,96))) *)
  0xc4; 0xe3; 0x75; 0x38; 0x4f; 0x68; 0x01;
                           (* VINSERTI128 (%_% ymm1) (%_% ymm1) (Memop Word128 (%% (rdi,104)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x75; 0x00; 0xce;
                           (* VPSHUFB (%_% ymm1) (%_% ymm1) (%_% ymm6) *)
  0xc5; 0xed; 0x71; 0xd1; 0x04;
                           (* VPSRLW (%_% ymm2) (%_% ymm1) (Imm8 (word 4)) *)
  0xc5; 0xf5; 0xdb; 0xcd;  (* VPAND (%_% ymm1) (%_% ymm1) (%_% ymm5) *)
  0xc4; 0xe3; 0x75; 0x0e; 0xca; 0xaa;
                           (* VPBLENDW (%_% ymm1) (%_% ymm1) (%_% ymm2) (Imm8 (word 170)) *)
  0xc5; 0xf5; 0x65; 0xc8;  (* VPCMPGTW (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xfa; 0x6f; 0x5f; 0x78;
                           (* VMOVDQU (%_% xmm3) (Memop Word128 (%% (rdi,120))) *)
  0xc4; 0xe3; 0x65; 0x38; 0x9f; 0x80; 0x00; 0x00; 0x00; 0x01;
                           (* VINSERTI128 (%_% ymm3) (%_% ymm3) (Memop Word128 (%% (rdi,128)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x65; 0x00; 0xde;
                           (* VPSHUFB (%_% ymm3) (%_% ymm3) (%_% ymm6) *)
  0xc5; 0xc5; 0x71; 0xd3; 0x04;
                           (* VPSRLW (%_% ymm7) (%_% ymm3) (Imm8 (word 4)) *)
  0xc5; 0xe5; 0xdb; 0xdd;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xe3; 0x65; 0x0e; 0xdf; 0xaa;
                           (* VPBLENDW (%_% ymm3) (%_% ymm3) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x65; 0xd8;  (* VPCMPGTW (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe3;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xfa; 0x6f; 0x8f; 0x90; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm1) (Memop Word128 (%% (rdi,144))) *)
  0xc4; 0xe3; 0x75; 0x38; 0x8f; 0x98; 0x00; 0x00; 0x00; 0x01;
                           (* VINSERTI128 (%_% ymm1) (%_% ymm1) (Memop Word128 (%% (rdi,152)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x75; 0x00; 0xce;
                           (* VPSHUFB (%_% ymm1) (%_% ymm1) (%_% ymm6) *)
  0xc5; 0xed; 0x71; 0xd1; 0x04;
                           (* VPSRLW (%_% ymm2) (%_% ymm1) (Imm8 (word 4)) *)
  0xc5; 0xf5; 0xdb; 0xcd;  (* VPAND (%_% ymm1) (%_% ymm1) (%_% ymm5) *)
  0xc4; 0xe3; 0x75; 0x0e; 0xca; 0xaa;
                           (* VPBLENDW (%_% ymm1) (%_% ymm1) (%_% ymm2) (Imm8 (word 170)) *)
  0xc5; 0xf5; 0x65; 0xc8;  (* VPCMPGTW (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xfa; 0x6f; 0x9f; 0xa8; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm3) (Memop Word128 (%% (rdi,168))) *)
  0xc4; 0xe3; 0x65; 0x38; 0x9f; 0xb0; 0x00; 0x00; 0x00; 0x01;
                           (* VINSERTI128 (%_% ymm3) (%_% ymm3) (Memop Word128 (%% (rdi,176)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x65; 0x00; 0xde;
                           (* VPSHUFB (%_% ymm3) (%_% ymm3) (%_% ymm6) *)
  0xc5; 0xc5; 0x71; 0xd3; 0x04;
                           (* VPSRLW (%_% ymm7) (%_% ymm3) (Imm8 (word 4)) *)
  0xc5; 0xe5; 0xdb; 0xdd;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xe3; 0x65; 0x0e; 0xdf; 0xaa;
                           (* VPBLENDW (%_% ymm3) (%_% ymm3) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x65; 0xd8;  (* VPCMPGTW (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe3;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xfa; 0x6f; 0x8f; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm1) (Memop Word128 (%% (rdi,192))) *)
  0xc4; 0xe3; 0x75; 0x38; 0x8f; 0xc8; 0x00; 0x00; 0x00; 0x01;
                           (* VINSERTI128 (%_% ymm1) (%_% ymm1) (Memop Word128 (%% (rdi,200)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x75; 0x00; 0xce;
                           (* VPSHUFB (%_% ymm1) (%_% ymm1) (%_% ymm6) *)
  0xc5; 0xed; 0x71; 0xd1; 0x04;
                           (* VPSRLW (%_% ymm2) (%_% ymm1) (Imm8 (word 4)) *)
  0xc5; 0xf5; 0xdb; 0xcd;  (* VPAND (%_% ymm1) (%_% ymm1) (%_% ymm5) *)
  0xc4; 0xe3; 0x75; 0x0e; 0xca; 0xaa;
                           (* VPBLENDW (%_% ymm1) (%_% ymm1) (%_% ymm2) (Imm8 (word 170)) *)
  0xc5; 0xf5; 0x65; 0xc8;  (* VPCMPGTW (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xfa; 0x6f; 0x9f; 0xd8; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm3) (Memop Word128 (%% (rdi,216))) *)
  0xc4; 0xe3; 0x65; 0x38; 0x9f; 0xe0; 0x00; 0x00; 0x00; 0x01;
                           (* VINSERTI128 (%_% ymm3) (%_% ymm3) (Memop Word128 (%% (rdi,224)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x65; 0x00; 0xde;
                           (* VPSHUFB (%_% ymm3) (%_% ymm3) (%_% ymm6) *)
  0xc5; 0xc5; 0x71; 0xd3; 0x04;
                           (* VPSRLW (%_% ymm7) (%_% ymm3) (Imm8 (word 4)) *)
  0xc5; 0xe5; 0xdb; 0xdd;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xe3; 0x65; 0x0e; 0xdf; 0xaa;
                           (* VPBLENDW (%_% ymm3) (%_% ymm3) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x65; 0xd8;  (* VPCMPGTW (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe3;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xfa; 0x6f; 0x8f; 0xf0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm1) (Memop Word128 (%% (rdi,240))) *)
  0xc4; 0xe3; 0x75; 0x38; 0x8f; 0xf8; 0x00; 0x00; 0x00; 0x01;
                           (* VINSERTI128 (%_% ymm1) (%_% ymm1) (Memop Word128 (%% (rdi,248)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x75; 0x00; 0xce;
                           (* VPSHUFB (%_% ymm1) (%_% ymm1) (%_% ymm6) *)
  0xc5; 0xed; 0x71; 0xd1; 0x04;
                           (* VPSRLW (%_% ymm2) (%_% ymm1) (Imm8 (word 4)) *)
  0xc5; 0xf5; 0xdb; 0xcd;  (* VPAND (%_% ymm1) (%_% ymm1) (%_% ymm5) *)
  0xc4; 0xe3; 0x75; 0x0e; 0xca; 0xaa;
                           (* VPBLENDW (%_% ymm1) (%_% ymm1) (%_% ymm2) (Imm8 (word 170)) *)
  0xc5; 0xf5; 0x65; 0xc8;  (* VPCMPGTW (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xfa; 0x6f; 0x9f; 0x08; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm3) (Memop Word128 (%% (rdi,264))) *)
  0xc4; 0xe3; 0x65; 0x38; 0x9f; 0x10; 0x01; 0x00; 0x00; 0x01;
                           (* VINSERTI128 (%_% ymm3) (%_% ymm3) (Memop Word128 (%% (rdi,272)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x65; 0x00; 0xde;
                           (* VPSHUFB (%_% ymm3) (%_% ymm3) (%_% ymm6) *)
  0xc5; 0xc5; 0x71; 0xd3; 0x04;
                           (* VPSRLW (%_% ymm7) (%_% ymm3) (Imm8 (word 4)) *)
  0xc5; 0xe5; 0xdb; 0xdd;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xe3; 0x65; 0x0e; 0xdf; 0xaa;
                           (* VPBLENDW (%_% ymm3) (%_% ymm3) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x65; 0xd8;  (* VPCMPGTW (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe3;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xfa; 0x6f; 0x8f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm1) (Memop Word128 (%% (rdi,288))) *)
  0xc4; 0xe3; 0x75; 0x38; 0x8f; 0x28; 0x01; 0x00; 0x00; 0x01;
                           (* VINSERTI128 (%_% ymm1) (%_% ymm1) (Memop Word128 (%% (rdi,296)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x75; 0x00; 0xce;
                           (* VPSHUFB (%_% ymm1) (%_% ymm1) (%_% ymm6) *)
  0xc5; 0xed; 0x71; 0xd1; 0x04;
                           (* VPSRLW (%_% ymm2) (%_% ymm1) (Imm8 (word 4)) *)
  0xc5; 0xf5; 0xdb; 0xcd;  (* VPAND (%_% ymm1) (%_% ymm1) (%_% ymm5) *)
  0xc4; 0xe3; 0x75; 0x0e; 0xca; 0xaa;
                           (* VPBLENDW (%_% ymm1) (%_% ymm1) (%_% ymm2) (Imm8 (word 170)) *)
  0xc5; 0xf5; 0x65; 0xc8;  (* VPCMPGTW (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xfa; 0x6f; 0x9f; 0x38; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm3) (Memop Word128 (%% (rdi,312))) *)
  0xc4; 0xe3; 0x65; 0x38; 0x9f; 0x40; 0x01; 0x00; 0x00; 0x01;
                           (* VINSERTI128 (%_% ymm3) (%_% ymm3) (Memop Word128 (%% (rdi,320)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x65; 0x00; 0xde;
                           (* VPSHUFB (%_% ymm3) (%_% ymm3) (%_% ymm6) *)
  0xc5; 0xc5; 0x71; 0xd3; 0x04;
                           (* VPSRLW (%_% ymm7) (%_% ymm3) (Imm8 (word 4)) *)
  0xc5; 0xe5; 0xdb; 0xdd;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xe3; 0x65; 0x0e; 0xdf; 0xaa;
                           (* VPBLENDW (%_% ymm3) (%_% ymm3) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x65; 0xd8;  (* VPCMPGTW (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe3;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xfa; 0x6f; 0x8f; 0x50; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm1) (Memop Word128 (%% (rdi,336))) *)
  0xc4; 0xe3; 0x75; 0x38; 0x8f; 0x58; 0x01; 0x00; 0x00; 0x01;
                           (* VINSERTI128 (%_% ymm1) (%_% ymm1) (Memop Word128 (%% (rdi,344)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x75; 0x00; 0xce;
                           (* VPSHUFB (%_% ymm1) (%_% ymm1) (%_% ymm6) *)
  0xc5; 0xed; 0x71; 0xd1; 0x04;
                           (* VPSRLW (%_% ymm2) (%_% ymm1) (Imm8 (word 4)) *)
  0xc5; 0xf5; 0xdb; 0xcd;  (* VPAND (%_% ymm1) (%_% ymm1) (%_% ymm5) *)
  0xc4; 0xe3; 0x75; 0x0e; 0xca; 0xaa;
                           (* VPBLENDW (%_% ymm1) (%_% ymm1) (%_% ymm2) (Imm8 (word 170)) *)
  0xc5; 0xf5; 0x65; 0xc8;  (* VPCMPGTW (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xfa; 0x6f; 0x9f; 0x68; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm3) (Memop Word128 (%% (rdi,360))) *)
  0xc4; 0xe3; 0x65; 0x38; 0x9f; 0x70; 0x01; 0x00; 0x00; 0x01;
                           (* VINSERTI128 (%_% ymm3) (%_% ymm3) (Memop Word128 (%% (rdi,368)))
(Imm8 (word 1)) *)
  0xc4; 0xe2; 0x65; 0x00; 0xde;
                           (* VPSHUFB (%_% ymm3) (%_% ymm3) (%_% ymm6) *)
  0xc5; 0xc5; 0x71; 0xd3; 0x04;
                           (* VPSRLW (%_% ymm7) (%_% ymm3) (Imm8 (word 4)) *)
  0xc5; 0xe5; 0xdb; 0xdd;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xe3; 0x65; 0x0e; 0xdf; 0xaa;
                           (* VPBLENDW (%_% ymm3) (%_% ymm3) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x65; 0xd8;  (* VPCMPGTW (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0xdd; 0xeb; 0xe3;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0x48; 0x81; 0xc7; 0x80; 0x01; 0x00; 0x00;
                           (* ADD (% rdi) (Imm32 (word 384)) *)
  0x48; 0xff; 0xce;        (* DEC (% rsi) *)
  0x0f; 0x85; 0x32; 0xfd; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294966578)) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x17; 0xe4;
                           (* VPTEST (%_% ymm4) (%_% ymm4) *)
  0x0f; 0x94; 0xc0;        (* SETE (% al) *)
  0xc5; 0xf8; 0x77;        (* VZEROUPPER *)
  0xc3                     (* RET *)
];;

let mlkem_check_encoding_tmc =
  define_trimmed "mlkem_check_encoding_tmc" mlkem_check_encoding_mc;;

let MLKEM_CHECK_ENCODING_TMC_EXEC =
  X86_MK_CORE_EXEC_RULE mlkem_check_encoding_tmc;;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

(*** The 32 loads of one iteration, two of 16 bytes for each block of 24
 *** bytes, as subwords of the 384 bytes of the iteration
 ***)

let CHECK_ENCODING_LOADS = prove
 (`!a:int64 m n k s:x86state.
        read (memory :> bytes(a,m)) s = n /\ k + 384 <= m
        ==> !j. j < 16
                ==> read (memory :> bytes128(word_add a (word(k + 24 * j))))
                         s =
                    word_subword
                     (word((n DIV 2 EXP (8 * k)) MOD 2 EXP 3072):3072 word)
                     (192 * j,128) /\
                    read (memory :> bytes128
                           (word_add a (word(k + 24 * j + 8)))) s =
                    word_subword
                     (word((n DIV 2 EXP (8 * k)) MOD 2 EXP 3072):3072 word)
                     (192 * j + 64,128)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`a:int64`; `m:num`; `n:num`; `k + 24 * j`; `s:x86state`]
      READ_MEMORY_BYTES128_OF_NUM);
    MP_TAC(SPECL [`a:int64`; `m:num`; `n:num`; `k + 24 * j + 8`;
                  `s:x86state`] READ_MEMORY_BYTES128_OF_NUM)] THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
  ASM_SIMP_TAC[WORD_SUBWORD_WORD; DIMINDEX_CONV `dimindex(:3072)`;
               ARITH_RULE `j < 16 ==> 192 * j + 128 <= 3072`;
               ARITH_RULE `j < 16 ==> (192 * j + 64) + 128 <= 3072`] THEN
  AP_TERM_TAC THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW;
               ARITH_RULE `j < 16 ==> 192 * j + 128 <= 3072`;
               ARITH_RULE `j < 16 ==> (192 * j + 64) + 128 <= 3072`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ARITH_TAC);;

(*** Whether field i (of 12 bits) is out of range, i.e. at least 3329 ***)

let cenc_bad = new_definition
 `cenc_bad n i <=> 3329 <= (n DIV 2 EXP (12 * i)) MOD 2 EXP 12`;;

let CHECK_ENCODING_FIELD = prove
 (`!n i c.
        word((n DIV 2 EXP (8 * (384 * i))) MOD 2 EXP 3072) = c
        ==> !j. j < 256
                ==> (cenc_bad n (256 * i + j) <=>
                     word_uge (word_subword (c:3072 word) (12 * j,12):12 word)
                              (word 3329))`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[cenc_bad; WORD_UGE; GE] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_CONV `dimindex(:3072)`;
              DIMINDEX_CONV `dimindex(:12)`; MOD_MOD_REFL;
              ARITH_RULE `MIN 12 12 = 12`] THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW;
               ARITH_RULE `j < 256 ==> 12 * j + 12 <= 3072`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `8 * 384 * i + 12 * j = 12 * (256 * i + j)`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let EXISTS_LT_ADD1 = prove
 (`!P n. (?t. t < n + 1 /\ P t) <=> (?t. t < n /\ P t) \/ P n`,
  REWRITE_TAC[GSYM ADD1; LT] THEN MESON_TAC[]);;

let EXISTS_LT_ADD16 = prove
 (`!P i. (?t. t < 16 * (i + 1) /\ P t) <=>
         (?t. t < 16 * i /\ P t) \/
         P(16 * i) \/ P(16 * i + 1) \/ P(16 * i + 2) \/ P(16 * i + 3) \/
         P(16 * i + 4) \/ P(16 * i + 5) \/ P(16 * i + 6) \/ P(16 * i + 7) \/
         P(16 * i + 8) \/ P(16 * i + 9) \/ P(16 * i + 10) \/
         P(16 * i + 11) \/ P(16 * i + 12) \/ P(16 * i + 13) \/
         P(16 * i + 14) \/ P(16 * i + 15)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
  MAP_EVERY (fun k ->
    let lhs = if k = 1 then `16 * i + 1` else
              mk_binop `(+):num->num->num` `16 * i` (mk_small_numeral k)
    and prev = if k = 1 then `16 * i` else
               mk_binop `(+):num->num->num` `16 * i` (mk_small_numeral(k-1)) in
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [ARITH_RULE(mk_eq(lhs,mk_binop `(+):num->num->num` prev `1`))] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EXISTS_LT_ADD1])
   (rev(1--16)) THEN
  REWRITE_TAC[GSYM DISJ_ASSOC] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[]);;

let CHECK_ENCODING_ALL = prove
 (`!n k. (!i. i < 256 * k ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329) <=>
         (!j. j < 16 ==> ~(?t. t < 16 * k /\ cenc_bad n (16 * t + j)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cenc_bad; NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`;
              NOT_LE] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `i MOD 16`) THEN
    REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    DISCH_THEN(MP_TAC o SPEC `i DIV 16`) THEN
    REWRITE_TAC[ARITH_RULE `16 * i DIV 16 + i MOD 16 = i`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let CHECK_ENCODING_OR_MASK = prove
 (`!p q. word_or (if p then word 65535 else word 0)
                 (if q then word 65535 else word 0):int16 =
         if p \/ q then word 65535 else word 0`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `p:bool` THEN
  BOOL_CASES_TAC `q:bool` THEN REWRITE_TAC[] THEN
  CONV_TAC WORD_REDUCE_CONV);;

(*** The comparison vector of one block of 24 bytes, from its two loads
 *** x0 (bytes 0-15 of the block) and x1 (bytes 8-23): lane k is all 1s
 *** exactly when field k of the block is out of range
 ***)

let CHECK_ENCODING_CHUNK =
  (16,16,
   (fun xs k ->
      let x,p = if k < 8 then el 0 xs,12 * k
                else el 1 xs,32 + 12 * (k - 8) in
      vsubst [mk_wsubword x p 12,`f:12 word`]
        `if word_uge (f:12 word) (word 3329) then word 65535:int16
         else word 0`),
   LANE_BITBLAST_TAC[]);;

(*** The test of the accumulator at the end ***)

let CHECK_ENCODING_ZERO = prove
 (`!acc:int256.
        acc = word 0 <=>
        !j. j < 16 ==> word_subword acc (16 * j,16):int16 = word 0`,
  GEN_TAC THEN
  CONV_TAC(RAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
  BITBLAST_TAC);;

let CHECK_ENCODING_MASK_ZERO = prove
 (`!p. ((if p then word 65535 else word 0):int16) = word 0 <=> ~p`,
  GEN_TAC THEN BOOL_CASES_TAC `p:bool` THEN REWRITE_TAC[] THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_CHECK_ENCODING_CORRECT = prove
 (`!a k n pc.
        ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST mlkem_check_encoding_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [a; k] s /\
              read (memory :> bytes(a,384 * val k)) s = n)
         (\s. read RIP s = word(pc + 0x348) /\
              C_RETURN s =
              if !i. i < 256 * val k
                     ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
              then word 1 else word 0)
         (MAYCHANGE [RIP; RAX; RDI; RSI] ,,
          MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                     ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  X_GEN_TAC `a:int64` THEN W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN

  (*** The trivial case k = 0, when the loop is skipped ***)

  ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; LT] THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_CHECK_ENCODING_TMC_EXEC [n] THEN
                        SIMD_SIMPLIFY_TAC[]) (1--22) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  (*** The invariant: the constants (3328 and the mask 0x0fff in each
   *** 16-bit lane, and the shuffle of the bytes of the fields), and lane
   *** j of the accumulator YMM4 all 1s exactly when one of the fields
   *** j, 16 + j, ... seen so far is out of range
   ***)

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x6d` `pc + 0x335`
   `\i s. (read RDI s = word_add a (word(384 * i)) /\
           read RSI s = word(k - i) /\
           read YMM0 s =
           word_join (word 0x0d000d000d000d000d000d000d000d00:int128)
                     (word 0x0d000d000d000d000d000d000d000d00:int128) /\
           read YMM5 s =
           word_join (word 0x0fff0fff0fff0fff0fff0fff0fff0fff:int128)
                     (word 0x0fff0fff0fff0fff0fff0fff0fff0fff:int128) /\
           read YMM6 s =
           word_join (word 0x0f0e0e0d0c0b0b0a0908080706050504:int128)
                     (word 0x0b0a0a09080707060504040302010100:int128) /\
           read (memory :> bytes(a,384 * k)) s = n /\
           !j. j < 16
               ==> word_subword (read YMM4 s) (16 * j,16):int16 =
                   if ?t. t < 16 * i /\ cenc_bad n (16 * t + j)
                   then word 65535 else word 0) /\
          (read ZF s <=> i = k)` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN
  REPEAT CONJ_TAC THENL
   [(*** The initialization, with all lanes 0 ***)

    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_CHECK_ENCODING_TMC_EXEC [n] THEN
                        SIMD_SIMPLIFY_TAC[]) (1--18) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; LT; WORD_SUBWORD_0;
                EXISTS_SIMP];

    (*** The loop body, on the 384-byte chunk c of the input, whose 32
     *** loads (two for each block of 24 bytes) are abbreviated l0..l31
     ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ABBREV_TAC
     `c:3072 word = word((n DIV 2 EXP (8 * (384 * i))) MOD 2 EXP 3072)` THEN
    ENSURES_INIT_TAC "s0" THEN
    ABBREV_TAC `acc = read YMM4 s0` THEN
    MP_TAC(SPECL [`a:int64`; `384 * k`; `n:num`; `384 * i`; `s0:x86state`]
      CHECK_ENCODING_LOADS) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [UNDISCH_TAC `i < k` THEN ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    MAP_EVERY (fun m ->
      ABBREV_TAC(mk_eq(mk_var("l"^string_of_int m,`:int128`),
                       mk_wsubword `c:3072 word`
                         (192 * (m / 2) + 64 * (m mod 2)) 128)))
     (0--31) THEN
    STRIP_TAC THEN

    (*** Simulate, replacing each comparison vector by its lanes ***)

    MAP_EVERY (fun k ->
      X86_STEPS_TAC MLKEM_CHECK_ENCODING_TMC_EXEC [k] THEN
      SIMD_SIMPLIFY_TAC[] THEN
      (if k <= 128 && k mod 8 = 7 then
         let blk = k / 8 in
         CHUNK_ABSTRACT_TAC CHECK_ENCODING_CHUNK
           (if blk mod 2 = 0 then `YMM1` else `YMM3`)
           [mk_var("l"^string_of_int(2 * blk),`:int128`);
            mk_var("l"^string_of_int(2 * blk + 1),`:int128`)] k
       else ALL_TAC)) (1--130) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `word_sub (word (k - i)) (word 1):int64 = word(k - (i + 1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `k - (i + 1) = k - i - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < k ==> 1 <= k - i`];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `k - (i + 1) < 2 EXP 64`
       (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th])
      THENL [UNDISCH_TAC `k < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `i < k` THEN ARITH_TAC] THEN

    (*** Lane j is the old one or-ed with those of the 16 blocks, which
     *** compare the fields 16 * m + j of the chunk
     ***)

    MP_TAC(SPECL [`n:num`; `i:num`; `c:3072 word`] CHECK_ENCODING_FIELD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
    STRIP_TAC THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[WORD_SUBWORD_OR] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
      check (fun th -> free_in `acc:int256` (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[EXISTS_LT_ADD16] THEN
    REWRITE_TAC[ARITH_RULE `16 * (16 * i + m) + j = 256 * i + 16 * m + j`;
                ARITH_RULE `16 * (16 * i) + j = 256 * i + j`] THEN
    MAP_EVERY (fun m ->
      let v = mk_var("l"^string_of_int m,`:int128`) in
      FIRST_ASSUM(fun th ->
        let c = concl th in
        if is_eq c && rhs c = v && is_comb(lhs c) &&
           fst(strip_comb(lhs c)) = `word_subword:3072 word->num#num->int128`
        then SUBST1_TAC(SYM th) else NO_TAC)) (0--31) THEN
    UNDISCH_TAC `j < 16` THEN SPEC_TAC(`j:num`,`j:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[CHECK_ENCODING_OR_MASK; GSYM DISJ_ASSOC];

    (*** The backward branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ABBREV_TAC `acc = read YMM4 s0` THEN
    X86_STEPS_TAC MLKEM_CHECK_ENCODING_TMC_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The test of the accumulator ***)

    ENSURES_INIT_TAC "s0" THEN
    ABBREV_TAC `acc = read YMM4 s0` THEN
    MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_CHECK_ENCODING_TMC_EXEC [n] THEN
                        SIMD_SIMPLIFY_TAC[]) (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_EQ_0; CHECK_ENCODING_ALL; CHECK_ENCODING_ZERO] THEN
    ASM_SIMP_TAC[CHECK_ENCODING_MASK_ZERO] THEN
    COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the IBT landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a k n pc stackpointer returnaddress.
        ensures x86
         (\s. bytes_loaded s (word pc) mlkem_check_encoding_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [a; k] s /\
              read (memory :> bytes(a,384 * val k)) s = n)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s =
              if !i. i < 256 * val k
                     ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
              then word 1 else word 0)
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_check_encoding_tmc
    MLKEM_CHECK_ENCODING_CORRECT);;

let MLKEM_CHECK_ENCODING_SUBROUTINE_CORRECT = prove
 (`!a k n pc stackpointer returnaddress.
        ensures x86
         (\s. bytes_loaded s (word pc) mlkem_check_encoding_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [a; k] s /\
              read (memory :> bytes(a,384 * val k)) s = n)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s =
              if !i. i < 256 * val k
                     ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
              then word 1 else word 0)
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC
   (ADD_IBT_RULE MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_check_encoding" subroutine_signatures)
    MLKEM_CHECK_ENCODING_CORRECT
    MLKEM_CHECK_ENCODING_TMC_EXEC;;

(*** The loop runs k times, so the events are those of the setup, of each
 *** iteration and of the end, or when k = 0 just those of a setup that
 *** skips the loop
 ***)

let MLKEM_CHECK_ENCODING_SAFE = time prove
 (`exists f_events.
    forall e a k pc.
        ensures x86
        (\s. bytes_loaded s (word pc) (BUTLAST mlkem_check_encoding_tmc) /\
             read RIP s = word pc /\
             C_ARGUMENTS [a; k] s /\
             read events s = e)
        (\s. read RIP s = word (pc + 0x348) /\
             (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a k pc /\
                  memaccess_inbounds e2 [a,(384 * val k) * 1] []))
        (MAYCHANGE [RIP; RAX; RDI; RSI] ,,
         MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                    ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (k:int64) (pc:num).
      if val k = 0 then f_ev_zero a k pc
      else APPEND (f_ev_epil a k pc)
                  (APPEND (ENUMERATEL (val k) (\i. f_ev_loop a k pc i))
                          (f_ev_prol a k pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `a:int64` THEN W64_GEN_TAC `k:num` THEN X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; fst MLKEM_CHECK_ENCODING_TMC_EXEC] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_CHECK_ENCODING_TMC_EXEC (1--22) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x6d` `pc + 0x33b`
   `\i s. read RDI s = word_add a (word(384 * i)) /\
          read RSI s = word(k - i)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_CHECK_ENCODING_TMC_EXEC (1--18) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `word_sub (word (k - i)) (word 1):int64 = word(k - (i + 1)) /\
      val(word(k - (i + 1)):int64) = k - (i + 1)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `k - (i + 1) = k - i - 1`] THEN
        GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < k ==> 1 <= k - i`];
        REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `k < 2 EXP 64` THEN ARITH_TAC];
      ALL_TAC] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_CHECK_ENCODING_TMC_EXEC (1--131) THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_CHECK_ENCODING_TMC_EXEC (1--4) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e a k pc stackpointer returnaddress.
        ensures x86
        (\s. bytes_loaded s (word pc) mlkem_check_encoding_tmc /\
             read RIP s = word pc /\
             read RSP s = stackpointer /\
             read (memory :> bytes64 stackpointer) s = returnaddress /\
             C_ARGUMENTS [a; k] s /\
             read events s = e)
        (\s. read RIP s = returnaddress /\
             read RSP s = word_add stackpointer (word 8) /\
             (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a k pc stackpointer returnaddress /\
                  memaccess_inbounds e2
                    [a,(384 * val k) * 1; stackpointer,8]
                    [stackpointer,8]))
        (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_check_encoding_tmc
    MLKEM_CHECK_ENCODING_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_CHECK_ENCODING_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e a k pc stackpointer returnaddress.
        ensures x86
        (\s. bytes_loaded s (word pc) mlkem_check_encoding_mc /\
             read RIP s = word pc /\
             read RSP s = stackpointer /\
             read (memory :> bytes64 stackpointer) s = returnaddress /\
             C_ARGUMENTS [a; k] s /\
             read events s = e)
        (\s. read RIP s = returnaddress /\
             read RSP s = word_add stackpointer (word 8) /\
             (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a k pc stackpointer returnaddress /\
                  memaccess_inbounds e2
                    [a,(384 * val k) * 1; stackpointer,8]
                    [stackpointer,8]))
        (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_SAFE));;
