(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise multiplication of polynomials in NTT domain for ML-DSA.         *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(*** print_literal_from_elf "x86/mldsa/mldsa_pointwise.o";;
 ***)
let mldsa_pointwise_mc = define_assert_from_elf "mldsa_pointwise_mc" "x86/mldsa/mldsa_pointwise.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xc5; 0xfd; 0x6f; 0x01;  (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rcx,0))) *)
  0xc5; 0xfd; 0x6f; 0x49; 0x20;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rcx,32))) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc5; 0xfd; 0x6f; 0x16;  (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0xfd; 0x6f; 0x66; 0x20;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0xfd; 0x6f; 0x76; 0x40;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,64))) *)
  0xc5; 0x7d; 0x6f; 0x12;  (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0x7d; 0x6f; 0x62; 0x20;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rdx,32))) *)
  0xc5; 0x7d; 0x6f; 0x72; 0x40;
                           (* VMOVDQA (%_% ymm14) (Memop Word256 (%% (rdx,64))) *)
  0xc5; 0xe5; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm2) (Imm8 (word 32)) *)
  0xc5; 0xd5; 0x73; 0xd4; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm4) (Imm8 (word 32)) *)
  0xc5; 0xfe; 0x16; 0xfe;  (* VMOVSHDUP (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xc1; 0x25; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm11) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x15; 0x73; 0xd4; 0x20;
                           (* VPSRLQ (%_% ymm13) (%_% ymm12) (Imm8 (word 32)) *)
  0xc4; 0x41; 0x7e; 0x16; 0xfe;
                           (* VMOVSHDUP (%_% ymm15) (%_% ymm14) *)
  0xc4; 0xc2; 0x6d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm2) (%_% ymm10) *)
  0xc4; 0xc2; 0x65; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc2; 0x55; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xf6;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0xc2; 0x45; 0x28; 0xff;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm15) *)
  0xc4; 0x62; 0x7d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm0) (%_% ymm2) *)
  0xc4; 0x62; 0x7d; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm11) (%_% ymm0) (%_% ymm3) *)
  0xc4; 0x62; 0x7d; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm12) (%_% ymm0) (%_% ymm4) *)
  0xc4; 0x62; 0x7d; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm13) (%_% ymm0) (%_% ymm5) *)
  0xc4; 0x62; 0x7d; 0x28; 0xf6;
                           (* VPMULDQ (%_% ymm14) (%_% ymm0) (%_% ymm6) *)
  0xc4; 0x62; 0x7d; 0x28; 0xff;
                           (* VPMULDQ (%_% ymm15) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x42; 0x75; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm1) (%_% ymm10) *)
  0xc4; 0x42; 0x75; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm11) (%_% ymm1) (%_% ymm11) *)
  0xc4; 0x42; 0x75; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm12) (%_% ymm1) (%_% ymm12) *)
  0xc4; 0x42; 0x75; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm13) (%_% ymm1) (%_% ymm13) *)
  0xc4; 0x42; 0x75; 0x28; 0xf6;
                           (* VPMULDQ (%_% ymm14) (%_% ymm1) (%_% ymm14) *)
  0xc4; 0x42; 0x75; 0x28; 0xff;
                           (* VPMULDQ (%_% ymm15) (%_% ymm1) (%_% ymm15) *)
  0xc4; 0xc1; 0x6d; 0xfb; 0xd2;
                           (* VPSUBQ (%_% ymm2) (%_% ymm2) (%_% ymm10) *)
  0xc4; 0xc1; 0x65; 0xfb; 0xdb;
                           (* VPSUBQ (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc1; 0x5d; 0xfb; 0xe4;
                           (* VPSUBQ (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc1; 0x55; 0xfb; 0xed;
                           (* VPSUBQ (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfb; 0xf6;
                           (* VPSUBQ (%_% ymm6) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0xc1; 0x45; 0xfb; 0xff;
                           (* VPSUBQ (%_% ymm7) (%_% ymm7) (%_% ymm15) *)
  0xc5; 0xed; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 32)) *)
  0xc5; 0xdd; 0x73; 0xd4; 0x20;
                           (* VPSRLQ (%_% ymm4) (%_% ymm4) (Imm8 (word 32)) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xe3; 0x6d; 0x02; 0xd3; 0xaa;
                           (* VPBLENDD (%_% ymm2) (%_% ymm2) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xe3; 0x5d; 0x02; 0xe5; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm5) (Imm8 (word 170)) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xf7; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xfd; 0x7f; 0x17;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x77; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm6) *)
  0x48; 0x83; 0xc7; 0x60;  (* ADD (% rdi) (Imm8 (word 96)) *)
  0x48; 0x83; 0xc6; 0x60;  (* ADD (% rsi) (Imm8 (word 96)) *)
  0x48; 0x83; 0xc2; 0x60;  (* ADD (% rdx) (Imm8 (word 96)) *)
  0x83; 0xc0; 0x01;        (* ADD (% eax) (Imm8 (word 1)) *)
  0x83; 0xf8; 0x0a;        (* CMP (% eax) (Imm8 (word 10)) *)
  0x0f; 0x82; 0x07; 0xff; 0xff; 0xff;
                           (* JB (Imm32 (word 4294967047)) *)
  0xc5; 0xfd; 0x6f; 0x16;  (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0xfd; 0x6f; 0x66; 0x20;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0x7d; 0x6f; 0x12;  (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0x7d; 0x6f; 0x62; 0x20;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rdx,32))) *)
  0xc5; 0xe5; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm2) (Imm8 (word 32)) *)
  0xc5; 0xd5; 0x73; 0xd4; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm4) (Imm8 (word 32)) *)
  0xc4; 0x41; 0x7e; 0x16; 0xda;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm12) *)
  0xc4; 0xc2; 0x6d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm2) (%_% ymm10) *)
  0xc4; 0xc2; 0x65; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc2; 0x55; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x7d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm0) (%_% ymm2) *)
  0xc4; 0x62; 0x7d; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm11) (%_% ymm0) (%_% ymm3) *)
  0xc4; 0x62; 0x7d; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm12) (%_% ymm0) (%_% ymm4) *)
  0xc4; 0x62; 0x7d; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm13) (%_% ymm0) (%_% ymm5) *)
  0xc4; 0x42; 0x75; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm1) (%_% ymm10) *)
  0xc4; 0x42; 0x75; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm11) (%_% ymm1) (%_% ymm11) *)
  0xc4; 0x42; 0x75; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm12) (%_% ymm1) (%_% ymm12) *)
  0xc4; 0x42; 0x75; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm13) (%_% ymm1) (%_% ymm13) *)
  0xc4; 0xc1; 0x6d; 0xfb; 0xd2;
                           (* VPSUBQ (%_% ymm2) (%_% ymm2) (%_% ymm10) *)
  0xc4; 0xc1; 0x65; 0xfb; 0xdb;
                           (* VPSUBQ (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc1; 0x5d; 0xfb; 0xe4;
                           (* VPSUBQ (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc1; 0x55; 0xfb; 0xed;
                           (* VPSUBQ (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc5; 0xed; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 32)) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xe3; 0x65; 0x02; 0xd2; 0x55;
                           (* VPBLENDD (%_% ymm2) (%_% ymm3) (%_% ymm2) (Imm8 (word 85)) *)
  0xc4; 0xe3; 0x55; 0x02; 0xe4; 0x55;
                           (* VPBLENDD (%_% ymm4) (%_% ymm5) (%_% ymm4) (Imm8 (word 85)) *)
  0xc5; 0xfd; 0x7f; 0x17;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm4) *)
  0xc3                     (* RET *)
];;

let mldsa_pointwise_tmc = define_trimmed "mldsa_pointwise_tmc" mldsa_pointwise_mc;;
let MLDSA_POINTWISE_TMC_EXEC = X86_MK_CORE_EXEC_RULE mldsa_pointwise_tmc;;
