(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 4-fold Keccak-f1600 using AVX-512VL (aws-lc PR #2720).                    *)
(*                                                                           *)
(* Mirrors x86/proofs/sha3_keccak4_f1600.ml (the AVX2 4x proof) closely.     *)
(* Kernel = s2n-vendored single-function form of aws-lc KeccakF1600_x4_      *)
(* avx512vl: the shared keccak_1600_permute is inlined and its embedded      *)
(* round-constant table is taken as a pointer argument (rsi), exactly as     *)
(* the AVX2 kernel takes rc_pointer. State is register-resident in           *)
(* ymm0..ymm24 (no stack spill), so the proof runs in the DEFAULT ZMM view   *)
(* and the loop invariant carries 25 ymm reads instead of AVX2's             *)
(* `[YMM5] ++ stack` form.                                                   *)
(*                                                                           *)
(* C arguments: rdi = bitstate_in (4 states x 200 bytes), rsi = rc_pointer.  *)
(* Offsets (post-trim tmc = mc - 4): entry 0x0; loop setup mov r10 @ 0x23a,  *)
(*   mov r11 @ 0x240; loop head 0x243; dec 0x5ee; jne -> 0x243; ret 0x834.   *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/keccak_spec.ml";;
needs "common/mlkem_mldsa.ml";;  (* for SIMD_SIMPLIFY_TAC *)

(* ZMM operand view: each 256-bit ymm operand
   reads as word_zx(read ZMMk):512 -> we bound the resulting term bloat during
   stepping with per-step SIMD_SIMPLIFY_TAC_LOCAL (cf mlkem_reduce), and carry
   raw ZMM ghosts in the precondition so stepped reads survive DISCARD_OLDSTATE
   (cf kec_unit_zmm). The discharge bridges read YMMk = word_zx(read ZMMk) via
   READ_ZEROTOP_256; BITBLAST absorbs the word_zx. *)

let sha3_keccak4_f1600_avx512vl_mc = define_assert_from_elf
  "sha3_keccak4_f1600_avx512vl_mc" "x86/sha3/sha3_keccak4_f1600_avx512vl.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x0f;
                           (* VMOVDQU64 (%_% ymm25) (Memop Word256 (%% (rdi,0)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x97; 0xc8; 0x00; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm26) (Memop Word256 (%% (rdi,200)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x9f; 0x90; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm27) (Memop Word256 (%% (rdi,400)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0xa7; 0x58; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm28) (Memop Word256 (%% (rdi,600)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xb5; 0x20; 0x6c; 0xea;
                           (* VPUNPCKLQDQ (%_% ymm29) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xb5; 0x20; 0x6d; 0xf2;
                           (* VPUNPCKHQDQ (%_% ymm30) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xa5; 0x20; 0x6c; 0xcc;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x01; 0xa5; 0x20; 0x6d; 0xd4;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x93; 0x95; 0x20; 0x43; 0xc1; 0x00;
                           (* VSHUFI64X2 (%_% ymm0) (%_% ymm29) (%_% ymm25) (Imm8 (word 0)) *)
  0x62; 0x93; 0x8d; 0x20; 0x43; 0xca; 0x00;
                           (* VSHUFI64X2 (%_% ymm1) (%_% ymm30) (%_% ymm26) (Imm8 (word 0)) *)
  0x62; 0x93; 0x95; 0x20; 0x43; 0xd1; 0x03;
                           (* VSHUFI64X2 (%_% ymm2) (%_% ymm29) (%_% ymm25) (Imm8 (word 3)) *)
  0x62; 0x93; 0x8d; 0x20; 0x43; 0xda; 0x03;
                           (* VSHUFI64X2 (%_% ymm3) (%_% ymm30) (%_% ymm26) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x4f; 0x01;
                           (* VMOVDQU64 (%_% ymm25) (Memop Word256 (%% (rdi,32)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x97; 0xe8; 0x00; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm26) (Memop Word256 (%% (rdi,232)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x9f; 0xb0; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm27) (Memop Word256 (%% (rdi,432)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0xa7; 0x78; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm28) (Memop Word256 (%% (rdi,632)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xb5; 0x20; 0x6c; 0xea;
                           (* VPUNPCKLQDQ (%_% ymm29) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xb5; 0x20; 0x6d; 0xf2;
                           (* VPUNPCKHQDQ (%_% ymm30) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xa5; 0x20; 0x6c; 0xcc;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x01; 0xa5; 0x20; 0x6d; 0xd4;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x93; 0x95; 0x20; 0x43; 0xe1; 0x00;
                           (* VSHUFI64X2 (%_% ymm4) (%_% ymm29) (%_% ymm25) (Imm8 (word 0)) *)
  0x62; 0x93; 0x8d; 0x20; 0x43; 0xea; 0x00;
                           (* VSHUFI64X2 (%_% ymm5) (%_% ymm30) (%_% ymm26) (Imm8 (word 0)) *)
  0x62; 0x93; 0x95; 0x20; 0x43; 0xf1; 0x03;
                           (* VSHUFI64X2 (%_% ymm6) (%_% ymm29) (%_% ymm25) (Imm8 (word 3)) *)
  0x62; 0x93; 0x8d; 0x20; 0x43; 0xfa; 0x03;
                           (* VSHUFI64X2 (%_% ymm7) (%_% ymm30) (%_% ymm26) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x4f; 0x02;
                           (* VMOVDQU64 (%_% ymm25) (Memop Word256 (%% (rdi,64)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x97; 0x08; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm26) (Memop Word256 (%% (rdi,264)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x9f; 0xd0; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm27) (Memop Word256 (%% (rdi,464)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0xa7; 0x98; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm28) (Memop Word256 (%% (rdi,664)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xb5; 0x20; 0x6c; 0xea;
                           (* VPUNPCKLQDQ (%_% ymm29) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xb5; 0x20; 0x6d; 0xf2;
                           (* VPUNPCKHQDQ (%_% ymm30) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xa5; 0x20; 0x6c; 0xcc;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x01; 0xa5; 0x20; 0x6d; 0xd4;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x13; 0x95; 0x20; 0x43; 0xc1; 0x00;
                           (* VSHUFI64X2 (%_% ymm8) (%_% ymm29) (%_% ymm25) (Imm8 (word 0)) *)
  0x62; 0x13; 0x8d; 0x20; 0x43; 0xca; 0x00;
                           (* VSHUFI64X2 (%_% ymm9) (%_% ymm30) (%_% ymm26) (Imm8 (word 0)) *)
  0x62; 0x13; 0x95; 0x20; 0x43; 0xd1; 0x03;
                           (* VSHUFI64X2 (%_% ymm10) (%_% ymm29) (%_% ymm25) (Imm8 (word 3)) *)
  0x62; 0x13; 0x8d; 0x20; 0x43; 0xda; 0x03;
                           (* VSHUFI64X2 (%_% ymm11) (%_% ymm30) (%_% ymm26) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x4f; 0x03;
                           (* VMOVDQU64 (%_% ymm25) (Memop Word256 (%% (rdi,96)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x97; 0x28; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm26) (Memop Word256 (%% (rdi,296)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x9f; 0xf0; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm27) (Memop Word256 (%% (rdi,496)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0xa7; 0xb8; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm28) (Memop Word256 (%% (rdi,696)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xb5; 0x20; 0x6c; 0xea;
                           (* VPUNPCKLQDQ (%_% ymm29) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xb5; 0x20; 0x6d; 0xf2;
                           (* VPUNPCKHQDQ (%_% ymm30) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xa5; 0x20; 0x6c; 0xcc;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x01; 0xa5; 0x20; 0x6d; 0xd4;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x13; 0x95; 0x20; 0x43; 0xe1; 0x00;
                           (* VSHUFI64X2 (%_% ymm12) (%_% ymm29) (%_% ymm25) (Imm8 (word 0)) *)
  0x62; 0x13; 0x8d; 0x20; 0x43; 0xea; 0x00;
                           (* VSHUFI64X2 (%_% ymm13) (%_% ymm30) (%_% ymm26) (Imm8 (word 0)) *)
  0x62; 0x13; 0x95; 0x20; 0x43; 0xf1; 0x03;
                           (* VSHUFI64X2 (%_% ymm14) (%_% ymm29) (%_% ymm25) (Imm8 (word 3)) *)
  0x62; 0x13; 0x8d; 0x20; 0x43; 0xfa; 0x03;
                           (* VSHUFI64X2 (%_% ymm15) (%_% ymm30) (%_% ymm26) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x4f; 0x04;
                           (* VMOVDQU64 (%_% ymm25) (Memop Word256 (%% (rdi,128)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x97; 0x48; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm26) (Memop Word256 (%% (rdi,328)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x9f; 0x10; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm27) (Memop Word256 (%% (rdi,528)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0xa7; 0xd8; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm28) (Memop Word256 (%% (rdi,728)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xb5; 0x20; 0x6c; 0xea;
                           (* VPUNPCKLQDQ (%_% ymm29) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xb5; 0x20; 0x6d; 0xf2;
                           (* VPUNPCKHQDQ (%_% ymm30) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xa5; 0x20; 0x6c; 0xcc;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x01; 0xa5; 0x20; 0x6d; 0xd4;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x83; 0x95; 0x20; 0x43; 0xc1; 0x00;
                           (* VSHUFI64X2 (%_% ymm16) (%_% ymm29) (%_% ymm25) (Imm8 (word 0)) *)
  0x62; 0x83; 0x8d; 0x20; 0x43; 0xca; 0x00;
                           (* VSHUFI64X2 (%_% ymm17) (%_% ymm30) (%_% ymm26) (Imm8 (word 0)) *)
  0x62; 0x83; 0x95; 0x20; 0x43; 0xd1; 0x03;
                           (* VSHUFI64X2 (%_% ymm18) (%_% ymm29) (%_% ymm25) (Imm8 (word 3)) *)
  0x62; 0x83; 0x8d; 0x20; 0x43; 0xda; 0x03;
                           (* VSHUFI64X2 (%_% ymm19) (%_% ymm30) (%_% ymm26) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x4f; 0x05;
                           (* VMOVDQU64 (%_% ymm25) (Memop Word256 (%% (rdi,160)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x97; 0x68; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm26) (Memop Word256 (%% (rdi,360)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x9f; 0x30; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm27) (Memop Word256 (%% (rdi,560)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0xa7; 0xf8; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm28) (Memop Word256 (%% (rdi,760)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xb5; 0x20; 0x6c; 0xea;
                           (* VPUNPCKLQDQ (%_% ymm29) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xb5; 0x20; 0x6d; 0xf2;
                           (* VPUNPCKHQDQ (%_% ymm30) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xa5; 0x20; 0x6c; 0xcc;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x01; 0xa5; 0x20; 0x6d; 0xd4;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x83; 0x95; 0x20; 0x43; 0xe1; 0x00;
                           (* VSHUFI64X2 (%_% ymm20) (%_% ymm29) (%_% ymm25) (Imm8 (word 0)) *)
  0x62; 0x83; 0x8d; 0x20; 0x43; 0xea; 0x00;
                           (* VSHUFI64X2 (%_% ymm21) (%_% ymm30) (%_% ymm26) (Imm8 (word 0)) *)
  0x62; 0x83; 0x95; 0x20; 0x43; 0xf1; 0x03;
                           (* VSHUFI64X2 (%_% ymm22) (%_% ymm29) (%_% ymm25) (Imm8 (word 3)) *)
  0x62; 0x83; 0x8d; 0x20; 0x43; 0xfa; 0x03;
                           (* VSHUFI64X2 (%_% ymm23) (%_% ymm30) (%_% ymm26) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfd; 0x08; 0x6e; 0x47; 0x18;
                           (* VMOVQ (%_% xmm24) (Memop Quadword (%% (rdi,192))) *)
  0x62; 0x63; 0xbd; 0x00; 0x22; 0x47; 0x31; 0x01;
                           (* VPINSRQ (%_% xmm24) (%_% xmm24) (Memop Quadword (%% (rdi,392)))
(Imm8 (word 1)) *)
  0x62; 0x61; 0xfd; 0x08; 0x6e; 0x4f; 0x4a;
                           (* VMOVQ (%_% xmm25) (Memop Quadword (%% (rdi,592))) *)
  0x62; 0x63; 0xb5; 0x00; 0x22; 0x4f; 0x63; 0x01;
                           (* VPINSRQ (%_% xmm25) (%_% xmm25) (Memop Quadword (%% (rdi,792)))
(Imm8 (word 1)) *)
  0x62; 0x03; 0x3d; 0x20; 0x38; 0xc1; 0x01;
                           (* VINSERTI32X4 (%_% ymm24) (%_% ymm24) (%_% xmm25) (Imm8 (word 1)) *)
  0x41; 0xba; 0x18; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 24)) *)
  0x49; 0x89; 0xf3;        (* MOV (% r11) (% rsi) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xc8;
                           (* VMOVDQA64 (%_% ymm25) (%_% ymm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xad; 0x28; 0x25; 0xcd; 0x96;
                           (* VPTERNLOGQ (%_% ymm25) (%_% ymm10) (%_% ymm5) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xd1;
                           (* VMOVDQA64 (%_% ymm26) (%_% ymm1) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xcd; 0x28; 0x25; 0xd3; 0x96;
                           (* VPTERNLOGQ (%_% ymm26) (%_% ymm6) (%_% ymm11) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xda;
                           (* VMOVDQA64 (%_% ymm27) (%_% ymm2) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xc5; 0x28; 0x25; 0xdc; 0x96;
                           (* VPTERNLOGQ (%_% ymm27) (%_% ymm7) (%_% ymm12) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xe3;
                           (* VMOVDQA64 (%_% ymm28) (%_% ymm3) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xbd; 0x28; 0x25; 0xe5; 0x96;
                           (* VPTERNLOGQ (%_% ymm28) (%_% ymm8) (%_% ymm13) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xec;
                           (* VMOVDQA64 (%_% ymm29) (%_% ymm4) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xb5; 0x28; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% ymm29) (%_% ymm9) (%_% ymm14) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0x85; 0x28; 0x25; 0xcc; 0x96;
                           (* VPTERNLOGQ (%_% ymm25) (%_% ymm15) (%_% ymm20) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xfd; 0x20; 0x25; 0xd5; 0x96;
                           (* VPTERNLOGQ (%_% ymm26) (%_% ymm16) (%_% ymm21) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xf5; 0x20; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% ymm27) (%_% ymm17) (%_% ymm22) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xed; 0x20; 0x25; 0xe7; 0x96;
                           (* VPTERNLOGQ (%_% ymm28) (%_% ymm18) (%_% ymm23) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xca; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm26) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x85; 0x20; 0x72; 0xcb; 0x01;
                           (* VPROLQ (%_% ymm31) (%_% ymm27) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0xe5; 0x20; 0x25; 0xe8; 0x96;
                           (* VPTERNLOGQ (%_% ymm29) (%_% ymm19) (%_% ymm24) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm0) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x95; 0x20; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% ymm10) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x95; 0x20; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% ymm20) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x20; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% ymm5) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x95; 0x20; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% ymm15) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xcc; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm28) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x20; 0x25; 0xf7; 0x96;
                           (* VPTERNLOGQ (%_% ymm6) (%_% ymm25) (%_% ymm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xb5; 0x20; 0x25; 0xc7; 0x96;
                           (* VPTERNLOGQ (%_% ymm16) (%_% ymm25) (%_% ymm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x20; 0x25; 0xcf; 0x96;
                           (* VPTERNLOGQ (%_% ymm1) (%_% ymm25) (%_% ymm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xb5; 0x20; 0x25; 0xdf; 0x96;
                           (* VPTERNLOGQ (%_% ymm11) (%_% ymm25) (%_% ymm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xb5; 0x20; 0x25; 0xef; 0x96;
                           (* VPTERNLOGQ (%_% ymm21) (%_% ymm25) (%_% ymm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x85; 0x20; 0x72; 0xcd; 0x01;
                           (* VPROLQ (%_% ymm31) (%_% ymm29) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x42; 0xfd; 0x28; 0x59; 0x2b;
                           (* VPBROADCASTQ (%_% ymm29) (Memop Quadword (%% (r11,0))) *)
  0x49; 0x83; 0xc3; 0x08;  (* ADD (% r11) (Imm8 (word 8)) *)
  0x62; 0x13; 0xad; 0x20; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% ymm12) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x20; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% ymm7) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xad; 0x20; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% ymm22) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xad; 0x20; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% ymm17) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x20; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% ymm2) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xc9; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm25) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xa5; 0x20; 0x25; 0xdf; 0x96;
                           (* VPTERNLOGQ (%_% ymm3) (%_% ymm27) (%_% ymm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xa5; 0x20; 0x25; 0xef; 0x96;
                           (* VPTERNLOGQ (%_% ymm13) (%_% ymm27) (%_% ymm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x20; 0x25; 0xff; 0x96;
                           (* VPTERNLOGQ (%_% ymm23) (%_% ymm27) (%_% ymm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xcd; 0x28; 0x72; 0xce; 0x2c;
                           (* VPROLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 44)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x20; 0x25; 0xd7; 0x96;
                           (* VPTERNLOGQ (%_% ymm18) (%_% ymm27) (%_% ymm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xa5; 0x20; 0x25; 0xc7; 0x96;
                           (* VPTERNLOGQ (%_% ymm8) (%_% ymm27) (%_% ymm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x9d; 0x28; 0x72; 0xcc; 0x2b;
                           (* VPROLQ (%_% ymm12) (%_% ymm12) (Imm8 (word 43)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xed; 0x20; 0x72; 0xca; 0x15;
                           (* VPROLQ (%_% ymm18) (%_% ymm18) (Imm8 (word 21)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0x9d; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm24) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xbd; 0x20; 0x72; 0xc8; 0x0e;
                           (* VPROLQ (%_% ymm24) (%_% ymm24) (Imm8 (word 14)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xe5; 0x28; 0x72; 0xcb; 0x1c;
                           (* VPROLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 28)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x20; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% ymm9) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xb5; 0x28; 0x72; 0xc9; 0x14;
                           (* VPROLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 20)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xad; 0x28; 0x72; 0xca; 0x03;
                           (* VPROLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 3)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x20; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% ymm19) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xfd; 0x20; 0x72; 0xc8; 0x2d;
                           (* VPROLQ (%_% ymm16) (%_% ymm16) (Imm8 (word 45)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xcd; 0x20; 0x72; 0xce; 0x3d;
                           (* VPROLQ (%_% ymm22) (%_% ymm22) (Imm8 (word 61)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x9d; 0x20; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% ymm4) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xf5; 0x28; 0x72; 0xc9; 0x01;
                           (* VPROLQ (%_% ymm1) (%_% ymm1) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xc5; 0x28; 0x72; 0xcf; 0x06;
                           (* VPROLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 6)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x20; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% ymm14) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x95; 0x28; 0x72; 0xcd; 0x19;
                           (* VPROLQ (%_% ymm13) (%_% ymm13) (Imm8 (word 25)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xe5; 0x20; 0x72; 0xcb; 0x08;
                           (* VPROLQ (%_% ymm19) (%_% ymm19) (Imm8 (word 8)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf0;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xcd; 0x28; 0x25; 0xf4; 0xd2;
                           (* VPTERNLOGQ (%_% ymm30) (%_% ymm6) (%_% ymm12) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xdd; 0x20; 0x72; 0xcc; 0x12;
                           (* VPROLQ (%_% ymm20) (%_% ymm20) (Imm8 (word 18)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xdd; 0x28; 0x72; 0xcc; 0x1b;
                           (* VPROLQ (%_% ymm4) (%_% ymm4) (Imm8 (word 27)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0x8d; 0x20; 0xef; 0xf5;
                           (* VPXORQ (%_% ymm30) (%_% ymm30) (%_% ymm29) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xd5; 0x28; 0x72; 0xcd; 0x24;
                           (* VPROLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 36)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xa5; 0x28; 0x72; 0xcb; 0x0a;
                           (* VPROLQ (%_% ymm11) (%_% ymm11) (Imm8 (word 10)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xfe;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm6) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0x9d; 0x28; 0x25; 0xfa; 0xd2;
                           (* VPTERNLOGQ (%_% ymm31) (%_% ymm12) (%_% ymm18) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xf5; 0x20; 0x72; 0xc9; 0x0f;
                           (* VPROLQ (%_% ymm17) (%_% ymm17) (Imm8 (word 15)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xc5; 0x20; 0x72; 0xcf; 0x38;
                           (* VPROLQ (%_% ymm23) (%_% ymm23) (Imm8 (word 56)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xed; 0x20; 0x25; 0xe0; 0xd2;
                           (* VPTERNLOGQ (%_% ymm12) (%_% ymm18) (%_% ymm24) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xed; 0x28; 0x72; 0xca; 0x3e;
                           (* VPROLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 62)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xbd; 0x28; 0x72; 0xc8; 0x37;
                           (* VPROLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 55)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xbd; 0x20; 0x25; 0xd0; 0xd2;
                           (* VPTERNLOGQ (%_% ymm18) (%_% ymm24) (%_% ymm0) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x8d; 0x28; 0x72; 0xce; 0x27;
                           (* VPROLQ (%_% ymm14) (%_% ymm14) (Imm8 (word 39)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x85; 0x28; 0x72; 0xcf; 0x29;
                           (* VPROLQ (%_% ymm15) (%_% ymm15) (Imm8 (word 41)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xfd; 0x28; 0x25; 0xc6; 0xd2;
                           (* VPTERNLOGQ (%_% ymm24) (%_% ymm0) (%_% ymm6) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x28; 0x6f; 0xc6;
                           (* VMOVDQA64 (%_% ymm0) (%_% ymm30) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x28; 0x6f; 0xf7;
                           (* VMOVDQA64 (%_% ymm6) (%_% ymm31) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xd5; 0x20; 0x72; 0xcd; 0x02;
                           (* VPROLQ (%_% ymm21) (%_% ymm21) (Imm8 (word 2)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf3;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm3) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xb5; 0x28; 0x25; 0xf2; 0xd2;
                           (* VPTERNLOGQ (%_% ymm30) (%_% ymm9) (%_% ymm10) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm9) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xad; 0x28; 0x25; 0xf8; 0xd2;
                           (* VPTERNLOGQ (%_% ymm31) (%_% ymm10) (%_% ymm16) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xfd; 0x20; 0x25; 0xd6; 0xd2;
                           (* VPTERNLOGQ (%_% ymm10) (%_% ymm16) (%_% ymm22) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xcd; 0x20; 0x25; 0xc3; 0xd2;
                           (* VPTERNLOGQ (%_% ymm16) (%_% ymm22) (%_% ymm3) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0xe5; 0x28; 0x25; 0xf1; 0xd2;
                           (* VPTERNLOGQ (%_% ymm22) (%_% ymm3) (%_% ymm9) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x28; 0x6f; 0xde;
                           (* VMOVDQA64 (%_% ymm3) (%_% ymm30) (Evex_deco Unmasked No_brc) *)
  0x62; 0x11; 0xfd; 0x28; 0x6f; 0xcf;
                           (* VMOVDQA64 (%_% ymm9) (%_% ymm31) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm1) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xc5; 0x28; 0x25; 0xf5; 0xd2;
                           (* VPTERNLOGQ (%_% ymm30) (%_% ymm7) (%_% ymm13) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xff;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm7) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0x95; 0x28; 0x25; 0xfb; 0xd2;
                           (* VPTERNLOGQ (%_% ymm31) (%_% ymm13) (%_% ymm19) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xe5; 0x20; 0x25; 0xec; 0xd2;
                           (* VPTERNLOGQ (%_% ymm13) (%_% ymm19) (%_% ymm20) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xdd; 0x20; 0x25; 0xd9; 0xd2;
                           (* VPTERNLOGQ (%_% ymm19) (%_% ymm20) (%_% ymm1) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xf5; 0x28; 0x25; 0xe7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm20) (%_% ymm1) (%_% ymm7) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x28; 0x6f; 0xce;
                           (* VMOVDQA64 (%_% ymm1) (%_% ymm30) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x28; 0x6f; 0xff;
                           (* VMOVDQA64 (%_% ymm7) (%_% ymm31) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf4;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm4) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xd5; 0x28; 0x25; 0xf3; 0xd2;
                           (* VPTERNLOGQ (%_% ymm30) (%_% ymm5) (%_% ymm11) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xfd;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm5) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xa5; 0x28; 0x25; 0xf9; 0xd2;
                           (* VPTERNLOGQ (%_% ymm31) (%_% ymm11) (%_% ymm17) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xf5; 0x20; 0x25; 0xdf; 0xd2;
                           (* VPTERNLOGQ (%_% ymm11) (%_% ymm17) (%_% ymm23) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xc5; 0x20; 0x25; 0xcc; 0xd2;
                           (* VPTERNLOGQ (%_% ymm17) (%_% ymm23) (%_% ymm4) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xdd; 0x28; 0x25; 0xfd; 0xd2;
                           (* VPTERNLOGQ (%_% ymm23) (%_% ymm4) (%_% ymm5) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x28; 0x6f; 0xe6;
                           (* VMOVDQA64 (%_% ymm4) (%_% ymm30) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x28; 0x6f; 0xef;
                           (* VMOVDQA64 (%_% ymm5) (%_% ymm31) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf2;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm2) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xbd; 0x28; 0x25; 0xf6; 0xd2;
                           (* VPTERNLOGQ (%_% ymm30) (%_% ymm8) (%_% ymm14) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xf8;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm8) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0x8d; 0x28; 0x25; 0xff; 0xd2;
                           (* VPTERNLOGQ (%_% ymm31) (%_% ymm14) (%_% ymm15) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0x85; 0x28; 0x25; 0xf5; 0xd2;
                           (* VPTERNLOGQ (%_% ymm14) (%_% ymm15) (%_% ymm21) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x73; 0xd5; 0x20; 0x25; 0xfa; 0xd2;
                           (* VPTERNLOGQ (%_% ymm15) (%_% ymm21) (%_% ymm2) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0xed; 0x28; 0x25; 0xe8; 0xd2;
                           (* VPTERNLOGQ (%_% ymm21) (%_% ymm2) (%_% ymm8) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x28; 0x6f; 0xd6;
                           (* VMOVDQA64 (%_% ymm2) (%_% ymm30) (Evex_deco Unmasked No_brc) *)
  0x62; 0x11; 0xfd; 0x28; 0x6f; 0xc7;
                           (* VMOVDQA64 (%_% ymm8) (%_% ymm31) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf3;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm3) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xfd; 0x28; 0x6f; 0xda;
                           (* VMOVDQA64 (%_% ymm3) (%_% ymm18) (Evex_deco Unmasked No_brc) *)
  0x62; 0xa1; 0xfd; 0x28; 0x6f; 0xd1;
                           (* VMOVDQA64 (%_% ymm18) (%_% ymm17) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc1; 0xfd; 0x28; 0x6f; 0xcb;
                           (* VMOVDQA64 (%_% ymm17) (%_% ymm11) (Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfd; 0x28; 0x6f; 0xdf;
                           (* VMOVDQA64 (%_% ymm11) (%_% ymm7) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xfd; 0x28; 0x6f; 0xfa;
                           (* VMOVDQA64 (%_% ymm7) (%_% ymm10) (Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfd; 0x28; 0x6f; 0xd1;
                           (* VMOVDQA64 (%_% ymm10) (%_% ymm1) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfd; 0x28; 0x6f; 0xce;
                           (* VMOVDQA64 (%_% ymm1) (%_% ymm6) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xfd; 0x28; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% ymm6) (%_% ymm9) (Evex_deco Unmasked No_brc) *)
  0x62; 0x31; 0xfd; 0x28; 0x6f; 0xce;
                           (* VMOVDQA64 (%_% ymm9) (%_% ymm22) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc1; 0xfd; 0x28; 0x6f; 0xf6;
                           (* VMOVDQA64 (%_% ymm22) (%_% ymm14) (Evex_deco Unmasked No_brc) *)
  0x62; 0x31; 0xfd; 0x28; 0x6f; 0xf4;
                           (* VMOVDQA64 (%_% ymm14) (%_% ymm20) (Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfd; 0x28; 0x6f; 0xe2;
                           (* VMOVDQA64 (%_% ymm20) (%_% ymm2) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xfd; 0x28; 0x6f; 0xd4;
                           (* VMOVDQA64 (%_% ymm2) (%_% ymm12) (Evex_deco Unmasked No_brc) *)
  0x62; 0x51; 0xfd; 0x28; 0x6f; 0xe5;
                           (* VMOVDQA64 (%_% ymm12) (%_% ymm13) (Evex_deco Unmasked No_brc) *)
  0x62; 0x31; 0xfd; 0x28; 0x6f; 0xeb;
                           (* VMOVDQA64 (%_% ymm13) (%_% ymm19) (Evex_deco Unmasked No_brc) *)
  0x62; 0xa1; 0xfd; 0x28; 0x6f; 0xdf;
                           (* VMOVDQA64 (%_% ymm19) (%_% ymm23) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc1; 0xfd; 0x28; 0x6f; 0xff;
                           (* VMOVDQA64 (%_% ymm23) (%_% ymm15) (Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfd; 0x28; 0x6f; 0xfc;
                           (* VMOVDQA64 (%_% ymm15) (%_% ymm4) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x28; 0x6f; 0xe0;
                           (* VMOVDQA64 (%_% ymm4) (%_% ymm24) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x28; 0x6f; 0xc5;
                           (* VMOVDQA64 (%_% ymm24) (%_% ymm21) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc1; 0xfd; 0x28; 0x6f; 0xe8;
                           (* VMOVDQA64 (%_% ymm21) (%_% ymm8) (Evex_deco Unmasked No_brc) *)
  0x62; 0x31; 0xfd; 0x28; 0x6f; 0xc0;
                           (* VMOVDQA64 (%_% ymm8) (%_% ymm16) (Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfd; 0x28; 0x6f; 0xc5;
                           (* VMOVDQA64 (%_% ymm16) (%_% ymm5) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x28; 0x6f; 0xee;
                           (* VMOVDQA64 (%_% ymm5) (%_% ymm30) (Evex_deco Unmasked No_brc) *)
  0x41; 0xff; 0xca;        (* DEC (% r10d) *)
  0x0f; 0x85; 0x4c; 0xfc; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294966348)) *)
  0x62; 0x61; 0xfd; 0x28; 0x6c; 0xc9;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm0) (%_% ymm1) *)
  0x62; 0x61; 0xfd; 0x28; 0x6d; 0xd1;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm0) (%_% ymm1) *)
  0x62; 0x61; 0xed; 0x28; 0x6c; 0xdb;
                           (* VPUNPCKLQDQ (%_% ymm27) (%_% ymm2) (%_% ymm3) *)
  0x62; 0x61; 0xed; 0x28; 0x6d; 0xe3;
                           (* VPUNPCKHQDQ (%_% ymm28) (%_% ymm2) (%_% ymm3) *)
  0x62; 0x93; 0xb5; 0x20; 0x43; 0xc3; 0x00;
                           (* VSHUFI64X2 (%_% ymm0) (%_% ymm25) (%_% ymm27) (Imm8 (word 0)) *)
  0x62; 0x93; 0xad; 0x20; 0x43; 0xcc; 0x00;
                           (* VSHUFI64X2 (%_% ymm1) (%_% ymm26) (%_% ymm28) (Imm8 (word 0)) *)
  0x62; 0x93; 0xb5; 0x20; 0x43; 0xd3; 0x03;
                           (* VSHUFI64X2 (%_% ymm2) (%_% ymm25) (%_% ymm27) (Imm8 (word 3)) *)
  0x62; 0x93; 0xad; 0x20; 0x43; 0xdc; 0x03;
                           (* VSHUFI64X2 (%_% ymm3) (%_% ymm26) (%_% ymm28) (Imm8 (word 3)) *)
  0x62; 0xf1; 0xfe; 0x28; 0x7f; 0x07;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,0))) (%_% ymm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x28; 0x7f; 0x8f; 0xc8; 0x00; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,200))) (%_% ymm1)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x28; 0x7f; 0x97; 0x90; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,400))) (%_% ymm2)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x28; 0x7f; 0x9f; 0x58; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,600))) (%_% ymm3)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xdd; 0x28; 0x6c; 0xcd;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm4) (%_% ymm5) *)
  0x62; 0x61; 0xdd; 0x28; 0x6d; 0xd5;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm4) (%_% ymm5) *)
  0x62; 0x61; 0xcd; 0x28; 0x6c; 0xdf;
                           (* VPUNPCKLQDQ (%_% ymm27) (%_% ymm6) (%_% ymm7) *)
  0x62; 0x61; 0xcd; 0x28; 0x6d; 0xe7;
                           (* VPUNPCKHQDQ (%_% ymm28) (%_% ymm6) (%_% ymm7) *)
  0x62; 0x93; 0xb5; 0x20; 0x43; 0xe3; 0x00;
                           (* VSHUFI64X2 (%_% ymm4) (%_% ymm25) (%_% ymm27) (Imm8 (word 0)) *)
  0x62; 0x93; 0xad; 0x20; 0x43; 0xec; 0x00;
                           (* VSHUFI64X2 (%_% ymm5) (%_% ymm26) (%_% ymm28) (Imm8 (word 0)) *)
  0x62; 0x93; 0xb5; 0x20; 0x43; 0xf3; 0x03;
                           (* VSHUFI64X2 (%_% ymm6) (%_% ymm25) (%_% ymm27) (Imm8 (word 3)) *)
  0x62; 0x93; 0xad; 0x20; 0x43; 0xfc; 0x03;
                           (* VSHUFI64X2 (%_% ymm7) (%_% ymm26) (%_% ymm28) (Imm8 (word 3)) *)
  0x62; 0xf1; 0xfe; 0x28; 0x7f; 0x67; 0x01;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,32))) (%_% ymm4)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x28; 0x7f; 0xaf; 0xe8; 0x00; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,232))) (%_% ymm5)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x28; 0x7f; 0xb7; 0xb0; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,432))) (%_% ymm6)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x28; 0x7f; 0xbf; 0x78; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,632))) (%_% ymm7)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xbd; 0x28; 0x6c; 0xc9;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm8) (%_% ymm9) *)
  0x62; 0x41; 0xbd; 0x28; 0x6d; 0xd1;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm8) (%_% ymm9) *)
  0x62; 0x41; 0xad; 0x28; 0x6c; 0xdb;
                           (* VPUNPCKLQDQ (%_% ymm27) (%_% ymm10) (%_% ymm11) *)
  0x62; 0x41; 0xad; 0x28; 0x6d; 0xe3;
                           (* VPUNPCKHQDQ (%_% ymm28) (%_% ymm10) (%_% ymm11) *)
  0x62; 0x13; 0xb5; 0x20; 0x43; 0xc3; 0x00;
                           (* VSHUFI64X2 (%_% ymm8) (%_% ymm25) (%_% ymm27) (Imm8 (word 0)) *)
  0x62; 0x13; 0xad; 0x20; 0x43; 0xcc; 0x00;
                           (* VSHUFI64X2 (%_% ymm9) (%_% ymm26) (%_% ymm28) (Imm8 (word 0)) *)
  0x62; 0x13; 0xb5; 0x20; 0x43; 0xd3; 0x03;
                           (* VSHUFI64X2 (%_% ymm10) (%_% ymm25) (%_% ymm27) (Imm8 (word 3)) *)
  0x62; 0x13; 0xad; 0x20; 0x43; 0xdc; 0x03;
                           (* VSHUFI64X2 (%_% ymm11) (%_% ymm26) (%_% ymm28) (Imm8 (word 3)) *)
  0x62; 0x71; 0xfe; 0x28; 0x7f; 0x47; 0x02;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,64))) (%_% ymm8)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x28; 0x7f; 0x8f; 0x08; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,264))) (%_% ymm9)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x28; 0x7f; 0x97; 0xd0; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,464))) (%_% ymm10)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x28; 0x7f; 0x9f; 0x98; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,664))) (%_% ymm11)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0x9d; 0x28; 0x6c; 0xcd;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm12) (%_% ymm13) *)
  0x62; 0x41; 0x9d; 0x28; 0x6d; 0xd5;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm12) (%_% ymm13) *)
  0x62; 0x41; 0x8d; 0x28; 0x6c; 0xdf;
                           (* VPUNPCKLQDQ (%_% ymm27) (%_% ymm14) (%_% ymm15) *)
  0x62; 0x41; 0x8d; 0x28; 0x6d; 0xe7;
                           (* VPUNPCKHQDQ (%_% ymm28) (%_% ymm14) (%_% ymm15) *)
  0x62; 0x13; 0xb5; 0x20; 0x43; 0xe3; 0x00;
                           (* VSHUFI64X2 (%_% ymm12) (%_% ymm25) (%_% ymm27) (Imm8 (word 0)) *)
  0x62; 0x13; 0xad; 0x20; 0x43; 0xec; 0x00;
                           (* VSHUFI64X2 (%_% ymm13) (%_% ymm26) (%_% ymm28) (Imm8 (word 0)) *)
  0x62; 0x13; 0xb5; 0x20; 0x43; 0xf3; 0x03;
                           (* VSHUFI64X2 (%_% ymm14) (%_% ymm25) (%_% ymm27) (Imm8 (word 3)) *)
  0x62; 0x13; 0xad; 0x20; 0x43; 0xfc; 0x03;
                           (* VSHUFI64X2 (%_% ymm15) (%_% ymm26) (%_% ymm28) (Imm8 (word 3)) *)
  0x62; 0x71; 0xfe; 0x28; 0x7f; 0x67; 0x03;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,96))) (%_% ymm12)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x28; 0x7f; 0xaf; 0x28; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,296))) (%_% ymm13)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x28; 0x7f; 0xb7; 0xf0; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,496))) (%_% ymm14)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x28; 0x7f; 0xbf; 0xb8; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,696))) (%_% ymm15)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x20; 0x6c; 0xc9;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm16) (%_% ymm17) *)
  0x62; 0x21; 0xfd; 0x20; 0x6d; 0xd1;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm16) (%_% ymm17) *)
  0x62; 0x21; 0xed; 0x20; 0x6c; 0xdb;
                           (* VPUNPCKLQDQ (%_% ymm27) (%_% ymm18) (%_% ymm19) *)
  0x62; 0x21; 0xed; 0x20; 0x6d; 0xe3;
                           (* VPUNPCKHQDQ (%_% ymm28) (%_% ymm18) (%_% ymm19) *)
  0x62; 0x83; 0xb5; 0x20; 0x43; 0xc3; 0x00;
                           (* VSHUFI64X2 (%_% ymm16) (%_% ymm25) (%_% ymm27) (Imm8 (word 0)) *)
  0x62; 0x83; 0xad; 0x20; 0x43; 0xcc; 0x00;
                           (* VSHUFI64X2 (%_% ymm17) (%_% ymm26) (%_% ymm28) (Imm8 (word 0)) *)
  0x62; 0x83; 0xb5; 0x20; 0x43; 0xd3; 0x03;
                           (* VSHUFI64X2 (%_% ymm18) (%_% ymm25) (%_% ymm27) (Imm8 (word 3)) *)
  0x62; 0x83; 0xad; 0x20; 0x43; 0xdc; 0x03;
                           (* VSHUFI64X2 (%_% ymm19) (%_% ymm26) (%_% ymm28) (Imm8 (word 3)) *)
  0x62; 0xe1; 0xfe; 0x28; 0x7f; 0x47; 0x04;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,128))) (%_% ymm16)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x28; 0x7f; 0x8f; 0x48; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,328))) (%_% ymm17)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x28; 0x7f; 0x97; 0x10; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,528))) (%_% ymm18)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x28; 0x7f; 0x9f; 0xd8; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,728))) (%_% ymm19)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xdd; 0x20; 0x6c; 0xcd;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm20) (%_% ymm21) *)
  0x62; 0x21; 0xdd; 0x20; 0x6d; 0xd5;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm20) (%_% ymm21) *)
  0x62; 0x21; 0xcd; 0x20; 0x6c; 0xdf;
                           (* VPUNPCKLQDQ (%_% ymm27) (%_% ymm22) (%_% ymm23) *)
  0x62; 0x21; 0xcd; 0x20; 0x6d; 0xe7;
                           (* VPUNPCKHQDQ (%_% ymm28) (%_% ymm22) (%_% ymm23) *)
  0x62; 0x83; 0xb5; 0x20; 0x43; 0xe3; 0x00;
                           (* VSHUFI64X2 (%_% ymm20) (%_% ymm25) (%_% ymm27) (Imm8 (word 0)) *)
  0x62; 0x83; 0xad; 0x20; 0x43; 0xec; 0x00;
                           (* VSHUFI64X2 (%_% ymm21) (%_% ymm26) (%_% ymm28) (Imm8 (word 0)) *)
  0x62; 0x83; 0xb5; 0x20; 0x43; 0xf3; 0x03;
                           (* VSHUFI64X2 (%_% ymm22) (%_% ymm25) (%_% ymm27) (Imm8 (word 3)) *)
  0x62; 0x83; 0xad; 0x20; 0x43; 0xfc; 0x03;
                           (* VSHUFI64X2 (%_% ymm23) (%_% ymm26) (%_% ymm28) (Imm8 (word 3)) *)
  0x62; 0xe1; 0xfe; 0x28; 0x7f; 0x67; 0x05;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,160))) (%_% ymm20)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x28; 0x7f; 0xaf; 0x68; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,360))) (%_% ymm21)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x28; 0x7f; 0xb7; 0x30; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,560))) (%_% ymm22)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x28; 0x7f; 0xbf; 0xf8; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,760))) (%_% ymm23)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0x7d; 0x28; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI32X4 (%_% xmm25) (%_% ymm24) (Imm8 (word 1)) *)
  0x62; 0x61; 0xfd; 0x08; 0x7e; 0x47; 0x18;
                           (* VMOVQ (Memop Quadword (%% (rdi,192))) (%_% xmm24) *)
  0x62; 0x63; 0xfd; 0x08; 0x16; 0x47; 0x31; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,392))) (%_% xmm24) (Imm8 (word 1)) *)
  0x62; 0x61; 0xfd; 0x08; 0x7e; 0x4f; 0x4a;
                           (* VMOVQ (Memop Quadword (%% (rdi,592))) (%_% xmm25) *)
  0x62; 0x63; 0xfd; 0x08; 0x16; 0x4f; 0x63; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,792))) (%_% xmm25) (Imm8 (word 1)) *)
  0xc5; 0xf8; 0x77;        (* VZEROUPPER *)
  0xc3                     (* RET *)
];;

let sha3_keccak4_f1600_avx512vl_tmc =
  define_trimmed "sha3_keccak4_f1600_avx512vl_tmc" sha3_keccak4_f1600_avx512vl_mc;;

let SHA3_KECCAK4_F1600_AVX512VL_EXEC =
  X86_MK_CORE_EXEC_RULE sha3_keccak4_f1600_avx512vl_tmc;;

(* ------------------------------------------------------------------------- *)
(* M1 - round-body CORRECTNESS. Mirrors the AVX2 4x preservation subgoal      *)
(* (sha3_keccak4_f1600.ml lines 972-1022): stepping the 142-instruction round *)
(* body carries the 4-way packed state to one keccak_round of each lane. The  *)
(* round constant `rc` is broadcast to all 4 lanes (vpbroadcastq (%r11)).     *)
(* Register-resident (ymm0..24), ZMM view; stepping uses the mlkem-CORE style *)
(* (GHOST_INTRO YMM + X86_STEPS + SIMD_SIMPLIFY) proven to work in ZMM view.  *)
(* ------------------------------------------------------------------------- *)

let keccak4_pack = define
 `keccak4_pack (B1:int64 list) B2 B3 B4 : int256 list =
    MAP2 word_join
      ((MAP2 word_join B4 B3):int128 list)
      ((MAP2 word_join B2 B1):int128 list)`;;

(* Clean ALL assumptions (incl. the ZMM view's int512 `read ZMMk` values that
   the standard int256-filtered SIMD_SIMPLIFY_TAC skips) - the key to a fast
   ZMM-view discharge, as in mlkem_reduce's ZMM proof. *)
let SIMD_SIMPLIFY_TAC_LOCAL unfold_defs =
  RULE_ASSUM_TAC(CONV_RULE(SIMD_SIMPLIFY_CONV unfold_defs));;

(* Lanewise decomposition helper: int256 equality iff its 4 x int64 sublane
   equalities. Turns each ROUND_CORRECT lane goal into 4 sub-BITBLASTs of
   ~512 free bits (theta+chi mixing) instead of one ~6400-bit monolithic
   BITBLAST -- required to fit in memory (the 25-lane monolithic version OOM'd
   at 59 GB). *)
let INT256_EQ_LANES = prove
 (`!x y:int256.
     x = y <=>
     (word_subword x (0,64)):int64 = word_subword y (0,64) /\
     (word_subword x (64,64)):int64 = word_subword y (64,64) /\
     (word_subword x (128,64)):int64 = word_subword y (128,64) /\
     (word_subword x (192,64)):int64 = word_subword y (192,64)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    BITBLAST_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Per-step word_zx round-trip collapse (keeps ZMM-view stepped terms clean  *)
(* so the discharge goals stay small and structurally lane-aligned).         *)
let WORD_SUBWORD_WORD_ZX = prove
 (`!(x:N word) pos len. pos + len <= dimindex(:N) /\ dimindex(:N) <= dimindex(:M)
      ==> word_subword ((word_zx x):M word) (pos,len):P word = word_subword x (pos,len)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_ZX] THEN
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> c) ==> (a /\ (c /\ d) <=> a /\ d)`) THEN
  REWRITE_TAC[ARITH_RULE `i < MIN a b <=> i < a /\ i < b`] THEN ASM_ARITH_TAC);;
let ZXWS = [0;32;64;96;128;160;192;224;256;320;384;448;512];;
let mkle a b = ARITH_RULE(mk_comb(mk_comb(`(<=):num->num->bool`, mk_small_numeral a), mk_small_numeral b));;
let mksumle a b c = ARITH_RULE(mk_comb(mk_comb(`(<=):num->num->bool`, mk_binop `(+):num->num->num` (mk_small_numeral a)(mk_small_numeral b)), mk_small_numeral c));;
let ZX_LEFACTS = (List.concat(map(fun a->List.concat(map(fun b->if a<=b then [mkle a b] else [])ZXWS)) ZXWS)) @
  (List.concat(map(fun a->List.concat(map(fun b->List.concat(map(fun c->if a+b<=c then [mksumle a b c] else [])ZXWS))ZXWS))ZXWS));;
let ZXCOLLAPSE = SIMP_CONV([WORD_ZX_ZX; WORD_SUBWORD_WORD_ZX; DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;DIMINDEX_512] @ ZX_LEFACTS);;
(* Collapse only the freshly-written hypotheses that actually carry a word_zx
   redex (word_zx(word_zx ..) or word_subword(word_zx ..)); the ~24 stable
   register hyps are already at fixpoint, so re-running ZXCOLLAPSE on them each
   step is pure waste.  Skipping them ~halves the per-step collapse cost with an
   identical result (ZXCOLLAPSE is a no-op on redex-free terms). *)
let rec zx_collapsible t =
  match t with
  | Comb(Const("word_zx",_), Comb(Const("word_zx",_),_)) -> true
  | Comb(Comb(Const("word_subword",_), Comb(Const("word_zx",_),_)), _) -> true
  | Comb(a,b) -> zx_collapsible a || zx_collapsible b
  | Abs(_,b) -> zx_collapsible b
  | _ -> false;;
let ZXCOLLAPSE_TAC : tactic =
  RULE_ASSUM_TAC(fun th ->
    if zx_collapsible (concl th) then CONV_RULE ZXCOLLAPSE th else th);;

(* ------------------------------------------------------------------------- *)
(* Prove-once/compose-per-buffer lane discharge.                             *)
(* A round output int256 register holds the SAME keccak_round lane computed  *)
(* on 4 independent buffers B1..B4 (positions 0/64/128/192 of the packed     *)
(* word_join).  Splitting into the 4 int64 sublanes and pushing word_subword *)
(* inward (through and/or/xor/not/join/zx) isolates ONE buffer per sublane   *)
(* (~1600 free bits vs ~6400), and the 4 sublanes are buffer-renamings of    *)
(* each other -> BITBLAST the first, INST the rest for free (~10x/lane).      *)
let SWP : conv =
  let aox = GEN_REWRITE_CONV I [WORD_SUBWORD_AND; WORD_SUBWORD_OR; WORD_SUBWORD_XOR] in
  let notm = PART_MATCH (lhs o rand) WORD_SUBWORD_NOT in
  let dis = (REWRITE_CONV[DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THENC NUM_REDUCE_CONV) in
  let push1 t =
    (try WORD_SIMPLE_SUBWORD_CONV t with Failure _ ->
     try aox t with Failure _ ->
     let th = notm t in MP th (EQT_ELIM(dis (lhand(concl th))))) in
  TOP_DEPTH_CONV push1;;

let LANE_TAC : tactic =
  let islist v = match type_of v with Tyapp("list",_)->true | _->false in
  ONCE_REWRITE_TAC[INT256_EQ_LANES] THEN
  CONV_TAC SWP THEN
  W(fun (_,w) ->
     let cs = conjuncts w in
     let g0 = hd cs in
     let b0 = find islist (frees g0) in
     let th0 = prove(g0, BITBLAST_TAC) in
     let thms = map (fun g ->
        if g = g0 then th0
        else let bg = find islist (frees g) in
             let th = INST [bg,b0] th0 in
             EQ_MP (ALPHA (concl th) g) th) cs in
     ACCEPT_TAC(end_itlist CONJ thms));;

(* ------------------------------------------------------------------------- *)
(* M1 round-body correctness (STRONG: carries RDI/RSI/R10/rc-table wordlist  *)
(* and bytes_loaded through pre+post, needed by the loop invariant).         *)
(* ------------------------------------------------------------------------- *)
let ROUND_CORRECT = prove
 (`!pc rcptr rc B1 B2 B3 B4 d rp cnt.
     LENGTH B1 = 25 /\ LENGTH B2 = 25 /\ LENGTH B3 = 25 /\ LENGTH B4 = 25
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (BUTLAST sha3_keccak4_f1600_avx512vl_tmc) /\
            read RIP s = word (pc + 0x243) /\
            read RDI s = d /\ read RSI s = rp /\ read R10 s = cnt /\
            read R11 s = rcptr /\
            read (memory :> bytes64 rcptr) s = rc /\
            wordlist_from_memory(rp,24) s = round_constants /\
            [read YMM0 s; read YMM1 s; read YMM2 s; read YMM3 s; read YMM4 s; read YMM5 s; read YMM6 s; read YMM7 s; read YMM8 s; read YMM9 s; read YMM10 s; read YMM11 s; read YMM12 s; read YMM13 s; read YMM14 s; read YMM15 s; read YMM16 s; read YMM17 s; read YMM18 s; read YMM19 s; read YMM20 s; read YMM21 s; read YMM22 s; read YMM23 s; read YMM24 s] = keccak4_pack B1 B2 B3 B4)
       (\s. bytes_loaded s (word pc) (BUTLAST sha3_keccak4_f1600_avx512vl_tmc) /\
            read RIP s = word (pc + 0x5ee) /\
            read RDI s = d /\ read RSI s = rp /\ read R10 s = cnt /\
            read R11 s = word_add rcptr (word 8) /\
            wordlist_from_memory(rp,24) s = round_constants /\
            [read YMM0 s; read YMM1 s; read YMM2 s; read YMM3 s; read YMM4 s; read YMM5 s; read YMM6 s; read YMM7 s; read YMM8 s; read YMM9 s; read YMM10 s; read YMM11 s; read YMM12 s; read YMM13 s; read YMM14 s; read YMM15 s; read YMM16 s; read YMM17 s; read YMM18 s; read YMM19 s; read YMM20 s; read YMM21 s; read YMM22 s; read YMM23 s; read YMM24 s] =
              keccak4_pack (keccak_round rc B1) (keccak_round rc B2)
                           (keccak_round rc B3) (keccak_round rc B4))
       (MAYCHANGE [RIP; R11] ,,
        MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17; ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23; ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS; fst SHA3_KECCAK4_F1600_AVX512VL_EXEC] THEN
  MAP_EVERY X_GEN_TAC
   [`pc:num`; `rcptr:int64`; `rc:int64`;
    `B1:int64 list`; `B2:int64 list`; `B3:int64 list`; `B4:int64 list`;
    `d:int64`; `rp:int64`; `cnt:int64`] THEN
  REWRITE_TAC[LENGTH_EQ_25] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
  (* packing expansion DEFERRED to discharge (keep lanes folded/opaque) *)
  (* unfold the rc-table wordlist (pre+post) into 24 component 64-bit reads so
     they are frame-preserved single reads, closed by ASM_REWRITE after stepping *)
  REWRITE_TAC[round_constants] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
  REWRITE_TAC[CONS_11] THEN
  REWRITE_TAC[YMM0; YMM1; YMM2; YMM3; YMM4; YMM5; YMM6; YMM7; YMM8; YMM9;
              YMM10; YMM11; YMM12; YMM13; YMM14; YMM15; YMM16; YMM17; YMM18;
              YMM19; YMM20; YMM21; YMM22; YMM23; YMM24; READ_ZEROTOP_256] THEN
  GHOST_INTRO_TAC `zg0:int512` `read ZMM0` THEN
  GHOST_INTRO_TAC `zg1:int512` `read ZMM1` THEN
  GHOST_INTRO_TAC `zg2:int512` `read ZMM2` THEN
  GHOST_INTRO_TAC `zg3:int512` `read ZMM3` THEN
  GHOST_INTRO_TAC `zg4:int512` `read ZMM4` THEN
  GHOST_INTRO_TAC `zg5:int512` `read ZMM5` THEN
  GHOST_INTRO_TAC `zg6:int512` `read ZMM6` THEN
  GHOST_INTRO_TAC `zg7:int512` `read ZMM7` THEN
  GHOST_INTRO_TAC `zg8:int512` `read ZMM8` THEN
  GHOST_INTRO_TAC `zg9:int512` `read ZMM9` THEN
  GHOST_INTRO_TAC `zg10:int512` `read ZMM10` THEN
  GHOST_INTRO_TAC `zg11:int512` `read ZMM11` THEN
  GHOST_INTRO_TAC `zg12:int512` `read ZMM12` THEN
  GHOST_INTRO_TAC `zg13:int512` `read ZMM13` THEN
  GHOST_INTRO_TAC `zg14:int512` `read ZMM14` THEN
  GHOST_INTRO_TAC `zg15:int512` `read ZMM15` THEN
  GHOST_INTRO_TAC `zg16:int512` `read ZMM16` THEN
  GHOST_INTRO_TAC `zg17:int512` `read ZMM17` THEN
  GHOST_INTRO_TAC `zg18:int512` `read ZMM18` THEN
  GHOST_INTRO_TAC `zg19:int512` `read ZMM19` THEN
  GHOST_INTRO_TAC `zg20:int512` `read ZMM20` THEN
  GHOST_INTRO_TAC `zg21:int512` `read ZMM21` THEN
  GHOST_INTRO_TAC `zg22:int512` `read ZMM22` THEN
  GHOST_INTRO_TAC `zg23:int512` `read ZMM23` THEN
  GHOST_INTRO_TAC `zg24:int512` `read ZMM24` THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC SHA3_KECCAK4_F1600_AVX512VL_EXEC [n] THEN ZXCOLLAPSE_TAC) (1--142) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[YMM0; YMM1; YMM2; YMM3; YMM4; YMM5; YMM6; YMM7; YMM8; YMM9;
              YMM10; YMM11; YMM12; YMM13; YMM14; YMM15; YMM16; YMM17; YMM18;
              YMM19; YMM20; YMM21; YMM22; YMM23; YMM24; READ_ZEROTOP_256] THEN
  ASM_REWRITE_TAC[] THEN
  (* packing was deferred: expand the folded precondition packing hyp into per-lane
     equalities (word_zx zg_k = word_join(EL k ...)) so per-bit BITBLAST can relate
     the opaque stepped lanes to B; keep lanes opaque (no substitution -> no re-bloat) *)
  (* deferred packing: split the folded precondition packing into per-lane hyps
     (word_zx zg_k = word_join(EL k B4)(EL k B3)(EL k B2)(EL k B1)), then SUBSTITUTE
     into the goal to make each lane self-contained in EL B, so LANE_TAC applies. *)
  RULE_ASSUM_TAC(REWRITE_RULE[keccak4_pack; MAP2; CONS_11]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check(is_conj o concl))) THEN
  (* substitute the packing (word_zx zg_k -> word_join(EL k B..)) -> goal now concrete
     in EL B, no zg; then the canonical LANE_TAC discharge applies. *)
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[keccak4_pack; keccak_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MAP2; CONS_11] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REPEAT CONJ_TAC THEN LANE_TAC);;

(* Element i (i<24) of the round-constants wordlist in memory = EL i round_constants *)
let RC_AT_R11 = prove
 (`!(x:x86state) rc_pointer:int64 i.
    i < 24 /\ wordlist_from_memory(rc_pointer,24) x = round_constants
    ==> read (memory :> bytes64 (word_add rc_pointer (word (8 * i)))) x =
        EL i round_constants`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `wordlist_from_memory(rc_pointer,24) x = round_constants` THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV
    `wordlist_from_memory(rc_pointer,24) x:int64 list`] THEN
  REWRITE_TAC[round_constants; CONS_11] THEN STRIP_TAC THEN
  UNDISCH_TAC `i < 24` THEN SPEC_TAC(`i:num`,`i:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  ASM_REWRITE_TAC[round_constants; WORD_ADD_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;


(* =========================================================================
   CORE CORRECT theorem (M2-M5).  Flat-kernel offsets (tmc = mc-4):
     entry 0x0 (transpose prologue) ; loop setup mov r10 @0x23a, mov r11 @0x240 ;
     loop head 0x243 ; body ; dec 0x5ee ; jne->0x243 @0x5f1 ;
     epilogue (untranspose+store) 0x5f7 ; vzeroupper 0x831 ; ret 0x834.
   State is register-resident (ymm0..24), RC via pointer arg rsi->r11, NO stack
   scratch and NO internal call (permute inlined).
   ========================================================================= *)

let SHA3_KECCAK4_F1600_AVX512VL_CORRECT = prove
 (`!rc_pointer:int64 bitstate_in:int64 A1 A2 A3 A4 pc:num.
    nonoverlapping (word pc, 0x835) (bitstate_in, 800) /\
    nonoverlapping (word pc, 0x835) (rc_pointer, 192) /\
    nonoverlapping (bitstate_in,800) (rc_pointer,192)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST sha3_keccak4_f1600_avx512vl_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [bitstate_in; rc_pointer] s /\
              wordlist_from_memory(rc_pointer,24) s = round_constants /\
              wordlist_from_memory(bitstate_in,25) s = A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200),25) s = A2 /\
              wordlist_from_memory(word_add bitstate_in (word 400),25) s = A3 /\
              wordlist_from_memory(word_add bitstate_in (word 600),25) s = A4)
             (\s. read RIP s = word(pc + 0x834) /\
                  wordlist_from_memory(bitstate_in,25) s = keccak 24 A1 /\
                  wordlist_from_memory(word_add bitstate_in (word 200),25) s = keccak 24 A2 /\
                  wordlist_from_memory(word_add bitstate_in (word 400),25) s = keccak 24 A3 /\
                  wordlist_from_memory(word_add bitstate_in (word 600),25) s = keccak 24 A4)
           (MAYCHANGE [RIP; R10; R11] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17; ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23; ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes (bitstate_in, 800)])`,
  REWRITE_TAC[SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              fst SHA3_KECCAK4_F1600_AVX512VL_EXEC] THEN
  MAP_EVERY X_GEN_TAC
   [`rc_pointer:int64`;`bitstate_in:int64`;`A1:int64 list`;`A2:int64 list`;
    `A3:int64 list`;`A4:int64 list`;`pc:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  (* degenerate LENGTH<>25 case, as AVX2 (912-921) *)
  ASM_CASES_TAC
   `LENGTH(A1:int64 list)=25 /\ LENGTH(A2:int64 list)=25 /\
    LENGTH(A3:int64 list)=25 /\ LENGTH(A4:int64 list)=25`
  THENL [ALL_TAC;
    ENSURES_INIT_TAC "s0" THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:int64 list->num`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]] THEN

  ENSURES_WHILE_PAUP_TAC `0` `24` `pc + 0x243` `pc + 0x5f1`
  `\i s.
      (read RDI s = bitstate_in /\
       read RSI s = rc_pointer /\
       read R10 s = word (24 - i) /\
       read R11 s = word_add rc_pointer (word (8 * i)) /\
       wordlist_from_memory(rc_pointer,24) s = round_constants /\
       [read YMM0 s; read YMM1 s; read YMM2 s; read YMM3 s; read YMM4 s; read YMM5 s; read YMM6 s; read YMM7 s; read YMM8 s; read YMM9 s; read YMM10 s; read YMM11 s; read YMM12 s; read YMM13 s; read YMM14 s; read YMM15 s; read YMM16 s; read YMM17 s; read YMM18 s; read YMM19 s; read YMM20 s; read YMM21 s; read YMM22 s; read YMM23 s; read YMM24 s] =
         keccak4_pack (keccak i A1) (keccak i A2) (keccak i A3) (keccak i A4)) /\
      (read ZF s <=> i = 24)` THEN
  REPEAT CONJ_TAC THENL
   [(*** 1: 0 < 24 ***) ARITH_TAC;

    (*** 2: initial holding (entry -> 0x243): load+transpose prologue,
         discharge the 25 YMM lanes per-lane with BITBLAST_TAC.  PAUP base
         case has NO ZF obligation. ***)
    REWRITE_TAC[ARITH_RULE `24 - 0 = 24`; ARITH_RULE `8 * 0 = 0`; WORD_ADD_0;
                CONJUNCT1 keccak; keccak4_pack] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_EQ_25]) THEN
    (* the LENGTH conjunction (from ASM_CASES) becomes one conjoined
       `A1=[..]/\../\A4=[..]` assumption; split it so the per-var SUBST fires. *)
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check(is_conj o concl))) THEN
    REPEAT(FIRST_X_ASSUM(fun th ->
       let l,r = dest_eq(concl th) in
       if is_var l && List.mem (fst(dest_var l)) ["A1";"A2";"A3";"A4"]
       then SUBST_ALL_TAC th else failwith "keep")) THEN
    REWRITE_TAC[MAP2; CONS_11] THEN
    CONV_TAC(TOP_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (bitstate_in,8 * 100)) s0` THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 0 6 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 200 6 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 400 6 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 600 6 THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN REPEAT STRIP_TAC THEN
    X86_STEPS_TAC SHA3_KECCAK4_F1600_AVX512VL_EXEC (1--79) THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[YMM0; YMM1; YMM2; YMM3; YMM4; YMM5; YMM6; YMM7; YMM8; YMM9; YMM10; YMM11; YMM12; YMM13; YMM14; YMM15; YMM16; YMM17; YMM18; YMM19; YMM20; YMM21; YMM22; YMM23; YMM24; READ_ZEROTOP_256] THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CONS_11]) THEN
    ASM_REWRITE_TAC[WORD_SUBWORD_JOIN_EXTRACT_64; WORD_SUBWORD_JOIN_EXTRACT_128;
                    MAP2; CONS_11] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN
    REPEAT CONJ_TAC THEN
    W(fun (_,w) -> ACCEPT_TAC(prove(w, BITBLAST_TAC)));

    (*** 3: preservation (0x243 -> 0x5f1) = ROUND_CORRECT (0x243->0x5ee) + dec
         (0x5ee->0x5f1). ***)
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      `read (memory :> bytes64 (word_add rc_pointer (word (8 * i))))
            (s:x86state) = EL i round_constants
       ==> T` (K ALL_TAC) THENL [MESON_TAC[]; ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x5ee`
     `\s. read RDI s = bitstate_in /\
          read RSI s = rc_pointer /\
          read R10 s = word (24 - i) /\
          read R11 s = word_add rc_pointer (word (8 * (i + 1))) /\
          wordlist_from_memory(rc_pointer,24) s = round_constants /\
          [read YMM0 s; read YMM1 s; read YMM2 s; read YMM3 s; read YMM4 s; read YMM5 s; read YMM6 s; read YMM7 s; read YMM8 s; read YMM9 s; read YMM10 s; read YMM11 s; read YMM12 s; read YMM13 s; read YMM14 s; read YMM15 s; read YMM16 s; read YMM17 s; read YMM18 s; read YMM19 s; read YMM20 s; read YMM21 s; read YMM22 s; read YMM23 s; read YMM24 s] =
            keccak4_pack (keccak (i+1) A1) (keccak (i+1) A2)
                         (keccak (i+1) A3) (keccak (i+1) A4)` THEN
    CONJ_TAC THENL
     [(* sub1: round body via ROUND_CORRECT *)
      REWRITE_TAC[keccak] THEN
      MATCH_MP_TAC ENSURES_PRECONDITION_THM_GEN THEN
      MAP_EVERY EXISTS_TAC
       [`\(s:x86state). bytes_loaded s (word pc) (BUTLAST sha3_keccak4_f1600_avx512vl_tmc) /\
             read RIP s = word (pc + 0x243) /\
             read RDI s = bitstate_in /\ read RSI s = rc_pointer /\
             read R10 s = word (24 - i) /\
             read R11 s = word_add rc_pointer (word (8 * i)) /\
             read (memory :> bytes64 (word_add rc_pointer (word (8 * i)))) s =
               EL i round_constants /\
             wordlist_from_memory(rc_pointer,24) s = round_constants /\
             [read YMM0 s; read YMM1 s; read YMM2 s; read YMM3 s; read YMM4 s; read YMM5 s; read YMM6 s; read YMM7 s; read YMM8 s; read YMM9 s; read YMM10 s; read YMM11 s; read YMM12 s; read YMM13 s; read YMM14 s; read YMM15 s; read YMM16 s; read YMM17 s; read YMM18 s; read YMM19 s; read YMM20 s; read YMM21 s; read YMM22 s; read YMM23 s; read YMM24 s] =
               keccak4_pack (keccak i A1) (keccak i A2) (keccak i A3) (keccak i A4)`;
        `MAYCHANGE [RIP; R11] ,,
         MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17; ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23; ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`] THEN
      REPEAT CONJ_TAC THENL
       [(* sg1: rc-at-r11 from wordlist via RC_AT_R11 *)
        X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`s:x86state`; `rc_pointer:int64`; `i:num`] RC_AT_R11) THEN
        ASM_REWRITE_TAC[];
        (* sg2: MAYCHANGE subsumption *)
        REWRITE_TAC[SOME_FLAGS] THEN
        CONV_TAC(REWR_CONV(GSYM subsumed)) THEN
        REWRITE_TAC[ETA_AX] THEN SUBSUMED_MAYCHANGE_TAC;
        (* sg3: ROUND_CORRECT instantiated *)
        REWRITE_TAC[WORD_RULE
          `word_add (rc_pointer:int64) (word (8 * (i + 1))) =
           word_add (word_add rc_pointer (word (8 * i))) (word 8)`] THEN
        MATCH_MP_TAC(ISPECL
          [`pc:num`; `(word_add rc_pointer (word (8 * i))):int64`;
           `(EL i round_constants):int64`;
           `keccak i A1`; `keccak i A2`; `keccak i A3`; `keccak i A4`;
           `bitstate_in:int64`; `rc_pointer:int64`; `(word (24 - i)):int64`]
          ROUND_CORRECT) THEN
        REPEAT CONJ_TAC THEN MATCH_MP_TAC LENGTH_KECCAK THEN ASM_REWRITE_TAC[]];

      (* sub2: dec 0x5ee->0x5f1 *)
      ENSURES_INIT_TAC "s0" THEN
      CONV_TAC(TOP_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
      X86_STEPS_TAC SHA3_KECCAK4_F1600_AVX512VL_EXEC (1--1) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `i < 24`)) THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST];

    (*** 4: backedge (0x5f1 -> 0x243): jne taken (ZF=F). ***)
    REPEAT STRIP_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `~(read ZF s0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    X86_STEPS_TAC SHA3_KECCAK4_F1600_AVX512VL_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** 5: tail (0x5f1 -> 0x834): i=24, jne NOT taken, epilogue. ***)
    ABBREV_TAC `B1 = keccak 24 A1` THEN
    ABBREV_TAC `B2 = keccak 24 A2` THEN
    ABBREV_TAC `B3 = keccak 24 A3` THEN
    ABBREV_TAC `B4 = keccak 24 A4` THEN
    SUBGOAL_THEN
      `LENGTH(B1:int64 list)=25 /\ LENGTH(B2:int64 list)=25 /\
       LENGTH(B3:int64 list)=25 /\ LENGTH(B4:int64 list)=25`
      STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["B1";"B2";"B3";"B4"] THEN
      ASM_MESON_TAC[LENGTH_KECCAK]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_EQ_25]) THEN
    REPEAT(FIRST_X_ASSUM(fun th ->
       let l,r = dest_eq(concl th) in
       if is_var l && List.mem (fst(dest_var l)) ["B1";"B2";"B3";"B4"]
       then SUBST_ALL_TAC th else failwith "keep")) THEN
    REWRITE_TAC[keccak4_pack] THEN
    REWRITE_TAC[MAP2; CONS_11] THEN
    REWRITE_TAC[YMM0; YMM1; YMM2; YMM3; YMM4; YMM5; YMM6; YMM7; YMM8; YMM9; YMM10; YMM11; YMM12; YMM13; YMM14; YMM15; YMM16; YMM17; YMM18; YMM19; YMM20; YMM21; YMM22; YMM23; YMM24; READ_ZEROTOP_256] THEN
    GHOST_INTRO_TAC `zg0:int512` `read ZMM0` THEN
    GHOST_INTRO_TAC `zg1:int512` `read ZMM1` THEN
    GHOST_INTRO_TAC `zg2:int512` `read ZMM2` THEN
    GHOST_INTRO_TAC `zg3:int512` `read ZMM3` THEN
    GHOST_INTRO_TAC `zg4:int512` `read ZMM4` THEN
    GHOST_INTRO_TAC `zg5:int512` `read ZMM5` THEN
    GHOST_INTRO_TAC `zg6:int512` `read ZMM6` THEN
    GHOST_INTRO_TAC `zg7:int512` `read ZMM7` THEN
    GHOST_INTRO_TAC `zg8:int512` `read ZMM8` THEN
    GHOST_INTRO_TAC `zg9:int512` `read ZMM9` THEN
    GHOST_INTRO_TAC `zg10:int512` `read ZMM10` THEN
    GHOST_INTRO_TAC `zg11:int512` `read ZMM11` THEN
    GHOST_INTRO_TAC `zg12:int512` `read ZMM12` THEN
    GHOST_INTRO_TAC `zg13:int512` `read ZMM13` THEN
    GHOST_INTRO_TAC `zg14:int512` `read ZMM14` THEN
    GHOST_INTRO_TAC `zg15:int512` `read ZMM15` THEN
    GHOST_INTRO_TAC `zg16:int512` `read ZMM16` THEN
    GHOST_INTRO_TAC `zg17:int512` `read ZMM17` THEN
    GHOST_INTRO_TAC `zg18:int512` `read ZMM18` THEN
    GHOST_INTRO_TAC `zg19:int512` `read ZMM19` THEN
    GHOST_INTRO_TAC `zg20:int512` `read ZMM20` THEN
    GHOST_INTRO_TAC `zg21:int512` `read ZMM21` THEN
    GHOST_INTRO_TAC `zg22:int512` `read ZMM22` THEN
    GHOST_INTRO_TAC `zg23:int512` `read ZMM23` THEN
    GHOST_INTRO_TAC `zg24:int512` `read ZMM24` THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC SHA3_KECCAK4_F1600_AVX512VL_EXEC (1--79) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ENSURES_FINAL_STATE_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[WORD_SUBWORD_JOIN_EXTRACT_64; WORD_SUBWORD_JOIN_EXTRACT_128;
                    MAP2; CONS_11] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN
    REPEAT CONJ_TAC THEN
    W(fun (_,w) -> ACCEPT_TAC(prove(w, BITBLAST_TAC)))]);;

(* ------------------------------------------------------------------------- *)
(* SysV ABI subroutine wrappers (register-resident kernel: no stack scratch,  *)
(* no internal call -> the simple NOSTACK promotion + IBT prefix).            *)
(* ------------------------------------------------------------------------- *)

(* So X86_PROMOTE_RETURN_NOSTACK_TAC's state-update propagation sees through
   wordlist_from_memory across the final `ret`.  Saved/restored so loading this
   file does not perturb simulation_precanon_thms for anything loaded after. *)
let sha3_keccak4_f1600_avx512vl_saved_precanon = !simulation_precanon_thms;;
simulation_precanon_thms := union [WORDLIST_FROM_MEMORY] (!simulation_precanon_thms);;

let SHA3_KECCAK4_F1600_AVX512VL_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!rc_pointer:int64 bitstate_in:int64 A1 A2 A3 A4 pc stackpointer returnaddress.
     nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_tmc) (bitstate_in, 800) /\
     nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_tmc) (rc_pointer, 192) /\
     nonoverlapping (bitstate_in, 800) (rc_pointer, 192) /\
     nonoverlapping (stackpointer, 8) (bitstate_in, 800)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_avx512vl_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [bitstate_in; rc_pointer] s /\
               wordlist_from_memory(rc_pointer,24) s = round_constants /\
               wordlist_from_memory(bitstate_in,25) s = A1 /\
               wordlist_from_memory(word_add bitstate_in (word 200),25) s = A2 /\
               wordlist_from_memory(word_add bitstate_in (word 400),25) s = A3 /\
               wordlist_from_memory(word_add bitstate_in (word 600),25) s = A4)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               wordlist_from_memory(bitstate_in,25) s = keccak 24 A1 /\
               wordlist_from_memory(word_add bitstate_in (word 200),25) s = keccak 24 A2 /\
               wordlist_from_memory(word_add bitstate_in (word 400),25) s = keccak 24 A3 /\
               wordlist_from_memory(word_add bitstate_in (word 600),25) s = keccak 24 A4)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes (bitstate_in, 800)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC sha3_keccak4_f1600_avx512vl_tmc
    SHA3_KECCAK4_F1600_AVX512VL_CORRECT);;

let SHA3_KECCAK4_F1600_AVX512VL_SUBROUTINE_CORRECT = time prove
 (`!rc_pointer:int64 bitstate_in:int64 A1 A2 A3 A4 pc stackpointer returnaddress.
     nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_mc) (bitstate_in, 800) /\
     nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_mc) (rc_pointer, 192) /\
     nonoverlapping (bitstate_in, 800) (rc_pointer, 192) /\
     nonoverlapping (stackpointer, 8) (bitstate_in, 800)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_avx512vl_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [bitstate_in; rc_pointer] s /\
               wordlist_from_memory(rc_pointer,24) s = round_constants /\
               wordlist_from_memory(bitstate_in,25) s = A1 /\
               wordlist_from_memory(word_add bitstate_in (word 200),25) s = A2 /\
               wordlist_from_memory(word_add bitstate_in (word 400),25) s = A3 /\
               wordlist_from_memory(word_add bitstate_in (word 600),25) s = A4)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               wordlist_from_memory(bitstate_in,25) s = keccak 24 A1 /\
               wordlist_from_memory(word_add bitstate_in (word 200),25) s = keccak 24 A2 /\
               wordlist_from_memory(word_add bitstate_in (word 400),25) s = keccak 24 A3 /\
               wordlist_from_memory(word_add bitstate_in (word 600),25) s = keccak 24 A4)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes (bitstate_in, 800)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE SHA3_KECCAK4_F1600_AVX512VL_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Windows ABI subroutine wrappers. The Windows object is built from the same *)
(* .S with -DWINDOWS_ABI=1: it prepends an endbr + a spill of the callee-saved *)
(* XMM6-15/RDI/RSI and shuffles the Microsoft args (RCX,RDX) into the SysV     *)
(* registers (RDI,RSI) the register-resident body expects, then a mirror       *)
(* restore + ret. The core body sits at offset 92 in the trimmed Windows       *)
(* object and is reused (no re-proof) via BYTES_LOADED_SUBPROGRAM_RULE.         *)
(* ------------------------------------------------------------------------- *)

let sha3_keccak4_f1600_avx512vl_windows_mc = define_from_elf
  "sha3_keccak4_f1600_avx512vl_windows_mc" "x86/sha3/sha3_keccak4_f1600_avx512vl.obj";;

let sha3_keccak4_f1600_avx512vl_windows_tmc =
  define_trimmed "sha3_keccak4_f1600_avx512vl_windows_tmc"
                 sha3_keccak4_f1600_avx512vl_windows_mc;;

let sha3_keccak4_f1600_avx512vl_windows_tmc_EXEC =
  X86_MK_EXEC_RULE sha3_keccak4_f1600_avx512vl_windows_tmc;;

let SHA3_KECCAK4_F1600_AVX512VL_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!rc_pointer:int64 bitstate_in:int64 A1 A2 A3 A4 pc:num stackpointer:int64 returnaddress.
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_tmc) (val (word_sub stackpointer (word 0xb0)), 0xb0) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_tmc) (val bitstate_in, 800) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_tmc) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in, 800) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in, 800) (val (word_sub stackpointer (word 0xb0)), 0xb0 + 8) /\
  nonoverlapping_modulo (2 EXP 64) (val (word_sub stackpointer (word 0xb0)), 0xb0) (val rc_pointer, 192)
  ==> ensures x86
         (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_avx512vl_windows_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS[bitstate_in; rc_pointer] s /\
              wordlist_from_memory(rc_pointer, 24) s = round_constants /\
              wordlist_from_memory(bitstate_in, 25) s = A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200), 25) s = A2 /\
              wordlist_from_memory(word_add bitstate_in (word 400), 25) s = A3 /\
              wordlist_from_memory(word_add bitstate_in (word 600), 25) s = A4)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              wordlist_from_memory(bitstate_in, 25) s = keccak 24 A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200), 25) s = keccak 24 A2 /\
              wordlist_from_memory(word_add bitstate_in (word 400), 25) s = keccak 24 A3 /\
              wordlist_from_memory(word_add bitstate_in (word 600), 25) s = keccak 24 A4)
         (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes (bitstate_in, 800);
                     memory :> bytes(word_sub stackpointer (word 0xb0), 0xb0)])`,
  REPLICATE_TAC 7 GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  WORD_FORALL_OFFSET_TAC 0xb0 THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fst sha3_keccak4_f1600_avx512vl_windows_tmc_EXEC] THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[ALL; WINDOWS_C_ARGUMENTS] THEN
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

  REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER] THEN
  GHOST_INTRO_TAC `init_zmm6:int512` `read ZMM6` THEN
  GHOST_INTRO_TAC `init_zmm7:int512` `read ZMM7` THEN
  GHOST_INTRO_TAC `init_zmm8:int512` `read ZMM8` THEN
  GHOST_INTRO_TAC `init_zmm9:int512` `read ZMM9` THEN
  GHOST_INTRO_TAC `init_zmm10:int512` `read ZMM10` THEN
  GHOST_INTRO_TAC `init_zmm11:int512` `read ZMM11` THEN
  GHOST_INTRO_TAC `init_zmm12:int512` `read ZMM12` THEN
  GHOST_INTRO_TAC `init_zmm13:int512` `read ZMM13` THEN
  GHOST_INTRO_TAC `init_zmm14:int512` `read ZMM14` THEN
  GHOST_INTRO_TAC `init_zmm15:int512` `read ZMM15` THEN

  GLOBALIZE_PRECONDITION_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN

  REWRITE_TAC[fst sha3_keccak4_f1600_avx512vl_windows_tmc_EXEC] THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY; DIMINDEX_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC sha3_keccak4_f1600_avx512vl_windows_tmc_EXEC (1--15) THEN

  MP_TAC(SPECL
   [`rc_pointer:int64`; `bitstate_in:int64`;
    `A1:int64 list`; `A2:int64 list`; `A3:int64 list`; `A4:int64 list`;
    `pc + 92`]
   SHA3_KECCAK4_F1600_AVX512VL_CORRECT) THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN REWRITE_TAC[ALL] THEN
  ANTS_TAC THENL [REPEAT NONOVERLAPPING_TAC; ALL_TAC] THEN

  REWRITE_TAC[WORDLIST_FROM_MEMORY; DIMINDEX_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN

  (* X86_BIGSTEP leaves exactly 2 goals here (bytes_loaded subprogram ; main
     eventually), so this is a 2-branch THENL. *)
  X86_BIGSTEP_TAC sha3_keccak4_f1600_avx512vl_windows_tmc_EXEC "s16" THENL
  [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
   (BYTES_LOADED_SUBPROGRAM_RULE sha3_keccak4_f1600_avx512vl_windows_tmc
   (REWRITE_RULE[BUTLAST_CLAUSES]
    (AP_TERM `BUTLAST:byte list->byte list` sha3_keccak4_f1600_avx512vl_tmc))
   92));
   RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN

  REWRITE_TAC[WORDLIST_FROM_MEMORY; DIMINDEX_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN

  MAP_EVERY ABBREV_TAC
   [`zmm6_epilog = read ZMM6 s16`;
    `zmm7_epilog = read ZMM7 s16`;
    `zmm8_epilog = read ZMM8 s16`;
    `zmm9_epilog = read ZMM9 s16`;
    `zmm10_epilog = read ZMM10 s16`;
    `zmm11_epilog = read ZMM11 s16`;
    `zmm12_epilog = read ZMM12 s16`;
    `zmm13_epilog = read ZMM13 s16`;
    `zmm14_epilog = read ZMM14 s16`;
    `zmm15_epilog = read ZMM15 s16`] THEN

  X86_STEPS_TAC sha3_keccak4_f1600_avx512vl_windows_tmc_EXEC (17--30) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let SHA3_KECCAK4_F1600_AVX512VL_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!rc_pointer:int64 bitstate_in:int64 A1 A2 A3 A4 pc:num stackpointer:int64 returnaddress.
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_mc) (val (word_sub stackpointer (word 0xb0)), 0xb0) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_mc) (val bitstate_in, 800) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_mc) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in, 800) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in, 800) (val (word_sub stackpointer (word 0xb0)), 0xb0 + 8) /\
  nonoverlapping_modulo (2 EXP 64) (val (word_sub stackpointer (word 0xb0)), 0xb0) (val rc_pointer, 192)
  ==> ensures x86
         (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_avx512vl_windows_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS[bitstate_in; rc_pointer] s /\
              wordlist_from_memory(rc_pointer, 24) s = round_constants /\
              wordlist_from_memory(bitstate_in, 25) s = A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200), 25) s = A2 /\
              wordlist_from_memory(word_add bitstate_in (word 400), 25) s = A3 /\
              wordlist_from_memory(word_add bitstate_in (word 600), 25) s = A4)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              wordlist_from_memory(bitstate_in, 25) s = keccak 24 A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200), 25) s = keccak 24 A2 /\
              wordlist_from_memory(word_add bitstate_in (word 400), 25) s = keccak 24 A3 /\
              wordlist_from_memory(word_add bitstate_in (word 600), 25) s = keccak 24 A4)
         (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes (bitstate_in, 800);
                     memory :> bytes(word_sub stackpointer (word 0xb0), 0xb0)])`,
 let TWEAK_CONV = ONCE_DEPTH_CONV NUM_ADD_CONV THENC
                   ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
    (CONV_RULE TWEAK_CONV SHA3_KECCAK4_F1600_AVX512VL_NOIBT_WINDOWS_SUBROUTINE_CORRECT)));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(*                                                                           *)
(* The kernel is register-resident with no data-dependent control flow or    *)
(* memory addressing, so the memory-safety property is proven directly from  *)
(* the correctness spec.  (Kept before the simulation_precanon_thms restore  *)
(* below so WORDLIST_FROM_MEMORY remains active for the NOSTACK promotion.)   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "sha3_keccak4_f1600_avx512vl" subroutine_signatures)
    (REWRITE_RULE[SOME_FLAGS] SHA3_KECCAK4_F1600_AVX512VL_CORRECT)
    SHA3_KECCAK4_F1600_AVX512VL_EXEC;;

let SHA3_KECCAK4_F1600_AVX512VL_SAFE = time prove
 (`exists f_events.
    forall e rc_pointer bitstate_in pc.
        nonoverlapping (word pc,2101) (bitstate_in,800) /\
        nonoverlapping (word pc,2101) (rc_pointer,192) /\
        nonoverlapping (bitstate_in,800) (rc_pointer,192)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc)
                 (BUTLAST sha3_keccak4_f1600_avx512vl_tmc) /\
                 read RIP s = word pc /\
                 C_ARGUMENTS [bitstate_in; rc_pointer] s /\
                 read events s = e)
            (\s.
                 read RIP s = word (pc + 2100) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc_pointer bitstate_in pc /\
                      memaccess_inbounds e2 [bitstate_in,800; rc_pointer,192]
                      [bitstate_in,800]))
            (MAYCHANGE [RIP; R10; R11] ,,
             MAYCHANGE
             [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9;
              ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17; ZMM18;
              ZMM19; ZMM20; ZMM21; ZMM22; ZMM23; ZMM24; ZMM25; ZMM26; ZMM27;
              ZMM28; ZMM29; ZMM30; ZMM31] ,,
             MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes (bitstate_in,800)])`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars SHA3_KECCAK4_F1600_AVX512VL_EXEC);;

let SHA3_KECCAK4_F1600_AVX512VL_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e rc_pointer:int64 bitstate_in:int64 pc stackpointer returnaddress.
          nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_tmc) (bitstate_in, 800) /\
          nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_tmc) (rc_pointer, 192) /\
          nonoverlapping (bitstate_in, 800) (rc_pointer, 192) /\
          nonoverlapping (stackpointer, 8) (bitstate_in, 800)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) sha3_keccak4_f1600_avx512vl_tmc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [bitstate_in; rc_pointer] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events rc_pointer bitstate_in pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                           [bitstate_in,800; rc_pointer,192; stackpointer,8]
                           [bitstate_in,800; stackpointer,8]))
               (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC sha3_keccak4_f1600_avx512vl_tmc
    SHA3_KECCAK4_F1600_AVX512VL_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let SHA3_KECCAK4_F1600_AVX512VL_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e rc_pointer:int64 bitstate_in:int64 pc stackpointer returnaddress.
          nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_mc) (bitstate_in, 800) /\
          nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_mc) (rc_pointer, 192) /\
          nonoverlapping (bitstate_in, 800) (rc_pointer, 192) /\
          nonoverlapping (stackpointer, 8) (bitstate_in, 800)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) sha3_keccak4_f1600_avx512vl_mc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [bitstate_in; rc_pointer] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events rc_pointer bitstate_in pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                           [bitstate_in,800; rc_pointer,192; stackpointer,8]
                           [bitstate_in,800; stackpointer,8]))
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE SHA3_KECCAK4_F1600_AVX512VL_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof of Windows ABI version.             *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK4_F1600_AVX512VL_NOIBT_WINDOWS_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e rc_pointer:int64 bitstate_in:int64 pc:num stackpointer:int64 returnaddress.
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_tmc) (val (word_sub stackpointer (word 0xb0)), 0xb0) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_tmc) (val bitstate_in, 800) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_tmc) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in, 800) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in, 800) (val (word_sub stackpointer (word 0xb0)), 0xb0 + 8) /\
  nonoverlapping_modulo (2 EXP 64) (val (word_sub stackpointer (word 0xb0)), 0xb0) (val rc_pointer, 192)
  ==> ensures x86
         (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_avx512vl_windows_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS[bitstate_in; rc_pointer] s /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events rc_pointer bitstate_in pc (word_sub stackpointer (word 0xb0)) returnaddress /\
                    memaccess_inbounds e2
                      [bitstate_in,800; rc_pointer,192;
                       word_sub stackpointer (word 0xb0),0xb0 + 8]
                      [bitstate_in,800; word_sub stackpointer (word 0xb0),0xb0]))
         (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes (bitstate_in, 800);
                     memory :> bytes(word_sub stackpointer (word 0xb0), 0xb0)])`,
  ASSUME_CALLEE_SAFETY_TAC SHA3_KECCAK4_F1600_AVX512VL_SAFE "H_subth" THEN
  META_EXISTS_TAC THEN
  REPLICATE_TAC 4 GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  WORD_FORALL_OFFSET_TAC 0xb0 THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fst sha3_keccak4_f1600_avx512vl_windows_tmc_EXEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[ALL; WINDOWS_C_ARGUMENTS] THEN
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

  REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER] THEN
  GHOST_INTRO_TAC `init_zmm6:int512` `read ZMM6` THEN
  GHOST_INTRO_TAC `init_zmm7:int512` `read ZMM7` THEN
  GHOST_INTRO_TAC `init_zmm8:int512` `read ZMM8` THEN
  GHOST_INTRO_TAC `init_zmm9:int512` `read ZMM9` THEN
  GHOST_INTRO_TAC `init_zmm10:int512` `read ZMM10` THEN
  GHOST_INTRO_TAC `init_zmm11:int512` `read ZMM11` THEN
  GHOST_INTRO_TAC `init_zmm12:int512` `read ZMM12` THEN
  GHOST_INTRO_TAC `init_zmm13:int512` `read ZMM13` THEN
  GHOST_INTRO_TAC `init_zmm14:int512` `read ZMM14` THEN
  GHOST_INTRO_TAC `init_zmm15:int512` `read ZMM15` THEN

  GLOBALIZE_PRECONDITION_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN

  REWRITE_TAC[fst sha3_keccak4_f1600_avx512vl_windows_tmc_EXEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC sha3_keccak4_f1600_avx512vl_windows_tmc_EXEC (1--15) THEN

  W(fun (asl,w) ->
    let current_events = filter_map (fun (_,ath) -> let t = concl ath in
      if is_eq t && is_read_events (lhs t) then Some (rhs t)
      else None) asl in
    if length current_events <> 1
    then failwith "More than 'read events .. = ..?'"
    else
      REMOVE_THEN "H_subth"
        (MP_TAC o SPECL [hd current_events; `rc_pointer:int64`; `bitstate_in:int64`;
                         `pc + 92`]))
  THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; ALL] THEN
  ANTS_TAC THENL [REPEAT NONOVERLAPPING_TAC; ALL_TAC] THEN

  X86_BIGSTEP_TAC sha3_keccak4_f1600_avx512vl_windows_tmc_EXEC "s16" THENL
  [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
   (BYTES_LOADED_SUBPROGRAM_RULE sha3_keccak4_f1600_avx512vl_windows_tmc
   (REWRITE_RULE[BUTLAST_CLAUSES]
    (AP_TERM `BUTLAST:byte list->byte list` sha3_keccak4_f1600_avx512vl_tmc))
   92));
   RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN

  MAP_EVERY ABBREV_TAC
   [`zmm6_epilog = read ZMM6 s16`;
    `zmm7_epilog = read ZMM7 s16`;
    `zmm8_epilog = read ZMM8 s16`;
    `zmm9_epilog = read ZMM9 s16`;
    `zmm10_epilog = read ZMM10 s16`;
    `zmm11_epilog = read ZMM11 s16`;
    `zmm12_epilog = read ZMM12 s16`;
    `zmm13_epilog = read ZMM13 s16`;
    `zmm14_epilog = read ZMM14 s16`;
    `zmm15_epilog = read ZMM15 s16`] THEN

  X86_STEPS_TAC sha3_keccak4_f1600_avx512vl_windows_tmc_EXEC (17--30) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ DISCHARGE_SAFETY_PROPERTY_TAC; ALL_TAC ] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let SHA3_KECCAK4_F1600_AVX512VL_WINDOWS_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e rc_pointer:int64 bitstate_in:int64 pc:num stackpointer:int64 returnaddress.
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_mc) (val (word_sub stackpointer (word 0xb0)), 0xb0) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_mc) (val bitstate_in, 800) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_mc) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in, 800) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in, 800) (val (word_sub stackpointer (word 0xb0)), 0xb0 + 8) /\
  nonoverlapping_modulo (2 EXP 64) (val (word_sub stackpointer (word 0xb0)), 0xb0) (val rc_pointer, 192)
  ==> ensures x86
         (\s. bytes_loaded s (word pc) sha3_keccak4_f1600_avx512vl_windows_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS[bitstate_in; rc_pointer] s /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events rc_pointer bitstate_in pc (word_sub stackpointer (word 0xb0)) returnaddress /\
                    memaccess_inbounds e2
                      [bitstate_in,800; rc_pointer,192;
                       word_sub stackpointer (word 0xb0),0xb0 + 8]
                      [bitstate_in,800; word_sub stackpointer (word 0xb0),0xb0]))
         (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes (bitstate_in, 800);
                     memory :> bytes(word_sub stackpointer (word 0xb0), 0xb0)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE SHA3_KECCAK4_F1600_AVX512VL_NOIBT_WINDOWS_SUBROUTINE_SAFE));;

simulation_precanon_thms := sha3_keccak4_f1600_avx512vl_saved_precanon;;

