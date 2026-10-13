(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/keccak_spec.ml";;

(**** print_literal_from_elf "x86/sha3/sha3_keccak8_f1600_avx512.o";;
****)

let sha3_keccak8_f1600_avx512_mc = define_assert_from_elf
  "sha3_keccak8_f1600_avx512_mc" "x86/sha3/sha3_keccak8_f1600_avx512.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x62; 0xf1; 0xfe; 0x48; 0x6f; 0x07;
                           (* VMOVDQU64 (%_% zmm0) (Memop Word512 (%% (rdi,0))) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x48; 0x6f; 0x8f; 0xc8; 0x00; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm1) (Memop Word512 (%% (rdi,200)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x48; 0x6f; 0x97; 0x90; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm2) (Memop Word512 (%% (rdi,400)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x48; 0x6f; 0x9f; 0x58; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm3) (Memop Word512 (%% (rdi,600)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x48; 0x6f; 0xa7; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm4) (Memop Word512 (%% (rdi,800)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x48; 0x6f; 0xaf; 0xe8; 0x03; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm5) (Memop Word512 (%% (rdi,1000)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x48; 0x6f; 0xb7; 0xb0; 0x04; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm6) (Memop Word512 (%% (rdi,1200)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x48; 0x6f; 0xbf; 0x78; 0x05; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm7) (Memop Word512 (%% (rdi,1400)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x48; 0x6d; 0xc9;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm0) (%_% zmm1) *)
  0x62; 0xf1; 0xfd; 0x48; 0x6c; 0xc1;
                           (* VPUNPCKLQDQ (%_% zmm0) (%_% zmm0) (%_% zmm1) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xc9;
                           (* VMOVDQA64 (%_% zmm1) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xed; 0x48; 0x6d; 0xcb;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm2) (%_% zmm3) *)
  0x62; 0xf1; 0xed; 0x48; 0x6c; 0xd3;
                           (* VPUNPCKLQDQ (%_% zmm2) (%_% zmm2) (%_% zmm3) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xd9;
                           (* VMOVDQA64 (%_% zmm3) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xdd; 0x48; 0x6d; 0xcd;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm4) (%_% zmm5) *)
  0x62; 0xf1; 0xdd; 0x48; 0x6c; 0xe5;
                           (* VPUNPCKLQDQ (%_% zmm4) (%_% zmm4) (%_% zmm5) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xe9;
                           (* VMOVDQA64 (%_% zmm5) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xcd; 0x48; 0x6d; 0xcf;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm6) (%_% zmm7) *)
  0x62; 0xf1; 0xcd; 0x48; 0x6c; 0xf7;
                           (* VPUNPCKLQDQ (%_% zmm6) (%_% zmm6) (%_% zmm7) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm7) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xfd; 0x48; 0x43; 0xca; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm0) (%_% zmm2) (Imm8 (word 221)) *)
  0x62; 0xf3; 0xfd; 0x48; 0x43; 0xc2; 0x88;
                           (* VSHUFI64X2 (%_% zmm0) (%_% zmm0) (%_% zmm2) (Imm8 (word 136)) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xd1;
                           (* VMOVDQA64 (%_% zmm2) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xf5; 0x48; 0x43; 0xcb; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm1) (%_% zmm3) (Imm8 (word 221)) *)
  0x62; 0xf3; 0xf5; 0x48; 0x43; 0xcb; 0x88;
                           (* VSHUFI64X2 (%_% zmm1) (%_% zmm1) (%_% zmm3) (Imm8 (word 136)) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xd9;
                           (* VMOVDQA64 (%_% zmm3) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xdd; 0x48; 0x43; 0xce; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm4) (%_% zmm6) (Imm8 (word 221)) *)
  0x62; 0xf3; 0xdd; 0x48; 0x43; 0xe6; 0x88;
                           (* VSHUFI64X2 (%_% zmm4) (%_% zmm4) (%_% zmm6) (Imm8 (word 136)) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% zmm6) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xd5; 0x48; 0x43; 0xcf; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm5) (%_% zmm7) (Imm8 (word 221)) *)
  0x62; 0xf3; 0xd5; 0x48; 0x43; 0xef; 0x88;
                           (* VSHUFI64X2 (%_% zmm5) (%_% zmm5) (%_% zmm7) (Imm8 (word 136)) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm7) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xfd; 0x48; 0x43; 0xcc; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm0) (%_% zmm4) (Imm8 (word 221)) *)
  0x62; 0xf3; 0xfd; 0x48; 0x43; 0xc4; 0x88;
                           (* VSHUFI64X2 (%_% zmm0) (%_% zmm0) (%_% zmm4) (Imm8 (word 136)) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xe1;
                           (* VMOVDQA64 (%_% zmm4) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xf5; 0x48; 0x43; 0xcd; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm1) (%_% zmm5) (Imm8 (word 221)) *)
  0x62; 0xf3; 0xf5; 0x48; 0x43; 0xcd; 0x88;
                           (* VSHUFI64X2 (%_% zmm1) (%_% zmm1) (%_% zmm5) (Imm8 (word 136)) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xe9;
                           (* VMOVDQA64 (%_% zmm5) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xed; 0x48; 0x43; 0xce; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm2) (%_% zmm6) (Imm8 (word 221)) *)
  0x62; 0xf3; 0xed; 0x48; 0x43; 0xd6; 0x88;
                           (* VSHUFI64X2 (%_% zmm2) (%_% zmm2) (%_% zmm6) (Imm8 (word 136)) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% zmm6) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xe5; 0x48; 0x43; 0xcf; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm3) (%_% zmm7) (Imm8 (word 221)) *)
  0x62; 0xf3; 0xe5; 0x48; 0x43; 0xdf; 0x88;
                           (* VSHUFI64X2 (%_% zmm3) (%_% zmm3) (%_% zmm7) (Imm8 (word 136)) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm7) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x48; 0x6f; 0x47; 0x01;
                           (* VMOVDQU64 (%_% zmm8) (Memop Word512 (%% (rdi,64)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x48; 0x6f; 0x8f; 0x08; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm9) (Memop Word512 (%% (rdi,264)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x48; 0x6f; 0x97; 0xd0; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm10) (Memop Word512 (%% (rdi,464)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x48; 0x6f; 0x9f; 0x98; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm11) (Memop Word512 (%% (rdi,664)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x48; 0x6f; 0xa7; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm12) (Memop Word512 (%% (rdi,864)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x48; 0x6f; 0xaf; 0x28; 0x04; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm13) (Memop Word512 (%% (rdi,1064)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x48; 0x6f; 0xb7; 0xf0; 0x04; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm14) (Memop Word512 (%% (rdi,1264)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x48; 0x6f; 0xbf; 0xb8; 0x05; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm15) (Memop Word512 (%% (rdi,1464)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xbd; 0x48; 0x6d; 0xc9;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm8) (%_% zmm9) *)
  0x62; 0x51; 0xbd; 0x48; 0x6c; 0xc1;
                           (* VPUNPCKLQDQ (%_% zmm8) (%_% zmm8) (%_% zmm9) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xc9;
                           (* VMOVDQA64 (%_% zmm9) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xad; 0x48; 0x6d; 0xcb;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm10) (%_% zmm11) *)
  0x62; 0x51; 0xad; 0x48; 0x6c; 0xd3;
                           (* VPUNPCKLQDQ (%_% zmm10) (%_% zmm10) (%_% zmm11) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xd9;
                           (* VMOVDQA64 (%_% zmm11) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0x9d; 0x48; 0x6d; 0xcd;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm12) (%_% zmm13) *)
  0x62; 0x51; 0x9d; 0x48; 0x6c; 0xe5;
                           (* VPUNPCKLQDQ (%_% zmm12) (%_% zmm12) (%_% zmm13) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xe9;
                           (* VMOVDQA64 (%_% zmm13) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0x8d; 0x48; 0x6d; 0xcf;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm14) (%_% zmm15) *)
  0x62; 0x51; 0x8d; 0x48; 0x6c; 0xf7;
                           (* VPUNPCKLQDQ (%_% zmm14) (%_% zmm14) (%_% zmm15) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm15) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xbd; 0x48; 0x43; 0xca; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm8) (%_% zmm10) (Imm8 (word 221)) *)
  0x62; 0x53; 0xbd; 0x48; 0x43; 0xc2; 0x88;
                           (* VSHUFI64X2 (%_% zmm8) (%_% zmm8) (%_% zmm10) (Imm8 (word 136)) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xd1;
                           (* VMOVDQA64 (%_% zmm10) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xb5; 0x48; 0x43; 0xcb; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm9) (%_% zmm11) (Imm8 (word 221)) *)
  0x62; 0x53; 0xb5; 0x48; 0x43; 0xcb; 0x88;
                           (* VSHUFI64X2 (%_% zmm9) (%_% zmm9) (%_% zmm11) (Imm8 (word 136)) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xd9;
                           (* VMOVDQA64 (%_% zmm11) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0x9d; 0x48; 0x43; 0xce; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm12) (%_% zmm14) (Imm8 (word 221)) *)
  0x62; 0x53; 0x9d; 0x48; 0x43; 0xe6; 0x88;
                           (* VSHUFI64X2 (%_% zmm12) (%_% zmm12) (%_% zmm14) (Imm8 (word 136)) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% zmm14) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0x95; 0x48; 0x43; 0xcf; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm13) (%_% zmm15) (Imm8 (word 221)) *)
  0x62; 0x53; 0x95; 0x48; 0x43; 0xef; 0x88;
                           (* VSHUFI64X2 (%_% zmm13) (%_% zmm13) (%_% zmm15) (Imm8 (word 136)) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm15) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xbd; 0x48; 0x43; 0xcc; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm8) (%_% zmm12) (Imm8 (word 221)) *)
  0x62; 0x53; 0xbd; 0x48; 0x43; 0xc4; 0x88;
                           (* VSHUFI64X2 (%_% zmm8) (%_% zmm8) (%_% zmm12) (Imm8 (word 136)) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xe1;
                           (* VMOVDQA64 (%_% zmm12) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xb5; 0x48; 0x43; 0xcd; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm9) (%_% zmm13) (Imm8 (word 221)) *)
  0x62; 0x53; 0xb5; 0x48; 0x43; 0xcd; 0x88;
                           (* VSHUFI64X2 (%_% zmm9) (%_% zmm9) (%_% zmm13) (Imm8 (word 136)) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xe9;
                           (* VMOVDQA64 (%_% zmm13) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xad; 0x48; 0x43; 0xce; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm10) (%_% zmm14) (Imm8 (word 221)) *)
  0x62; 0x53; 0xad; 0x48; 0x43; 0xd6; 0x88;
                           (* VSHUFI64X2 (%_% zmm10) (%_% zmm10) (%_% zmm14) (Imm8 (word 136)) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% zmm14) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xa5; 0x48; 0x43; 0xcf; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm11) (%_% zmm15) (Imm8 (word 221)) *)
  0x62; 0x53; 0xa5; 0x48; 0x43; 0xdf; 0x88;
                           (* VSHUFI64X2 (%_% zmm11) (%_% zmm11) (%_% zmm15) (Imm8 (word 136)) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm15) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x48; 0x6f; 0x47; 0x02;
                           (* VMOVDQU64 (%_% zmm16) (Memop Word512 (%% (rdi,128)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x48; 0x6f; 0x8f; 0x48; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm17) (Memop Word512 (%% (rdi,328)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x48; 0x6f; 0x97; 0x10; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm18) (Memop Word512 (%% (rdi,528)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x48; 0x6f; 0x9f; 0xd8; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm19) (Memop Word512 (%% (rdi,728)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x48; 0x6f; 0xa7; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm20) (Memop Word512 (%% (rdi,928)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x48; 0x6f; 0xaf; 0x68; 0x04; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm21) (Memop Word512 (%% (rdi,1128)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x48; 0x6f; 0xb7; 0x30; 0x05; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm22) (Memop Word512 (%% (rdi,1328)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x48; 0x6f; 0xbf; 0xf8; 0x05; 0x00; 0x00;
                           (* VMOVDQU64 (%_% zmm23) (Memop Word512 (%% (rdi,1528)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x40; 0x6d; 0xc9;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm16) (%_% zmm17) *)
  0x62; 0xa1; 0xfd; 0x40; 0x6c; 0xc1;
                           (* VPUNPCKLQDQ (%_% zmm16) (%_% zmm16) (%_% zmm17) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xc9;
                           (* VMOVDQA64 (%_% zmm17) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xed; 0x40; 0x6d; 0xcb;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm18) (%_% zmm19) *)
  0x62; 0xa1; 0xed; 0x40; 0x6c; 0xd3;
                           (* VPUNPCKLQDQ (%_% zmm18) (%_% zmm18) (%_% zmm19) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xd9;
                           (* VMOVDQA64 (%_% zmm19) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xdd; 0x40; 0x6d; 0xcd;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm20) (%_% zmm21) *)
  0x62; 0xa1; 0xdd; 0x40; 0x6c; 0xe5;
                           (* VPUNPCKLQDQ (%_% zmm20) (%_% zmm20) (%_% zmm21) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xe9;
                           (* VMOVDQA64 (%_% zmm21) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xcd; 0x40; 0x6d; 0xcf;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm22) (%_% zmm23) *)
  0x62; 0xa1; 0xcd; 0x40; 0x6c; 0xf7;
                           (* VPUNPCKLQDQ (%_% zmm22) (%_% zmm22) (%_% zmm23) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm23) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xfd; 0x40; 0x43; 0xca; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm16) (%_% zmm18) (Imm8 (word 221)) *)
  0x62; 0xa3; 0xfd; 0x40; 0x43; 0xc2; 0x88;
                           (* VSHUFI64X2 (%_% zmm16) (%_% zmm16) (%_% zmm18) (Imm8 (word 136)) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xd1;
                           (* VMOVDQA64 (%_% zmm18) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xf5; 0x40; 0x43; 0xcb; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm17) (%_% zmm19) (Imm8 (word 221)) *)
  0x62; 0xa3; 0xf5; 0x40; 0x43; 0xcb; 0x88;
                           (* VSHUFI64X2 (%_% zmm17) (%_% zmm17) (%_% zmm19) (Imm8 (word 136)) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xd9;
                           (* VMOVDQA64 (%_% zmm19) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xdd; 0x40; 0x43; 0xce; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm20) (%_% zmm22) (Imm8 (word 221)) *)
  0x62; 0xa3; 0xdd; 0x40; 0x43; 0xe6; 0x88;
                           (* VSHUFI64X2 (%_% zmm20) (%_% zmm20) (%_% zmm22) (Imm8 (word 136)) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% zmm22) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xd5; 0x40; 0x43; 0xcf; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm21) (%_% zmm23) (Imm8 (word 221)) *)
  0x62; 0xa3; 0xd5; 0x40; 0x43; 0xef; 0x88;
                           (* VSHUFI64X2 (%_% zmm21) (%_% zmm21) (%_% zmm23) (Imm8 (word 136)) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm23) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xfd; 0x40; 0x43; 0xcc; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm16) (%_% zmm20) (Imm8 (word 221)) *)
  0x62; 0xa3; 0xfd; 0x40; 0x43; 0xc4; 0x88;
                           (* VSHUFI64X2 (%_% zmm16) (%_% zmm16) (%_% zmm20) (Imm8 (word 136)) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xe1;
                           (* VMOVDQA64 (%_% zmm20) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xf5; 0x40; 0x43; 0xcd; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm17) (%_% zmm21) (Imm8 (word 221)) *)
  0x62; 0xa3; 0xf5; 0x40; 0x43; 0xcd; 0x88;
                           (* VSHUFI64X2 (%_% zmm17) (%_% zmm17) (%_% zmm21) (Imm8 (word 136)) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xe9;
                           (* VMOVDQA64 (%_% zmm21) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xed; 0x40; 0x43; 0xce; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm18) (%_% zmm22) (Imm8 (word 221)) *)
  0x62; 0xa3; 0xed; 0x40; 0x43; 0xd6; 0x88;
                           (* VSHUFI64X2 (%_% zmm18) (%_% zmm18) (%_% zmm22) (Imm8 (word 136)) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% zmm22) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xe5; 0x40; 0x43; 0xcf; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm19) (%_% zmm23) (Imm8 (word 221)) *)
  0x62; 0xa3; 0xe5; 0x40; 0x43; 0xdf; 0x88;
                           (* VSHUFI64X2 (%_% zmm19) (%_% zmm19) (%_% zmm23) (Imm8 (word 136)) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm23) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
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
  0x62; 0x03; 0x3d; 0x40; 0x38; 0xc1; 0x01;
                           (* VINSERTI32X4 (%_% zmm24) (%_% zmm24) (%_% xmm25) (Imm8 (word 1)) *)
  0x62; 0x61; 0xfd; 0x08; 0x6e; 0x4f; 0x7c;
                           (* VMOVQ (%_% xmm25) (Memop Quadword (%% (rdi,992))) *)
  0x62; 0x63; 0xb5; 0x00; 0x22; 0x8f; 0xa8; 0x04; 0x00; 0x00; 0x01;
                           (* VPINSRQ (%_% xmm25) (%_% xmm25) (Memop Quadword (%% (rdi,1192)))
(Imm8 (word 1)) *)
  0x62; 0x03; 0x3d; 0x40; 0x38; 0xc1; 0x02;
                           (* VINSERTI32X4 (%_% zmm24) (%_% zmm24) (%_% xmm25) (Imm8 (word 2)) *)
  0x62; 0x61; 0xfd; 0x08; 0x6e; 0x8f; 0x70; 0x05; 0x00; 0x00;
                           (* VMOVQ (%_% xmm25) (Memop Quadword (%% (rdi,1392))) *)
  0x62; 0x63; 0xb5; 0x00; 0x22; 0x8f; 0x38; 0x06; 0x00; 0x00; 0x01;
                           (* VPINSRQ (%_% xmm25) (%_% xmm25) (Memop Quadword (%% (rdi,1592)))
(Imm8 (word 1)) *)
  0x62; 0x03; 0x3d; 0x40; 0x38; 0xc1; 0x03;
                           (* VINSERTI32X4 (%_% zmm24) (%_% zmm24) (%_% xmm25) (Imm8 (word 3)) *)
  0x48; 0xc7; 0xc0; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm32 (word 0)) *)
  0x62; 0x61; 0xfd; 0x48; 0x6f; 0xc8;
                           (* VMOVDQA64 (%_% zmm25) (%_% zmm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xad; 0x48; 0x25; 0xcd; 0x96;
                           (* VPTERNLOGQ (%_% zmm25) (%_% zmm10) (%_% zmm5) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x48; 0x6f; 0xd1;
                           (* VMOVDQA64 (%_% zmm26) (%_% zmm1) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xcd; 0x48; 0x25; 0xd3; 0x96;
                           (* VPTERNLOGQ (%_% zmm26) (%_% zmm6) (%_% zmm11) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x48; 0x6f; 0xda;
                           (* VMOVDQA64 (%_% zmm27) (%_% zmm2) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xc5; 0x48; 0x25; 0xdc; 0x96;
                           (* VPTERNLOGQ (%_% zmm27) (%_% zmm7) (%_% zmm12) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x48; 0x6f; 0xe3;
                           (* VMOVDQA64 (%_% zmm28) (%_% zmm3) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xbd; 0x48; 0x25; 0xe5; 0x96;
                           (* VPTERNLOGQ (%_% zmm28) (%_% zmm8) (%_% zmm13) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x48; 0x6f; 0xec;
                           (* VMOVDQA64 (%_% zmm29) (%_% zmm4) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xb5; 0x48; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% zmm29) (%_% zmm9) (%_% zmm14) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0x85; 0x48; 0x25; 0xcc; 0x96;
                           (* VPTERNLOGQ (%_% zmm25) (%_% zmm15) (%_% zmm20) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xfd; 0x40; 0x25; 0xd5; 0x96;
                           (* VPTERNLOGQ (%_% zmm26) (%_% zmm16) (%_% zmm21) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xf5; 0x40; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% zmm27) (%_% zmm17) (%_% zmm22) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xed; 0x40; 0x25; 0xe7; 0x96;
                           (* VPTERNLOGQ (%_% zmm28) (%_% zmm18) (%_% zmm23) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x40; 0x72; 0xca; 0x01;
                           (* VPROLQ (%_% zmm30) (%_% zmm26) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x85; 0x40; 0x72; 0xcb; 0x01;
                           (* VPROLQ (%_% zmm31) (%_% zmm27) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0xe5; 0x40; 0x25; 0xe8; 0x96;
                           (* VPTERNLOGQ (%_% zmm29) (%_% zmm19) (%_% zmm24) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x40; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% zmm0) (%_% zmm29) (%_% zmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x95; 0x40; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% zmm10) (%_% zmm29) (%_% zmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x95; 0x40; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% zmm20) (%_% zmm29) (%_% zmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x40; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% zmm5) (%_% zmm29) (%_% zmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x95; 0x40; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% zmm15) (%_% zmm29) (%_% zmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x40; 0x72; 0xcc; 0x01;
                           (* VPROLQ (%_% zmm30) (%_% zmm28) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x40; 0x25; 0xf7; 0x96;
                           (* VPTERNLOGQ (%_% zmm6) (%_% zmm25) (%_% zmm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xb5; 0x40; 0x25; 0xc7; 0x96;
                           (* VPTERNLOGQ (%_% zmm16) (%_% zmm25) (%_% zmm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x40; 0x25; 0xcf; 0x96;
                           (* VPTERNLOGQ (%_% zmm1) (%_% zmm25) (%_% zmm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xb5; 0x40; 0x25; 0xdf; 0x96;
                           (* VPTERNLOGQ (%_% zmm11) (%_% zmm25) (%_% zmm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xb5; 0x40; 0x25; 0xef; 0x96;
                           (* VPTERNLOGQ (%_% zmm21) (%_% zmm25) (%_% zmm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x85; 0x40; 0x72; 0xcd; 0x01;
                           (* VPROLQ (%_% zmm31) (%_% zmm29) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x62; 0xfd; 0x48; 0x59; 0x2e;
                           (* VPBROADCASTQ (%_% zmm29) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x83; 0xc6; 0x08;  (* ADD (% rsi) (Imm8 (word 8)) *)
  0x62; 0x13; 0xad; 0x40; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% zmm12) (%_% zmm26) (%_% zmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x40; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% zmm7) (%_% zmm26) (%_% zmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xad; 0x40; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% zmm22) (%_% zmm26) (%_% zmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xad; 0x40; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% zmm17) (%_% zmm26) (%_% zmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x40; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% zmm2) (%_% zmm26) (%_% zmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x40; 0x72; 0xc9; 0x01;
                           (* VPROLQ (%_% zmm30) (%_% zmm25) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xa5; 0x40; 0x25; 0xdf; 0x96;
                           (* VPTERNLOGQ (%_% zmm3) (%_% zmm27) (%_% zmm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xa5; 0x40; 0x25; 0xef; 0x96;
                           (* VPTERNLOGQ (%_% zmm13) (%_% zmm27) (%_% zmm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x40; 0x25; 0xff; 0x96;
                           (* VPTERNLOGQ (%_% zmm23) (%_% zmm27) (%_% zmm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xcd; 0x48; 0x72; 0xce; 0x2c;
                           (* VPROLQ (%_% zmm6) (%_% zmm6) (Imm8 (word 44)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x40; 0x25; 0xd7; 0x96;
                           (* VPTERNLOGQ (%_% zmm18) (%_% zmm27) (%_% zmm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xa5; 0x40; 0x25; 0xc7; 0x96;
                           (* VPTERNLOGQ (%_% zmm8) (%_% zmm27) (%_% zmm31) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x9d; 0x48; 0x72; 0xcc; 0x2b;
                           (* VPROLQ (%_% zmm12) (%_% zmm12) (Imm8 (word 43)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xed; 0x40; 0x72; 0xca; 0x15;
                           (* VPROLQ (%_% zmm18) (%_% zmm18) (Imm8 (word 21)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0x9d; 0x40; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% zmm24) (%_% zmm28) (%_% zmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xbd; 0x40; 0x72; 0xc8; 0x0e;
                           (* VPROLQ (%_% zmm24) (%_% zmm24) (Imm8 (word 14)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xe5; 0x48; 0x72; 0xcb; 0x1c;
                           (* VPROLQ (%_% zmm3) (%_% zmm3) (Imm8 (word 28)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x40; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% zmm9) (%_% zmm28) (%_% zmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xb5; 0x48; 0x72; 0xc9; 0x14;
                           (* VPROLQ (%_% zmm9) (%_% zmm9) (Imm8 (word 20)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xad; 0x48; 0x72; 0xca; 0x03;
                           (* VPROLQ (%_% zmm10) (%_% zmm10) (Imm8 (word 3)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x40; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% zmm19) (%_% zmm28) (%_% zmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xfd; 0x40; 0x72; 0xc8; 0x2d;
                           (* VPROLQ (%_% zmm16) (%_% zmm16) (Imm8 (word 45)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xcd; 0x40; 0x72; 0xce; 0x3d;
                           (* VPROLQ (%_% zmm22) (%_% zmm22) (Imm8 (word 61)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x9d; 0x40; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% zmm4) (%_% zmm28) (%_% zmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xf5; 0x48; 0x72; 0xc9; 0x01;
                           (* VPROLQ (%_% zmm1) (%_% zmm1) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xc5; 0x48; 0x72; 0xcf; 0x06;
                           (* VPROLQ (%_% zmm7) (%_% zmm7) (Imm8 (word 6)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x40; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% zmm14) (%_% zmm28) (%_% zmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x95; 0x48; 0x72; 0xcd; 0x19;
                           (* VPROLQ (%_% zmm13) (%_% zmm13) (Imm8 (word 25)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xe5; 0x40; 0x72; 0xcb; 0x08;
                           (* VPROLQ (%_% zmm19) (%_% zmm19) (Imm8 (word 8)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x48; 0x6f; 0xf0;
                           (* VMOVDQA64 (%_% zmm30) (%_% zmm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xcd; 0x48; 0x25; 0xf4; 0xd2;
                           (* VPTERNLOGQ (%_% zmm30) (%_% zmm6) (%_% zmm12) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xdd; 0x40; 0x72; 0xcc; 0x12;
                           (* VPROLQ (%_% zmm20) (%_% zmm20) (Imm8 (word 18)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xdd; 0x48; 0x72; 0xcc; 0x1b;
                           (* VPROLQ (%_% zmm4) (%_% zmm4) (Imm8 (word 27)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0x8d; 0x40; 0xef; 0xf5;
                           (* VPXORQ (%_% zmm30) (%_% zmm30) (%_% zmm29) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xd5; 0x48; 0x72; 0xcd; 0x24;
                           (* VPROLQ (%_% zmm5) (%_% zmm5) (Imm8 (word 36)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xa5; 0x48; 0x72; 0xcb; 0x0a;
                           (* VPROLQ (%_% zmm11) (%_% zmm11) (Imm8 (word 10)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x48; 0x6f; 0xfe;
                           (* VMOVDQA64 (%_% zmm31) (%_% zmm6) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0x9d; 0x48; 0x25; 0xfa; 0xd2;
                           (* VPTERNLOGQ (%_% zmm31) (%_% zmm12) (%_% zmm18) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xf5; 0x40; 0x72; 0xc9; 0x0f;
                           (* VPROLQ (%_% zmm17) (%_% zmm17) (Imm8 (word 15)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xc5; 0x40; 0x72; 0xcf; 0x38;
                           (* VPROLQ (%_% zmm23) (%_% zmm23) (Imm8 (word 56)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xed; 0x40; 0x25; 0xe0; 0xd2;
                           (* VPTERNLOGQ (%_% zmm12) (%_% zmm18) (%_% zmm24) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xed; 0x48; 0x72; 0xca; 0x3e;
                           (* VPROLQ (%_% zmm2) (%_% zmm2) (Imm8 (word 62)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xbd; 0x48; 0x72; 0xc8; 0x37;
                           (* VPROLQ (%_% zmm8) (%_% zmm8) (Imm8 (word 55)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xbd; 0x40; 0x25; 0xd0; 0xd2;
                           (* VPTERNLOGQ (%_% zmm18) (%_% zmm24) (%_% zmm0) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x8d; 0x48; 0x72; 0xce; 0x27;
                           (* VPROLQ (%_% zmm14) (%_% zmm14) (Imm8 (word 39)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x85; 0x48; 0x72; 0xcf; 0x29;
                           (* VPROLQ (%_% zmm15) (%_% zmm15) (Imm8 (word 41)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xfd; 0x48; 0x25; 0xc6; 0xd2;
                           (* VPTERNLOGQ (%_% zmm24) (%_% zmm0) (%_% zmm6) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xc6;
                           (* VMOVDQA64 (%_% zmm0) (%_% zmm30) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xf7;
                           (* VMOVDQA64 (%_% zmm6) (%_% zmm31) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xd5; 0x40; 0x72; 0xcd; 0x02;
                           (* VPROLQ (%_% zmm21) (%_% zmm21) (Imm8 (word 2)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x48; 0x6f; 0xf3;
                           (* VMOVDQA64 (%_% zmm30) (%_% zmm3) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xb5; 0x48; 0x25; 0xf2; 0xd2;
                           (* VPTERNLOGQ (%_% zmm30) (%_% zmm9) (%_% zmm10) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm31) (%_% zmm9) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xad; 0x48; 0x25; 0xf8; 0xd2;
                           (* VPTERNLOGQ (%_% zmm31) (%_% zmm10) (%_% zmm16) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xfd; 0x40; 0x25; 0xd6; 0xd2;
                           (* VPTERNLOGQ (%_% zmm10) (%_% zmm16) (%_% zmm22) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xcd; 0x40; 0x25; 0xc3; 0xd2;
                           (* VPTERNLOGQ (%_% zmm16) (%_% zmm22) (%_% zmm3) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0xe5; 0x48; 0x25; 0xf1; 0xd2;
                           (* VPTERNLOGQ (%_% zmm22) (%_% zmm3) (%_% zmm9) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xde;
                           (* VMOVDQA64 (%_% zmm3) (%_% zmm30) (Evex_deco Unmasked No_brc) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xcf;
                           (* VMOVDQA64 (%_% zmm9) (%_% zmm31) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x48; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% zmm30) (%_% zmm1) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xc5; 0x48; 0x25; 0xf5; 0xd2;
                           (* VPTERNLOGQ (%_% zmm30) (%_% zmm7) (%_% zmm13) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x48; 0x6f; 0xff;
                           (* VMOVDQA64 (%_% zmm31) (%_% zmm7) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0x95; 0x48; 0x25; 0xfb; 0xd2;
                           (* VPTERNLOGQ (%_% zmm31) (%_% zmm13) (%_% zmm19) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xe5; 0x40; 0x25; 0xec; 0xd2;
                           (* VPTERNLOGQ (%_% zmm13) (%_% zmm19) (%_% zmm20) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xdd; 0x40; 0x25; 0xd9; 0xd2;
                           (* VPTERNLOGQ (%_% zmm19) (%_% zmm20) (%_% zmm1) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xf5; 0x48; 0x25; 0xe7; 0xd2;
                           (* VPTERNLOGQ (%_% zmm20) (%_% zmm1) (%_% zmm7) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xce;
                           (* VMOVDQA64 (%_% zmm1) (%_% zmm30) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xff;
                           (* VMOVDQA64 (%_% zmm7) (%_% zmm31) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x48; 0x6f; 0xf4;
                           (* VMOVDQA64 (%_% zmm30) (%_% zmm4) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xd5; 0x48; 0x25; 0xf3; 0xd2;
                           (* VPTERNLOGQ (%_% zmm30) (%_% zmm5) (%_% zmm11) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x48; 0x6f; 0xfd;
                           (* VMOVDQA64 (%_% zmm31) (%_% zmm5) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xa5; 0x48; 0x25; 0xf9; 0xd2;
                           (* VPTERNLOGQ (%_% zmm31) (%_% zmm11) (%_% zmm17) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xf5; 0x40; 0x25; 0xdf; 0xd2;
                           (* VPTERNLOGQ (%_% zmm11) (%_% zmm17) (%_% zmm23) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xc5; 0x40; 0x25; 0xcc; 0xd2;
                           (* VPTERNLOGQ (%_% zmm17) (%_% zmm23) (%_% zmm4) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xdd; 0x48; 0x25; 0xfd; 0xd2;
                           (* VPTERNLOGQ (%_% zmm23) (%_% zmm4) (%_% zmm5) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xe6;
                           (* VMOVDQA64 (%_% zmm4) (%_% zmm30) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xef;
                           (* VMOVDQA64 (%_% zmm5) (%_% zmm31) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x48; 0x6f; 0xf2;
                           (* VMOVDQA64 (%_% zmm30) (%_% zmm2) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xbd; 0x48; 0x25; 0xf6; 0xd2;
                           (* VPTERNLOGQ (%_% zmm30) (%_% zmm8) (%_% zmm14) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x48; 0x6f; 0xf8;
                           (* VMOVDQA64 (%_% zmm31) (%_% zmm8) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0x8d; 0x48; 0x25; 0xff; 0xd2;
                           (* VPTERNLOGQ (%_% zmm31) (%_% zmm14) (%_% zmm15) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0x85; 0x48; 0x25; 0xf5; 0xd2;
                           (* VPTERNLOGQ (%_% zmm14) (%_% zmm15) (%_% zmm21) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x73; 0xd5; 0x40; 0x25; 0xfa; 0xd2;
                           (* VPTERNLOGQ (%_% zmm15) (%_% zmm21) (%_% zmm2) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0xed; 0x48; 0x25; 0xe8; 0xd2;
                           (* VPTERNLOGQ (%_% zmm21) (%_% zmm2) (%_% zmm8) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xd6;
                           (* VMOVDQA64 (%_% zmm2) (%_% zmm30) (Evex_deco Unmasked No_brc) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xc7;
                           (* VMOVDQA64 (%_% zmm8) (%_% zmm31) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x48; 0x6f; 0xf3;
                           (* VMOVDQA64 (%_% zmm30) (%_% zmm3) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xfd; 0x48; 0x6f; 0xda;
                           (* VMOVDQA64 (%_% zmm3) (%_% zmm18) (Evex_deco Unmasked No_brc) *)
  0x62; 0xa1; 0xfd; 0x48; 0x6f; 0xd1;
                           (* VMOVDQA64 (%_% zmm18) (%_% zmm17) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc1; 0xfd; 0x48; 0x6f; 0xcb;
                           (* VMOVDQA64 (%_% zmm17) (%_% zmm11) (Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfd; 0x48; 0x6f; 0xdf;
                           (* VMOVDQA64 (%_% zmm11) (%_% zmm7) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xfd; 0x48; 0x6f; 0xfa;
                           (* VMOVDQA64 (%_% zmm7) (%_% zmm10) (Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfd; 0x48; 0x6f; 0xd1;
                           (* VMOVDQA64 (%_% zmm10) (%_% zmm1) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfd; 0x48; 0x6f; 0xce;
                           (* VMOVDQA64 (%_% zmm1) (%_% zmm6) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xfd; 0x48; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% zmm6) (%_% zmm9) (Evex_deco Unmasked No_brc) *)
  0x62; 0x31; 0xfd; 0x48; 0x6f; 0xce;
                           (* VMOVDQA64 (%_% zmm9) (%_% zmm22) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc1; 0xfd; 0x48; 0x6f; 0xf6;
                           (* VMOVDQA64 (%_% zmm22) (%_% zmm14) (Evex_deco Unmasked No_brc) *)
  0x62; 0x31; 0xfd; 0x48; 0x6f; 0xf4;
                           (* VMOVDQA64 (%_% zmm14) (%_% zmm20) (Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfd; 0x48; 0x6f; 0xe2;
                           (* VMOVDQA64 (%_% zmm20) (%_% zmm2) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xfd; 0x48; 0x6f; 0xd4;
                           (* VMOVDQA64 (%_% zmm2) (%_% zmm12) (Evex_deco Unmasked No_brc) *)
  0x62; 0x51; 0xfd; 0x48; 0x6f; 0xe5;
                           (* VMOVDQA64 (%_% zmm12) (%_% zmm13) (Evex_deco Unmasked No_brc) *)
  0x62; 0x31; 0xfd; 0x48; 0x6f; 0xeb;
                           (* VMOVDQA64 (%_% zmm13) (%_% zmm19) (Evex_deco Unmasked No_brc) *)
  0x62; 0xa1; 0xfd; 0x48; 0x6f; 0xdf;
                           (* VMOVDQA64 (%_% zmm19) (%_% zmm23) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc1; 0xfd; 0x48; 0x6f; 0xff;
                           (* VMOVDQA64 (%_% zmm23) (%_% zmm15) (Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfd; 0x48; 0x6f; 0xfc;
                           (* VMOVDQA64 (%_% zmm15) (%_% zmm4) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xe0;
                           (* VMOVDQA64 (%_% zmm4) (%_% zmm24) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x48; 0x6f; 0xc5;
                           (* VMOVDQA64 (%_% zmm24) (%_% zmm21) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc1; 0xfd; 0x48; 0x6f; 0xe8;
                           (* VMOVDQA64 (%_% zmm21) (%_% zmm8) (Evex_deco Unmasked No_brc) *)
  0x62; 0x31; 0xfd; 0x48; 0x6f; 0xc0;
                           (* VMOVDQA64 (%_% zmm8) (%_% zmm16) (Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfd; 0x48; 0x6f; 0xc5;
                           (* VMOVDQA64 (%_% zmm16) (%_% zmm5) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xee;
                           (* VMOVDQA64 (%_% zmm5) (%_% zmm30) (Evex_deco Unmasked No_brc) *)
  0x48; 0x83; 0xc0; 0x01;  (* ADD (% rax) (Imm8 (word 1)) *)
  0x48; 0x83; 0xf8; 0x18;  (* CMP (% rax) (Imm8 (word 24)) *)
  0x0f; 0x85; 0x47; 0xfc; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294966343)) *)
  0x62; 0x61; 0xfd; 0x48; 0x6d; 0xc9;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm0) (%_% zmm1) *)
  0x62; 0xf1; 0xfd; 0x48; 0x6c; 0xc1;
                           (* VPUNPCKLQDQ (%_% zmm0) (%_% zmm0) (%_% zmm1) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xc9;
                           (* VMOVDQA64 (%_% zmm1) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xed; 0x48; 0x6d; 0xcb;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm2) (%_% zmm3) *)
  0x62; 0xf1; 0xed; 0x48; 0x6c; 0xd3;
                           (* VPUNPCKLQDQ (%_% zmm2) (%_% zmm2) (%_% zmm3) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xd9;
                           (* VMOVDQA64 (%_% zmm3) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xdd; 0x48; 0x6d; 0xcd;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm4) (%_% zmm5) *)
  0x62; 0xf1; 0xdd; 0x48; 0x6c; 0xe5;
                           (* VPUNPCKLQDQ (%_% zmm4) (%_% zmm4) (%_% zmm5) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xe9;
                           (* VMOVDQA64 (%_% zmm5) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xcd; 0x48; 0x6d; 0xcf;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm6) (%_% zmm7) *)
  0x62; 0xf1; 0xcd; 0x48; 0x6c; 0xf7;
                           (* VPUNPCKLQDQ (%_% zmm6) (%_% zmm6) (%_% zmm7) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm7) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xfd; 0x48; 0x43; 0xca; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm0) (%_% zmm2) (Imm8 (word 221)) *)
  0x62; 0xf3; 0xfd; 0x48; 0x43; 0xc2; 0x88;
                           (* VSHUFI64X2 (%_% zmm0) (%_% zmm0) (%_% zmm2) (Imm8 (word 136)) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xd1;
                           (* VMOVDQA64 (%_% zmm2) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xf5; 0x48; 0x43; 0xcb; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm1) (%_% zmm3) (Imm8 (word 221)) *)
  0x62; 0xf3; 0xf5; 0x48; 0x43; 0xcb; 0x88;
                           (* VSHUFI64X2 (%_% zmm1) (%_% zmm1) (%_% zmm3) (Imm8 (word 136)) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xd9;
                           (* VMOVDQA64 (%_% zmm3) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xdd; 0x48; 0x43; 0xce; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm4) (%_% zmm6) (Imm8 (word 221)) *)
  0x62; 0xf3; 0xdd; 0x48; 0x43; 0xe6; 0x88;
                           (* VSHUFI64X2 (%_% zmm4) (%_% zmm4) (%_% zmm6) (Imm8 (word 136)) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% zmm6) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xd5; 0x48; 0x43; 0xcf; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm5) (%_% zmm7) (Imm8 (word 221)) *)
  0x62; 0xf3; 0xd5; 0x48; 0x43; 0xef; 0x88;
                           (* VSHUFI64X2 (%_% zmm5) (%_% zmm5) (%_% zmm7) (Imm8 (word 136)) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm7) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xfd; 0x48; 0x43; 0xcc; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm0) (%_% zmm4) (Imm8 (word 221)) *)
  0x62; 0xf3; 0xfd; 0x48; 0x43; 0xc4; 0x88;
                           (* VSHUFI64X2 (%_% zmm0) (%_% zmm0) (%_% zmm4) (Imm8 (word 136)) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xe1;
                           (* VMOVDQA64 (%_% zmm4) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xf5; 0x48; 0x43; 0xcd; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm1) (%_% zmm5) (Imm8 (word 221)) *)
  0x62; 0xf3; 0xf5; 0x48; 0x43; 0xcd; 0x88;
                           (* VSHUFI64X2 (%_% zmm1) (%_% zmm1) (%_% zmm5) (Imm8 (word 136)) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xe9;
                           (* VMOVDQA64 (%_% zmm5) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xed; 0x48; 0x43; 0xce; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm2) (%_% zmm6) (Imm8 (word 221)) *)
  0x62; 0xf3; 0xed; 0x48; 0x43; 0xd6; 0x88;
                           (* VSHUFI64X2 (%_% zmm2) (%_% zmm2) (%_% zmm6) (Imm8 (word 136)) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% zmm6) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xe5; 0x48; 0x43; 0xcf; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm3) (%_% zmm7) (Imm8 (word 221)) *)
  0x62; 0xf3; 0xe5; 0x48; 0x43; 0xdf; 0x88;
                           (* VSHUFI64X2 (%_% zmm3) (%_% zmm3) (%_% zmm7) (Imm8 (word 136)) *)
  0x62; 0x91; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm7) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x48; 0x7f; 0x07;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,0))) (%_% zmm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x48; 0x7f; 0x8f; 0xc8; 0x00; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,200))) (%_% zmm1)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x48; 0x7f; 0x97; 0x90; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,400))) (%_% zmm2)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x48; 0x7f; 0x9f; 0x58; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,600))) (%_% zmm3)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x48; 0x7f; 0xa7; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,800))) (%_% zmm4)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x48; 0x7f; 0xaf; 0xe8; 0x03; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,1000))) (%_% zmm5)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x48; 0x7f; 0xb7; 0xb0; 0x04; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,1200))) (%_% zmm6)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfe; 0x48; 0x7f; 0xbf; 0x78; 0x05; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,1400))) (%_% zmm7)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xbd; 0x48; 0x6d; 0xc9;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm8) (%_% zmm9) *)
  0x62; 0x51; 0xbd; 0x48; 0x6c; 0xc1;
                           (* VPUNPCKLQDQ (%_% zmm8) (%_% zmm8) (%_% zmm9) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xc9;
                           (* VMOVDQA64 (%_% zmm9) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xad; 0x48; 0x6d; 0xcb;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm10) (%_% zmm11) *)
  0x62; 0x51; 0xad; 0x48; 0x6c; 0xd3;
                           (* VPUNPCKLQDQ (%_% zmm10) (%_% zmm10) (%_% zmm11) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xd9;
                           (* VMOVDQA64 (%_% zmm11) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0x9d; 0x48; 0x6d; 0xcd;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm12) (%_% zmm13) *)
  0x62; 0x51; 0x9d; 0x48; 0x6c; 0xe5;
                           (* VPUNPCKLQDQ (%_% zmm12) (%_% zmm12) (%_% zmm13) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xe9;
                           (* VMOVDQA64 (%_% zmm13) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0x8d; 0x48; 0x6d; 0xcf;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm14) (%_% zmm15) *)
  0x62; 0x51; 0x8d; 0x48; 0x6c; 0xf7;
                           (* VPUNPCKLQDQ (%_% zmm14) (%_% zmm14) (%_% zmm15) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm15) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xbd; 0x48; 0x43; 0xca; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm8) (%_% zmm10) (Imm8 (word 221)) *)
  0x62; 0x53; 0xbd; 0x48; 0x43; 0xc2; 0x88;
                           (* VSHUFI64X2 (%_% zmm8) (%_% zmm8) (%_% zmm10) (Imm8 (word 136)) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xd1;
                           (* VMOVDQA64 (%_% zmm10) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xb5; 0x48; 0x43; 0xcb; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm9) (%_% zmm11) (Imm8 (word 221)) *)
  0x62; 0x53; 0xb5; 0x48; 0x43; 0xcb; 0x88;
                           (* VSHUFI64X2 (%_% zmm9) (%_% zmm9) (%_% zmm11) (Imm8 (word 136)) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xd9;
                           (* VMOVDQA64 (%_% zmm11) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0x9d; 0x48; 0x43; 0xce; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm12) (%_% zmm14) (Imm8 (word 221)) *)
  0x62; 0x53; 0x9d; 0x48; 0x43; 0xe6; 0x88;
                           (* VSHUFI64X2 (%_% zmm12) (%_% zmm12) (%_% zmm14) (Imm8 (word 136)) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% zmm14) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0x95; 0x48; 0x43; 0xcf; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm13) (%_% zmm15) (Imm8 (word 221)) *)
  0x62; 0x53; 0x95; 0x48; 0x43; 0xef; 0x88;
                           (* VSHUFI64X2 (%_% zmm13) (%_% zmm13) (%_% zmm15) (Imm8 (word 136)) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm15) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xbd; 0x48; 0x43; 0xcc; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm8) (%_% zmm12) (Imm8 (word 221)) *)
  0x62; 0x53; 0xbd; 0x48; 0x43; 0xc4; 0x88;
                           (* VSHUFI64X2 (%_% zmm8) (%_% zmm8) (%_% zmm12) (Imm8 (word 136)) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xe1;
                           (* VMOVDQA64 (%_% zmm12) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xb5; 0x48; 0x43; 0xcd; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm9) (%_% zmm13) (Imm8 (word 221)) *)
  0x62; 0x53; 0xb5; 0x48; 0x43; 0xcd; 0x88;
                           (* VSHUFI64X2 (%_% zmm9) (%_% zmm9) (%_% zmm13) (Imm8 (word 136)) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xe9;
                           (* VMOVDQA64 (%_% zmm13) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xad; 0x48; 0x43; 0xce; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm10) (%_% zmm14) (Imm8 (word 221)) *)
  0x62; 0x53; 0xad; 0x48; 0x43; 0xd6; 0x88;
                           (* VSHUFI64X2 (%_% zmm10) (%_% zmm10) (%_% zmm14) (Imm8 (word 136)) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% zmm14) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xa5; 0x48; 0x43; 0xcf; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm11) (%_% zmm15) (Imm8 (word 221)) *)
  0x62; 0x53; 0xa5; 0x48; 0x43; 0xdf; 0x88;
                           (* VSHUFI64X2 (%_% zmm11) (%_% zmm11) (%_% zmm15) (Imm8 (word 136)) *)
  0x62; 0x11; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm15) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x48; 0x7f; 0x47; 0x01;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,64))) (%_% zmm8)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x48; 0x7f; 0x8f; 0x08; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,264))) (%_% zmm9)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x48; 0x7f; 0x97; 0xd0; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,464))) (%_% zmm10)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x48; 0x7f; 0x9f; 0x98; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,664))) (%_% zmm11)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x48; 0x7f; 0xa7; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,864))) (%_% zmm12)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x48; 0x7f; 0xaf; 0x28; 0x04; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,1064))) (%_% zmm13)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x48; 0x7f; 0xb7; 0xf0; 0x04; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,1264))) (%_% zmm14)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x71; 0xfe; 0x48; 0x7f; 0xbf; 0xb8; 0x05; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,1464))) (%_% zmm15)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x40; 0x6d; 0xc9;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm16) (%_% zmm17) *)
  0x62; 0xa1; 0xfd; 0x40; 0x6c; 0xc1;
                           (* VPUNPCKLQDQ (%_% zmm16) (%_% zmm16) (%_% zmm17) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xc9;
                           (* VMOVDQA64 (%_% zmm17) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xed; 0x40; 0x6d; 0xcb;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm18) (%_% zmm19) *)
  0x62; 0xa1; 0xed; 0x40; 0x6c; 0xd3;
                           (* VPUNPCKLQDQ (%_% zmm18) (%_% zmm18) (%_% zmm19) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xd9;
                           (* VMOVDQA64 (%_% zmm19) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xdd; 0x40; 0x6d; 0xcd;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm20) (%_% zmm21) *)
  0x62; 0xa1; 0xdd; 0x40; 0x6c; 0xe5;
                           (* VPUNPCKLQDQ (%_% zmm20) (%_% zmm20) (%_% zmm21) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xe9;
                           (* VMOVDQA64 (%_% zmm21) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xcd; 0x40; 0x6d; 0xcf;
                           (* VPUNPCKHQDQ (%_% zmm25) (%_% zmm22) (%_% zmm23) *)
  0x62; 0xa1; 0xcd; 0x40; 0x6c; 0xf7;
                           (* VPUNPCKLQDQ (%_% zmm22) (%_% zmm22) (%_% zmm23) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm23) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xfd; 0x40; 0x43; 0xca; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm16) (%_% zmm18) (Imm8 (word 221)) *)
  0x62; 0xa3; 0xfd; 0x40; 0x43; 0xc2; 0x88;
                           (* VSHUFI64X2 (%_% zmm16) (%_% zmm16) (%_% zmm18) (Imm8 (word 136)) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xd1;
                           (* VMOVDQA64 (%_% zmm18) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xf5; 0x40; 0x43; 0xcb; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm17) (%_% zmm19) (Imm8 (word 221)) *)
  0x62; 0xa3; 0xf5; 0x40; 0x43; 0xcb; 0x88;
                           (* VSHUFI64X2 (%_% zmm17) (%_% zmm17) (%_% zmm19) (Imm8 (word 136)) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xd9;
                           (* VMOVDQA64 (%_% zmm19) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xdd; 0x40; 0x43; 0xce; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm20) (%_% zmm22) (Imm8 (word 221)) *)
  0x62; 0xa3; 0xdd; 0x40; 0x43; 0xe6; 0x88;
                           (* VSHUFI64X2 (%_% zmm20) (%_% zmm20) (%_% zmm22) (Imm8 (word 136)) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% zmm22) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xd5; 0x40; 0x43; 0xcf; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm21) (%_% zmm23) (Imm8 (word 221)) *)
  0x62; 0xa3; 0xd5; 0x40; 0x43; 0xef; 0x88;
                           (* VSHUFI64X2 (%_% zmm21) (%_% zmm21) (%_% zmm23) (Imm8 (word 136)) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm23) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xfd; 0x40; 0x43; 0xcc; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm16) (%_% zmm20) (Imm8 (word 221)) *)
  0x62; 0xa3; 0xfd; 0x40; 0x43; 0xc4; 0x88;
                           (* VSHUFI64X2 (%_% zmm16) (%_% zmm16) (%_% zmm20) (Imm8 (word 136)) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xe1;
                           (* VMOVDQA64 (%_% zmm20) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xf5; 0x40; 0x43; 0xcd; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm17) (%_% zmm21) (Imm8 (word 221)) *)
  0x62; 0xa3; 0xf5; 0x40; 0x43; 0xcd; 0x88;
                           (* VSHUFI64X2 (%_% zmm17) (%_% zmm17) (%_% zmm21) (Imm8 (word 136)) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xe9;
                           (* VMOVDQA64 (%_% zmm21) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xed; 0x40; 0x43; 0xce; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm18) (%_% zmm22) (Imm8 (word 221)) *)
  0x62; 0xa3; 0xed; 0x40; 0x43; 0xd6; 0x88;
                           (* VSHUFI64X2 (%_% zmm18) (%_% zmm18) (%_% zmm22) (Imm8 (word 136)) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% zmm22) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xe5; 0x40; 0x43; 0xcf; 0xdd;
                           (* VSHUFI64X2 (%_% zmm25) (%_% zmm19) (%_% zmm23) (Imm8 (word 221)) *)
  0x62; 0xa3; 0xe5; 0x40; 0x43; 0xdf; 0x88;
                           (* VSHUFI64X2 (%_% zmm19) (%_% zmm19) (%_% zmm23) (Imm8 (word 136)) *)
  0x62; 0x81; 0xfd; 0x48; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% zmm23) (%_% zmm25) (Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x48; 0x7f; 0x47; 0x02;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,128))) (%_% zmm16)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x48; 0x7f; 0x8f; 0x48; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,328))) (%_% zmm17)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x48; 0x7f; 0x97; 0x10; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,528))) (%_% zmm18)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x48; 0x7f; 0x9f; 0xd8; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,728))) (%_% zmm19)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x48; 0x7f; 0xa7; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,928))) (%_% zmm20)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x48; 0x7f; 0xaf; 0x68; 0x04; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,1128))) (%_% zmm21)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x48; 0x7f; 0xb7; 0x30; 0x05; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,1328))) (%_% zmm22)
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfe; 0x48; 0x7f; 0xbf; 0xf8; 0x05; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word512 (%% (rdi,1528))) (%_% zmm23)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x7e; 0x47; 0x18;
                           (* VMOVQ (Memop Quadword (%% (rdi,192))) (%_% xmm24) *)
  0x62; 0x63; 0xfd; 0x08; 0x16; 0x47; 0x31; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,392))) (%_% xmm24) (Imm8 (word 1)) *)
  0x62; 0x03; 0x7d; 0x48; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI32X4 (%_% xmm25) (%_% zmm24) (Imm8 (word 1)) *)
  0x62; 0x61; 0xfd; 0x08; 0x7e; 0x4f; 0x4a;
                           (* VMOVQ (Memop Quadword (%% (rdi,592))) (%_% xmm25) *)
  0x62; 0x63; 0xfd; 0x08; 0x16; 0x4f; 0x63; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,792))) (%_% xmm25) (Imm8 (word 1)) *)
  0x62; 0x03; 0x7d; 0x48; 0x39; 0xc1; 0x02;
                           (* VEXTRACTI32X4 (%_% xmm25) (%_% zmm24) (Imm8 (word 2)) *)
  0x62; 0x61; 0xfd; 0x08; 0x7e; 0x4f; 0x7c;
                           (* VMOVQ (Memop Quadword (%% (rdi,992))) (%_% xmm25) *)
  0x62; 0x63; 0xfd; 0x08; 0x16; 0x8f; 0xa8; 0x04; 0x00; 0x00; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,1192))) (%_% xmm25) (Imm8 (word 1)) *)
  0x62; 0x03; 0x7d; 0x48; 0x39; 0xc1; 0x03;
                           (* VEXTRACTI32X4 (%_% xmm25) (%_% zmm24) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfd; 0x08; 0x7e; 0x8f; 0x70; 0x05; 0x00; 0x00;
                           (* VMOVQ (Memop Quadword (%% (rdi,1392))) (%_% xmm25) *)
  0x62; 0x63; 0xfd; 0x08; 0x16; 0x8f; 0x38; 0x06; 0x00; 0x00; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,1592))) (%_% xmm25) (Imm8 (word 1)) *)
  0xc5; 0xf8; 0x77;        (* VZEROUPPER *)
  0xc3                     (* RET *)
];;

let sha3_keccak8_f1600_avx512_tmc = define_trimmed "sha3_keccak8_f1600_avx512_tmc" sha3_keccak8_f1600_avx512_mc;;

let SHA3_KECCAK8_F1600_AVX512_EXEC = X86_MK_CORE_EXEC_RULE sha3_keccak8_f1600_avx512_tmc;;

(* Symbolic execution with ZMM abbreviation: X86_ABBREV_STEPS_TAC execth ns
   steps the instructions ns one at a time and, after each step, abbreviates
   each non-variable `read ZMMk sN = rhs` of the new state to a fresh
   variable, so the stepped 512-bit terms never nest. *)
let X86_ABBREV_STEPS_TAC =
  let abbrev_tac sname =
    let st = mk_var(sname,`:x86state`) in
    let is_new_zmm_read t =
      match t with
        Comb(Comb(Const("read",_),Const(n,_)),s) ->
          s = st && String.length n >= 3 && String.sub n 0 3 = "ZMM"
      | _ -> false in
    let target th =
      let c = concl th in
      if not(is_eq c && is_new_zmm_read(lhand c)) then failwith "target" else
      let e = rand c in
      if is_var e then failwith "target" else e in
    W(fun (asl,_) ->
      MAP_EVERY (fun t -> ABBREV_TAC(mk_eq(genvar(type_of t),t)))
                (mapfilter (target o snd) asl)) in
  fun execth ns ->
    MAP_EVERY (fun n -> X86_STEPS_TAC execth [n] THEN
                        abbrev_tac ("s"^string_of_int n)) ns;;

(* Discharge a conjunction of 512-bit lane equations.  Each lane is split into
   its eight 64-bit sublanes (one per state).  Every equation of the
   abbreviation chain and of the ghost/invariant facts is projected to each
   sublane by pushing word_subword inward; the goal is rewritten with these,
   the assumptions are dropped, and the first sublane is closed bit by bit
   and reused (by matching) for the others. *)
let SUBLANE_BITBLAST : tactic =
  let SPLIT_SUBLANES = prove
   (`!x y:int512.
       x = y <=>
       (word_subword x (0,64)):int64 = word_subword y (0,64) /\
       (word_subword x (64,64)):int64 = word_subword y (64,64) /\
       (word_subword x (128,64)):int64 = word_subword y (128,64) /\
       (word_subword x (192,64)):int64 = word_subword y (192,64) /\
       (word_subword x (256,64)):int64 = word_subword y (256,64) /\
       (word_subword x (320,64)):int64 = word_subword y (320,64) /\
       (word_subword x (384,64)):int64 = word_subword y (384,64) /\
       (word_subword x (448,64)):int64 = word_subword y (448,64)`,
    REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]; BITBLAST_TAC]) in
  (* push word_subword inward through word_join/word_subword/word_zx and
     word_and/word_or/word_xor/word_not, projecting a lane expression down to
     one 64-bit sublane *)
  let SUBWORD_PUSH_CONV =
    TOP_DEPTH_CONV
     (WORD_SIMPLE_SUBWORD_CONV ORELSEC
      GEN_REWRITE_CONV I
       [WORD_SUBWORD_AND; WORD_SUBWORD_OR; WORD_SUBWORD_XOR] ORELSEC
      (MP_CONV (REWRITE_CONV[DIMINDEX_64; DIMINDEX_128; DIMINDEX_256;
                             DIMINDEX_512] THENC NUM_REDUCE_CONV) o
       IMP_REWR_CONV WORD_SUBWORD_NOT)) in
  (* per-output-bit BITBLAST: one tiny BDD per bit *)
  let PERBIT_BITBLAST =
    BITBLAST_THEN (fun vars ->
      REPEAT CONJ_TAC THEN
      W(fun (_,w) -> ACCEPT_TAC(prove(w, CONV_TAC(BDD_DEFTAUT vars))))) in
  (* project an equation to sublane j (word_subword _ (64j,64) of both sides,
     pushed inward), oriented to rewrite away an abbreviation variable if it
     has one, else a ghost variable *)
  let subword_tm = `word_subword:N word->num#num->int64` in
  let is_atom t =
    match t with
      Comb(Comb(Const("word_subword",_),v),_) -> is_var v
    | _ -> false in
  let is_abbrev_atom t =
    is_atom t && let n = fst(dest_var(lhand t)) in n <> "" && n.[0] = '_' in
  let proj_lane j th =
    let pos = mk_pair(mk_small_numeral(64*j),`64`) in
    let n = hd(snd(dest_type(type_of(lhand(concl th))))) in
    let pth = CONV_RULE(BINOP_CONV SUBWORD_PUSH_CONV)
      (AP_THM (AP_TERM (inst [n,`:N`] subword_tm) th) pos) in
    let l = lhand(concl pth) and r = rand(concl pth) in
    if is_abbrev_atom r then SYM pth
    else if is_atom l then pth
    else if is_atom r then SYM pth
    else failwith "proj_lane" in
  REPEAT CONJ_TAC THEN
  (ONCE_REWRITE_TAC[SPLIT_SUBLANES] THEN CONV_TAC SUBWORD_PUSH_CONV THEN
   W(fun (asl,_) ->
      let eqs = flat(map (CONJUNCTS o snd) asl) in
      REWRITE_TAC(flat(map (fun j -> mapfilter (proj_lane j) eqs) (0--7)))) THEN
   POP_ASSUM_LIST(K ALL_TAC) THEN
   (* prove the state-1 sublane once, generalise it over its free variables,
      and use the result for all eight sublanes *)
   W(fun (_,w) ->
      let th = prove(hd(conjuncts w), PERBIT_BITBLAST) in
      REPEAT CONJ_TAC THEN MATCH_ACCEPT_TAC(GENL (frees(concl th)) th)));;

(* Discharge for Initial holding and the tail: unfold the abbreviation chain
   (GSYM the `expr = _v` and `.. = EL k Bj` assumptions, not the
   `read .. = _v` ones), then bit-blast (the transpose is a pure digit
   permutation). *)
let TRANSPOSE_BITBLAST : tactic =
  let head_name t = name_of(fst(strip_comb t)) in
  let is_genvar v = is_var v && let n = name_of v in n <> "" && n.[0] = '_' in
  (* `expr = _v` chain facts (not the `read .. = _v` ones) and `.. = EL k B` *)
  let unfoldable th =
    let c = concl th in
    is_eq c &&
    (is_genvar(rand c) && head_name(lhand c) <> "read" ||
     head_name(rand c) = "EL") in
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check(is_conj o concl))) THEN
  W(fun (asl,_) -> REWRITE_TAC(map GSYM (filter unfoldable (map snd asl)))) THEN
  BITBLAST_TAC;;

let SHA3_KECCAK8_F1600_AVX512_CORRECT = prove
  (`!rc_pointer:int64 bitstate_in:int64 A1 A2 A3 A4 A5 A6 A7 A8 pc:num.
    nonoverlapping (word pc, 0xbb4) (bitstate_in, 1600) /\
    nonoverlapping (word pc, 0xbb4) (rc_pointer, 192) /\
    nonoverlapping (bitstate_in,1600) (rc_pointer,192)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST sha3_keccak8_f1600_avx512_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [bitstate_in; rc_pointer] s /\
              wordlist_from_memory(rc_pointer,24) s = round_constants /\
              wordlist_from_memory(bitstate_in,25) s = A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200),25) s = A2 /\
              wordlist_from_memory(word_add bitstate_in (word 400),25) s = A3 /\
              wordlist_from_memory(word_add bitstate_in (word 600),25) s = A4 /\
              wordlist_from_memory(word_add bitstate_in (word 800),25) s = A5 /\
              wordlist_from_memory(word_add bitstate_in (word 1000),25) s = A6 /\
              wordlist_from_memory(word_add bitstate_in (word 1200),25) s = A7 /\
              wordlist_from_memory(word_add bitstate_in (word 1400),25) s = A8)
             (\s. read RIP s = word(pc + 0xbb3) /\
                  wordlist_from_memory(bitstate_in,25) s = keccak 24 A1 /\
                  wordlist_from_memory(word_add bitstate_in (word 200),25) s = keccak 24 A2 /\
                  wordlist_from_memory(word_add bitstate_in (word 400),25) s = keccak 24 A3 /\
                  wordlist_from_memory(word_add bitstate_in (word 600),25) s = keccak 24 A4 /\
                  wordlist_from_memory(word_add bitstate_in (word 800),25) s = keccak 24 A5 /\
                  wordlist_from_memory(word_add bitstate_in (word 1000),25) s = keccak 24 A6 /\
                  wordlist_from_memory(word_add bitstate_in (word 1200),25) s = keccak 24 A7 /\
                  wordlist_from_memory(word_add bitstate_in (word 1400),25) s = keccak 24 A8)
           (MAYCHANGE [RIP; RAX; RSI] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17; ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23; ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes (bitstate_in, 1600)])`,
  REWRITE_TAC
   [SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    C_ARGUMENTS; NONOVERLAPPING_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC
   [`rc_pointer:int64`;`bitstate_in:int64`;
    `A1:int64 list`;`A2:int64 list`;`A3:int64 list`;`A4:int64 list`;
    `A5:int64 list`;`A6:int64 list`;`A7:int64 list`;`A8:int64 list`;`pc:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC
   `LENGTH(A1:int64 list)=25 /\ LENGTH(A2:int64 list)=25 /\
    LENGTH(A3:int64 list)=25 /\ LENGTH(A4:int64 list)=25 /\
    LENGTH(A5:int64 list)=25 /\ LENGTH(A6:int64 list)=25 /\
    LENGTH(A7:int64 list)=25 /\ LENGTH(A8:int64 list)=25`
  THENL [ALL_TAC;
    ENSURES_INIT_TAC "s0" THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:int64 list->num`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]] THEN

  (*** Set up the loop invariant ***)

  ENSURES_WHILE_PAUP_TAC `0` `24` `pc + 0x3ff` `pc + 0x7b2`
  `\i s.
      (read RAX s = word i /\
       read RDI s = bitstate_in /\
       read RSI s = word_add rc_pointer (word (8 * i)) /\
       wordlist_from_memory(rc_pointer,24) s = round_constants /\
       [read ZMM0 s; read ZMM1 s; read ZMM2 s; read ZMM3 s; read ZMM4 s;
        read ZMM5 s; read ZMM6 s; read ZMM7 s; read ZMM8 s; read ZMM9 s;
        read ZMM10 s; read ZMM11 s; read ZMM12 s; read ZMM13 s; read ZMM14 s;
        read ZMM15 s; read ZMM16 s; read ZMM17 s; read ZMM18 s; read ZMM19 s;
        read ZMM20 s; read ZMM21 s; read ZMM22 s; read ZMM23 s; read ZMM24 s] =
         ((MAP2 word_join
            ((MAP2 word_join
               ((MAP2 word_join (keccak i A8) (keccak i A7)):int128 list)
               ((MAP2 word_join (keccak i A6) (keccak i A5)):int128 list)):int256 list)
            ((MAP2 word_join
               ((MAP2 word_join (keccak i A4) (keccak i A3)):int128 list)
               ((MAP2 word_join (keccak i A2) (keccak i A1)):int128 list)):int256 list)):int512 list)) /\
      (read ZF s <=> i = 24)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial holding of the invariant ***)

    REWRITE_TAC[ARITH_RULE `8 * 0 = 0`; WORD_ADD_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ENSURES_INIT_TAC "s0" THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (bitstate_in,8 * 200)) s0` THEN
    MEMORY_512_FROM_64_TAC "bitstate_in" 0 3 THEN
    MEMORY_512_FROM_64_TAC "bitstate_in" 200 3 THEN
    MEMORY_512_FROM_64_TAC "bitstate_in" 400 3 THEN
    MEMORY_512_FROM_64_TAC "bitstate_in" 600 3 THEN
    MEMORY_512_FROM_64_TAC "bitstate_in" 800 3 THEN
    MEMORY_512_FROM_64_TAC "bitstate_in" 1000 3 THEN
    MEMORY_512_FROM_64_TAC "bitstate_in" 1200 3 THEN
    MEMORY_512_FROM_64_TAC "bitstate_in" 1400 3 THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN
    REPEAT STRIP_TAC THEN
    X86_ABBREV_STEPS_TAC SHA3_KECCAK8_F1600_AVX512_EXEC (1--144) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CHANGED_TAC(EXPAND_TAC "A1") THEN
    CHANGED_TAC(EXPAND_TAC "A2") THEN
    CHANGED_TAC(EXPAND_TAC "A3") THEN
    CHANGED_TAC(EXPAND_TAC "A4") THEN
    CHANGED_TAC(EXPAND_TAC "A5") THEN
    CHANGED_TAC(EXPAND_TAC "A6") THEN
    CHANGED_TAC(EXPAND_TAC "A7") THEN
    CHANGED_TAC(EXPAND_TAC "A8") THEN
    REWRITE_TAC[keccak; MAP2; CONS_11] THEN
    TRANSPOSE_BITBLAST;

    (*** Preservation of the invariant including end condition code ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[round_constants] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    MP_TAC(ISPECL [`A1:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A2:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A3:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A4:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A5:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A6:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A7:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A8:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[CONS_11] THEN
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
    SUBGOAL_THEN
     `read (memory :> bytes64(word_add rc_pointer (word(8 * i)))) s0 =
      EL i round_constants`
    ASSUME_TAC THENL
     [UNDISCH_TAC `i < 24` THEN SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[round_constants; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    X86_ABBREV_STEPS_TAC SHA3_KECCAK8_F1600_AVX512_EXEC (1--144) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[WORD_ADD];
      CONV_TAC WORD_RULE;
      (* the vpternlogq truth-table formulas in the stepped chain: theta's
         (imm 0x96) is a 3-way XOR, chi's (imm 0xd2) is a ^^ (~~b && c) *)
      RULE_ASSUM_TAC(REWRITE_RULE[
        WORD_BITWISE_RULE
         `!a b c:N word. (~~a && ~~b && c) || (~~a && b && ~~c) ||
                         (a && ~~b && ~~c) || (a && b && c) = a ^^ b ^^ c`;
        WORD_BITWISE_RULE
         `!a b c:N word. (~~a && ~~b && c) || (a && ~~b && ~~c) ||
                         (a && b && ~~c) || (a && b && c) = a ^^ (~~b && c)`]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MAP2; CONS_11]) THEN
      REWRITE_TAC[keccak; keccak_round] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[MAP2; CONS_11] THEN
      SUBLANE_BITBLAST;
      REWRITE_TAC[WORD_BLAST `word_add x (word 18446744073709551593):int64 =
                              word_sub x (word 23)`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
      REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT; ARITH_RULE `23 < 2 EXP 64`] THEN
      CONJ_TAC THENL [UNDISCH_TAC `i < 24` THEN ARITH_TAC; ARITH_TAC]];

    (*** The trivial loop-back goal ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC SHA3_KECCAK8_F1600_AVX512_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The tail of un-transpose and writeback ***)

    ABBREV_TAC `B1 = keccak 24 A1` THEN ABBREV_TAC `B2 = keccak 24 A2` THEN
    ABBREV_TAC `B3 = keccak 24 A3` THEN ABBREV_TAC `B4 = keccak 24 A4` THEN
    ABBREV_TAC `B5 = keccak 24 A5` THEN ABBREV_TAC `B6 = keccak 24 A6` THEN
    ABBREV_TAC `B7 = keccak 24 A7` THEN ABBREV_TAC `B8 = keccak 24 A8` THEN
    SUBGOAL_THEN
      `LENGTH(B1:int64 list)=25 /\ LENGTH(B2:int64 list)=25 /\
       LENGTH(B3:int64 list)=25 /\ LENGTH(B4:int64 list)=25 /\
       LENGTH(B5:int64 list)=25 /\ LENGTH(B6:int64 list)=25 /\
       LENGTH(B7:int64 list)=25 /\ LENGTH(B8:int64 list)=25`
      STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["B1";"B2";"B3";"B4";"B5";"B6";"B7";"B8"] THEN
      ASM_MESON_TAC[LENGTH_KECCAK]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_EQ_25]) THEN
    REPEAT(FIRST_X_ASSUM(fun th ->
       let l,r = dest_eq(concl th) in
       if is_var l && List.mem (fst(dest_var l))
            ["B1";"B2";"B3";"B4";"B5";"B6";"B7";"B8"]
       then SUBST_ALL_TAC th else failwith "keep")) THEN
    REWRITE_TAC[MAP2; CONS_11] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_ABBREV_STEPS_TAC SHA3_KECCAK8_F1600_AVX512_EXEC (1--145) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (can (term_match [] `read qqq s:int512 = xxx`) o concl))) THEN
    ENSURES_FINAL_STATE_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ASM_REWRITE_TAC[WORD_SUBWORD_JOIN_EXTRACT_64; WORD_SUBWORD_JOIN_EXTRACT_128;
                    CONS_11] THEN
    TRANSPOSE_BITBLAST]);;

let SHA3_KECCAK8_F1600_AVX512_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!rc_pointer:int64 bitstate_in:int64 A1 A2 A3 A4 A5 A6 A7 A8 pc stackpointer returnaddress.
     nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_tmc) (bitstate_in, 1600) /\
     nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_tmc) (rc_pointer, 192) /\
     nonoverlapping (bitstate_in, 1600) (rc_pointer, 192) /\
     nonoverlapping (stackpointer, 8) (bitstate_in, 1600)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) sha3_keccak8_f1600_avx512_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [bitstate_in; rc_pointer] s /\
               wordlist_from_memory(rc_pointer,24) s = round_constants /\
               wordlist_from_memory(bitstate_in,25) s = A1 /\
               wordlist_from_memory(word_add bitstate_in (word 200),25) s = A2 /\
               wordlist_from_memory(word_add bitstate_in (word 400),25) s = A3 /\
               wordlist_from_memory(word_add bitstate_in (word 600),25) s = A4 /\
               wordlist_from_memory(word_add bitstate_in (word 800),25) s = A5 /\
               wordlist_from_memory(word_add bitstate_in (word 1000),25) s = A6 /\
               wordlist_from_memory(word_add bitstate_in (word 1200),25) s = A7 /\
               wordlist_from_memory(word_add bitstate_in (word 1400),25) s = A8)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               wordlist_from_memory(bitstate_in,25) s = keccak 24 A1 /\
               wordlist_from_memory(word_add bitstate_in (word 200),25) s = keccak 24 A2 /\
               wordlist_from_memory(word_add bitstate_in (word 400),25) s = keccak 24 A3 /\
               wordlist_from_memory(word_add bitstate_in (word 600),25) s = keccak 24 A4 /\
               wordlist_from_memory(word_add bitstate_in (word 800),25) s = keccak 24 A5 /\
               wordlist_from_memory(word_add bitstate_in (word 1000),25) s = keccak 24 A6 /\
               wordlist_from_memory(word_add bitstate_in (word 1200),25) s = keccak 24 A7 /\
               wordlist_from_memory(word_add bitstate_in (word 1400),25) s = keccak 24 A8)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes (bitstate_in, 1600)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_PROMOTE_RETURN_NOSTACK_TAC sha3_keccak8_f1600_avx512_tmc
    (CONV_RULE TWEAK_CONV SHA3_KECCAK8_F1600_AVX512_CORRECT));;

let SHA3_KECCAK8_F1600_AVX512_SUBROUTINE_CORRECT = time prove
 (`!rc_pointer:int64 bitstate_in:int64 A1 A2 A3 A4 A5 A6 A7 A8 pc stackpointer returnaddress.
     nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_mc) (bitstate_in, 1600) /\
     nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_mc) (rc_pointer, 192) /\
     nonoverlapping (bitstate_in, 1600) (rc_pointer, 192) /\
     nonoverlapping (stackpointer, 8) (bitstate_in, 1600)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) sha3_keccak8_f1600_avx512_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [bitstate_in; rc_pointer] s /\
               wordlist_from_memory(rc_pointer,24) s = round_constants /\
               wordlist_from_memory(bitstate_in,25) s = A1 /\
               wordlist_from_memory(word_add bitstate_in (word 200),25) s = A2 /\
               wordlist_from_memory(word_add bitstate_in (word 400),25) s = A3 /\
               wordlist_from_memory(word_add bitstate_in (word 600),25) s = A4 /\
               wordlist_from_memory(word_add bitstate_in (word 800),25) s = A5 /\
               wordlist_from_memory(word_add bitstate_in (word 1000),25) s = A6 /\
               wordlist_from_memory(word_add bitstate_in (word 1200),25) s = A7 /\
               wordlist_from_memory(word_add bitstate_in (word 1400),25) s = A8)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               wordlist_from_memory(bitstate_in,25) s = keccak 24 A1 /\
               wordlist_from_memory(word_add bitstate_in (word 200),25) s = keccak 24 A2 /\
               wordlist_from_memory(word_add bitstate_in (word 400),25) s = keccak 24 A3 /\
               wordlist_from_memory(word_add bitstate_in (word 600),25) s = keccak 24 A4 /\
               wordlist_from_memory(word_add bitstate_in (word 800),25) s = keccak 24 A5 /\
               wordlist_from_memory(word_add bitstate_in (word 1000),25) s = keccak 24 A6 /\
               wordlist_from_memory(word_add bitstate_in (word 1200),25) s = keccak 24 A7 /\
               wordlist_from_memory(word_add bitstate_in (word 1400),25) s = keccak 24 A8)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes (bitstate_in, 1600)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
    (CONV_RULE TWEAK_CONV SHA3_KECCAK8_F1600_AVX512_NOIBT_SUBROUTINE_CORRECT)));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let sha3_keccak8_f1600_avx512_windows_mc = define_from_elf
  "sha3_keccak8_f1600_avx512_windows_mc" "x86/sha3/sha3_keccak8_f1600_avx512.obj";;

let sha3_keccak8_f1600_avx512_windows_tmc = define_trimmed "sha3_keccak8_f1600_avx512_windows_tmc" sha3_keccak8_f1600_avx512_windows_mc;;

let sha3_keccak8_f1600_avx512_windows_tmc_EXEC = X86_MK_EXEC_RULE sha3_keccak8_f1600_avx512_windows_tmc;;

let SHA3_KECCAK8_F1600_AVX512_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!rc_pointer:int64 bitstate_in:int64 A1 A2 A3 A4 A5 A6 A7 A8 pc:num stackpointer:int64 returnaddress.
  nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_windows_tmc) (word_sub stackpointer (word 0xb0), 0xb0) /\
  nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_windows_tmc) (bitstate_in, 1600) /\
  nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_windows_tmc) (rc_pointer, 192) /\
  nonoverlapping (bitstate_in, 1600) (rc_pointer, 192) /\
  nonoverlapping (bitstate_in, 1600) (word_sub stackpointer (word 0xb0), 0xb0 + 8) /\
  nonoverlapping (word_sub stackpointer (word 0xb0), 0xb0) (rc_pointer, 192)
  ==> ensures x86
         (\s. bytes_loaded s (word pc) sha3_keccak8_f1600_avx512_windows_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS[bitstate_in; rc_pointer] s /\
              wordlist_from_memory(rc_pointer, 24) s = round_constants /\
              wordlist_from_memory(bitstate_in, 25) s = A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200), 25) s = A2 /\
              wordlist_from_memory(word_add bitstate_in (word 400), 25) s = A3 /\
              wordlist_from_memory(word_add bitstate_in (word 600), 25) s = A4 /\
              wordlist_from_memory(word_add bitstate_in (word 800), 25) s = A5 /\
              wordlist_from_memory(word_add bitstate_in (word 1000), 25) s = A6 /\
              wordlist_from_memory(word_add bitstate_in (word 1200), 25) s = A7 /\
              wordlist_from_memory(word_add bitstate_in (word 1400), 25) s = A8)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              wordlist_from_memory(bitstate_in, 25) s = keccak 24 A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200), 25) s = keccak 24 A2 /\
              wordlist_from_memory(word_add bitstate_in (word 400), 25) s = keccak 24 A3 /\
              wordlist_from_memory(word_add bitstate_in (word 600), 25) s = keccak 24 A4 /\
              wordlist_from_memory(word_add bitstate_in (word 800), 25) s = keccak 24 A5 /\
              wordlist_from_memory(word_add bitstate_in (word 1000), 25) s = keccak 24 A6 /\
              wordlist_from_memory(word_add bitstate_in (word 1200), 25) s = keccak 24 A7 /\
              wordlist_from_memory(word_add bitstate_in (word 1400), 25) s = keccak 24 A8)
         (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes (bitstate_in, 1600);
                     memory :> bytes(word_sub stackpointer (word 0xb0), 0xb0)])`,
  REPLICATE_TAC 11 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 0xb0 THEN
  REWRITE_TAC[fst sha3_keccak8_f1600_avx512_windows_tmc_EXEC] THEN
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

  REWRITE_TAC[WORDLIST_FROM_MEMORY; DIMINDEX_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC sha3_keccak8_f1600_avx512_windows_tmc_EXEC (1--15) THEN

  MP_TAC(SPECL
   [`rc_pointer:int64`; `bitstate_in:int64`;
    `A1:int64 list`; `A2:int64 list`; `A3:int64 list`; `A4:int64 list`;
    `A5:int64 list`; `A6:int64 list`; `A7:int64 list`; `A8:int64 list`;
    `pc + 92`]
   SHA3_KECCAK8_F1600_AVX512_CORRECT) THEN
  ANTS_TAC THENL [REPEAT NONOVERLAPPING_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY; DIMINDEX_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN

  X86_BIGSTEP_TAC sha3_keccak8_f1600_avx512_windows_tmc_EXEC "s16" THENL
  [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
   (BYTES_LOADED_SUBPROGRAM_RULE sha3_keccak8_f1600_avx512_windows_tmc
   (REWRITE_RULE[BUTLAST_CLAUSES]
    (AP_TERM `BUTLAST:byte list->byte list` sha3_keccak8_f1600_avx512_tmc))
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

  X86_STEPS_TAC sha3_keccak8_f1600_avx512_windows_tmc_EXEC (17--30) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let SHA3_KECCAK8_F1600_AVX512_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!rc_pointer:int64 bitstate_in:int64 A1 A2 A3 A4 A5 A6 A7 A8 pc:num stackpointer:int64 returnaddress.
  nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_windows_mc) (word_sub stackpointer (word 0xb0), 0xb0) /\
  nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_windows_mc) (bitstate_in, 1600) /\
  nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_windows_mc) (rc_pointer, 192) /\
  nonoverlapping (bitstate_in, 1600) (rc_pointer, 192) /\
  nonoverlapping (bitstate_in, 1600) (word_sub stackpointer (word 0xb0), 0xb0 + 8) /\
  nonoverlapping (word_sub stackpointer (word 0xb0), 0xb0) (rc_pointer, 192)
  ==> ensures x86
         (\s. bytes_loaded s (word pc) sha3_keccak8_f1600_avx512_windows_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS[bitstate_in; rc_pointer] s /\
              wordlist_from_memory(rc_pointer, 24) s = round_constants /\
              wordlist_from_memory(bitstate_in, 25) s = A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200), 25) s = A2 /\
              wordlist_from_memory(word_add bitstate_in (word 400), 25) s = A3 /\
              wordlist_from_memory(word_add bitstate_in (word 600), 25) s = A4 /\
              wordlist_from_memory(word_add bitstate_in (word 800), 25) s = A5 /\
              wordlist_from_memory(word_add bitstate_in (word 1000), 25) s = A6 /\
              wordlist_from_memory(word_add bitstate_in (word 1200), 25) s = A7 /\
              wordlist_from_memory(word_add bitstate_in (word 1400), 25) s = A8)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              wordlist_from_memory(bitstate_in, 25) s = keccak 24 A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200), 25) s = keccak 24 A2 /\
              wordlist_from_memory(word_add bitstate_in (word 400), 25) s = keccak 24 A3 /\
              wordlist_from_memory(word_add bitstate_in (word 600), 25) s = keccak 24 A4 /\
              wordlist_from_memory(word_add bitstate_in (word 800), 25) s = keccak 24 A5 /\
              wordlist_from_memory(word_add bitstate_in (word 1000), 25) s = keccak 24 A6 /\
              wordlist_from_memory(word_add bitstate_in (word 1200), 25) s = keccak 24 A7 /\
              wordlist_from_memory(word_add bitstate_in (word 1400), 25) s = keccak 24 A8)
         (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes (bitstate_in, 1600);
                     memory :> bytes(word_sub stackpointer (word 0xb0), 0xb0)])`,
 let TWEAK_CONV = ONCE_DEPTH_CONV NUM_ADD_CONV THENC
                   ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
    (CONV_RULE TWEAK_CONV SHA3_KECCAK8_F1600_AVX512_NOIBT_WINDOWS_SUBROUTINE_CORRECT)));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "sha3_keccak8_f1600_avx512" subroutine_signatures)
    (REWRITE_RULE[SOME_FLAGS] SHA3_KECCAK8_F1600_AVX512_CORRECT)
    SHA3_KECCAK8_F1600_AVX512_EXEC;;

let SHA3_KECCAK8_F1600_AVX512_SAFE = time prove
 (`exists f_events.
    forall e rc_pointer bitstate_in pc.
        nonoverlapping (word pc,2996) (bitstate_in,1600) /\
        nonoverlapping (word pc,2996) (rc_pointer,192) /\
        nonoverlapping (bitstate_in,1600) (rc_pointer,192)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) (BUTLAST sha3_keccak8_f1600_avx512_tmc) /\
                 read RIP s = word pc /\
                 C_ARGUMENTS [bitstate_in; rc_pointer] s /\
                 read events s = e)
            (\s.
                 read RIP s = word (pc + 2995) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc_pointer bitstate_in pc /\
                      memaccess_inbounds e2 [bitstate_in,1600; rc_pointer,192]
                      [bitstate_in,1600]))
            (MAYCHANGE [RIP; RAX; RSI] ,,
             MAYCHANGE
             [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9;
              ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17; ZMM18;
              ZMM19; ZMM20; ZMM21; ZMM22; ZMM23; ZMM24; ZMM25; ZMM26; ZMM27;
              ZMM28; ZMM29; ZMM30; ZMM31] ,,
             MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes (bitstate_in,1600)])`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars SHA3_KECCAK8_F1600_AVX512_EXEC);;

let SHA3_KECCAK8_F1600_AVX512_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e rc_pointer:int64 bitstate_in:int64 pc stackpointer returnaddress.
          nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_tmc) (bitstate_in, 1600) /\
          nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_tmc) (rc_pointer, 192) /\
          nonoverlapping (bitstate_in, 1600) (rc_pointer, 192) /\
          nonoverlapping (stackpointer, 8) (bitstate_in, 1600)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) sha3_keccak8_f1600_avx512_tmc /\
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
                           [bitstate_in,1600; rc_pointer,192; stackpointer,8]
                           [bitstate_in,1600; stackpointer,8]))
               (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC sha3_keccak8_f1600_avx512_tmc
    SHA3_KECCAK8_F1600_AVX512_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let SHA3_KECCAK8_F1600_AVX512_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e rc_pointer:int64 bitstate_in:int64 pc stackpointer returnaddress.
          nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_mc) (bitstate_in, 1600) /\
          nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_mc) (rc_pointer, 192) /\
          nonoverlapping (bitstate_in, 1600) (rc_pointer, 192) /\
          nonoverlapping (stackpointer, 8) (bitstate_in, 1600)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) sha3_keccak8_f1600_avx512_mc /\
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
                           [bitstate_in,1600; rc_pointer,192; stackpointer,8]
                           [bitstate_in,1600; stackpointer,8]))
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE SHA3_KECCAK8_F1600_AVX512_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof of Windows ABI version.             *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK8_F1600_AVX512_NOIBT_WINDOWS_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e rc_pointer:int64 bitstate_in:int64 pc:num stackpointer:int64 returnaddress.
  nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_windows_tmc) (word_sub stackpointer (word 0xb0), 0xb0) /\
  nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_windows_tmc) (bitstate_in, 1600) /\
  nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_windows_tmc) (rc_pointer, 192) /\
  nonoverlapping (bitstate_in, 1600) (rc_pointer, 192) /\
  nonoverlapping (bitstate_in, 1600) (word_sub stackpointer (word 0xb0), 0xb0 + 8) /\
  nonoverlapping (word_sub stackpointer (word 0xb0), 0xb0) (rc_pointer, 192)
  ==> ensures x86
         (\s. bytes_loaded s (word pc) sha3_keccak8_f1600_avx512_windows_tmc /\
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
                      [bitstate_in,1600; rc_pointer,192;
                       word_sub stackpointer (word 0xb0),0xb0 + 8]
                      [bitstate_in,1600; word_sub stackpointer (word 0xb0),0xb0]))
         (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes (bitstate_in, 1600);
                     memory :> bytes(word_sub stackpointer (word 0xb0), 0xb0)])`,
  ASSUME_CALLEE_SAFETY_TAC SHA3_KECCAK8_F1600_AVX512_SAFE "H_subth" THEN
  META_EXISTS_TAC THEN
  REPLICATE_TAC 4 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 0xb0 THEN
  REWRITE_TAC[fst sha3_keccak8_f1600_avx512_windows_tmc_EXEC] THEN
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

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC sha3_keccak8_f1600_avx512_windows_tmc_EXEC (1--15) THEN

  W(fun (asl,w) ->
    let current_events = filter_map (fun (_,ath) -> let t = concl ath in
      if is_eq t && is_read_events (lhs t) then Some (rhs t)
      else None) asl in
    if length current_events <> 1
    then failwith "More than 'read events .. = ..?'"
    else
      REMOVE_THEN "H_subth"
        (MP_TAC o SPECL [hd current_events; `rc_pointer:int64`; `bitstate_in:int64`;
                         `pc + 92`])) THEN
  ASM_REWRITE_TAC[C_ARGUMENTS] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN

  X86_BIGSTEP_TAC sha3_keccak8_f1600_avx512_windows_tmc_EXEC "s16" THENL
  [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
   (BYTES_LOADED_SUBPROGRAM_RULE sha3_keccak8_f1600_avx512_windows_tmc
   (REWRITE_RULE[BUTLAST_CLAUSES]
    (AP_TERM `BUTLAST:byte list->byte list` sha3_keccak8_f1600_avx512_tmc))
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

  X86_STEPS_TAC sha3_keccak8_f1600_avx512_windows_tmc_EXEC (17--30) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ DISCHARGE_SAFETY_PROPERTY_TAC; ALL_TAC ] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let SHA3_KECCAK8_F1600_AVX512_WINDOWS_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e rc_pointer:int64 bitstate_in:int64 pc:num stackpointer:int64 returnaddress.
  nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_windows_mc) (word_sub stackpointer (word 0xb0), 0xb0) /\
  nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_windows_mc) (bitstate_in, 1600) /\
  nonoverlapping (word pc, LENGTH sha3_keccak8_f1600_avx512_windows_mc) (rc_pointer, 192) /\
  nonoverlapping (bitstate_in, 1600) (rc_pointer, 192) /\
  nonoverlapping (bitstate_in, 1600) (word_sub stackpointer (word 0xb0), 0xb0 + 8) /\
  nonoverlapping (word_sub stackpointer (word 0xb0), 0xb0) (rc_pointer, 192)
  ==> ensures x86
         (\s. bytes_loaded s (word pc) sha3_keccak8_f1600_avx512_windows_mc /\
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
                      [bitstate_in,1600; rc_pointer,192;
                       word_sub stackpointer (word 0xb0),0xb0 + 8]
                      [bitstate_in,1600; word_sub stackpointer (word 0xb0),0xb0]))
         (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes (bitstate_in, 1600);
                     memory :> bytes(word_sub stackpointer (word 0xb0), 0xb0)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE SHA3_KECCAK8_F1600_AVX512_NOIBT_WINDOWS_SUBROUTINE_SAFE));;
