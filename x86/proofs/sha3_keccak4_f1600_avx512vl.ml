(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/keccak_spec.ml";;

(**** print_literal_from_elf "x86/sha3/sha3_keccak4_f1600_avx512vl.o";;
****)

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
  0x48; 0xc7; 0xc0; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm32 (word 0)) *)
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
  0x62; 0x62; 0xfd; 0x28; 0x59; 0x2e;
                           (* VPBROADCASTQ (%_% ymm29) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x83; 0xc6; 0x08;  (* ADD (% rsi) (Imm8 (word 8)) *)
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
  0x48; 0x83; 0xc0; 0x01;  (* ADD (% rax) (Imm8 (word 1)) *)
  0x48; 0x83; 0xf8; 0x18;  (* CMP (% rax) (Imm8 (word 24)) *)
  0x0f; 0x85; 0x47; 0xfc; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294966343)) *)
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

let sha3_keccak4_f1600_avx512vl_tmc = define_trimmed "sha3_keccak4_f1600_avx512vl_tmc" sha3_keccak4_f1600_avx512vl_mc;;

let SHA3_KECCAK4_F1600_AVX512VL_EXEC = X86_MK_CORE_EXEC_RULE sha3_keccak4_f1600_avx512vl_tmc;;

(* Symbolic execution for the ZMM operand view with abbreviation:
   X86_ABBREV_STEPS_TAC execth ns steps the instructions ns one at a time;
   after each step it collapses word_zx (word_zx _) round-trips (VEX operands
   read through zerotop_256 as word_zx(read ZMMk)) and abbreviates the 256-bit
   value e of each new `read ZMMk sN = word_zx e` to a fresh variable, so the
   stepped terms never nest. *)
let X86_ABBREV_STEPS_TAC =
  let ZX_COLLAPSE_CONV = SIMP_CONV
   [WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128; DIMINDEX_256;
    DIMINDEX_512; ARITH] in
  let is_zx_redex t =
    match t with
      Comb(Const("word_zx",_),Comb(Const("word_zx",_),_)) -> true
    | _ -> false in
  let collapse_tac =
    RULE_ASSUM_TAC(fun th ->
      if can (find_term is_zx_redex) (concl th)
      then CONV_RULE ZX_COLLAPSE_CONV th else th) in
  let abbrev_tac sname =
    let st = mk_var(sname,`:x86state`) in
    let is_new_zmm_read t =
      match t with
        Comb(Comb(Const("read",_),Const(n,_)),s) ->
          s = st && String.length n >= 3 && String.sub n 0 3 = "ZMM"
      | _ -> false in
    let unzx t =
      if is_comb t && name_of(rator t) = "word_zx" then rand t else t in
    (* the 256-bit value e of `read ZMMk sN = word_zx e`, unless it is a
       variable or word_zx of one (a ghost read) *)
    let target th =
      let c = concl th in
      if not(is_eq c && is_new_zmm_read(lhand c)) then failwith "target" else
      let e = unzx(rand c) in
      if is_var(unzx e) then failwith "target" else e in
    W(fun (asl,_) ->
      MAP_EVERY (fun t -> ABBREV_TAC(mk_eq(genvar(type_of t),t)))
                (mapfilter (target o snd) asl)) in
  fun execth ns ->
    MAP_EVERY (fun n -> X86_STEPS_TAC execth [n] THEN collapse_tac THEN
                        abbrev_tac ("s"^string_of_int n)) ns;;

(* Discharge a conjunction of 256-bit lane equations.  Each lane is split into
   its four 64-bit sublanes (one per state).  Every equation of the
   abbreviation chain and of the ghost/invariant facts is projected to each
   sublane by pushing word_subword inward; the goal is rewritten with these,
   the assumptions are dropped, and the first sublane is closed bit by bit
   and reused (by matching) for the others. *)
let SUBLANE_BITBLAST : tactic =
  let SPLIT_SUBLANES = prove
   (`!x y:int256.
       x = y <=>
       (word_subword x (0,64)):int64 = word_subword y (0,64) /\
       (word_subword x (64,64)):int64 = word_subword y (64,64) /\
       (word_subword x (128,64)):int64 = word_subword y (128,64) /\
       (word_subword x (192,64)):int64 = word_subword y (192,64)`,
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
      REWRITE_TAC(flat(map (fun j -> mapfilter (proj_lane j) eqs) (0--3)))) THEN
   POP_ASSUM_LIST(K ALL_TAC) THEN
   (* prove the state-1 sublane once, generalise it over its free variables,
      and use the result for all four sublanes *)
   W(fun (_,w) ->
      let th = prove(hd(conjuncts w), PERBIT_BITBLAST) in
      REPEAT CONJ_TAC THEN MATCH_ACCEPT_TAC(GENL (frees(concl th)) th)));;

let SHA3_KECCAK4_F1600_AVX512VL_CORRECT = prove
  (`!rc_pointer:int64 bitstate_in:int64 A1 A2 A3 A4 pc:num.
    nonoverlapping (word pc, 0x838) (bitstate_in, 800) /\
    nonoverlapping (word pc, 0x838) (rc_pointer, 192) /\
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
             (\s. read RIP s = word(pc + 0x837) /\
                  wordlist_from_memory(bitstate_in,25) s = keccak 24 A1 /\
                  wordlist_from_memory(word_add bitstate_in (word 200),25) s = keccak 24 A2 /\
                  wordlist_from_memory(word_add bitstate_in (word 400),25) s = keccak 24 A3 /\
                  wordlist_from_memory(word_add bitstate_in (word 600),25) s = keccak 24 A4)
           (MAYCHANGE [RIP; RAX; RSI] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17; ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23; ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes (bitstate_in, 800)])`,
  REWRITE_TAC
   [SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    C_ARGUMENTS; NONOVERLAPPING_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC
   [`rc_pointer:int64`;`bitstate_in:int64`;
    `A1:int64 list`;`A2:int64 list`;
    `A3:int64 list`;`A4:int64 list`;`pc:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC
   `LENGTH(A1:int64 list)=25 /\ LENGTH(A2:int64 list)=25 /\
    LENGTH(A3:int64 list)=25 /\ LENGTH(A4:int64 list)=25`
  THENL [ALL_TAC;
    ENSURES_INIT_TAC "s0" THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:int64 list->num`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]] THEN

  (*** Set up the loop invariant ***)

  ENSURES_WHILE_PAUP_TAC `0` `24` `pc + 0x241` `pc + 0x5f4`
  `\i s.
      (read RAX s = word i /\
       read RDI s = bitstate_in /\
       read RSI s = word_add rc_pointer (word (8 * i)) /\
       wordlist_from_memory(rc_pointer,24) s = round_constants /\
       [read YMM0 s; read YMM1 s; read YMM2 s; read YMM3 s; read YMM4 s; read YMM5 s; read YMM6 s; read YMM7 s; read YMM8 s; read YMM9 s; read YMM10 s; read YMM11 s; read YMM12 s; read YMM13 s; read YMM14 s; read YMM15 s; read YMM16 s; read YMM17 s; read YMM18 s; read YMM19 s; read YMM20 s; read YMM21 s; read YMM22 s; read YMM23 s; read YMM24 s] =
         (MAP2 word_join
            ((MAP2 word_join (keccak i A4) (keccak i A3)):int128 list)
            ((MAP2 word_join (keccak i A2) (keccak i A1)):int128 list)):int256 list) /\
      (read ZF s <=> i = 24)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial holding of the invariant ***)

    REWRITE_TAC[ARITH_RULE `8 * 0 = 0`; WORD_ADD_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ENSURES_INIT_TAC "s0" THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (bitstate_in,8 * 100)) s0` THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 0 6 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 200 6 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 400 6 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 600 6 THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN
    REPEAT STRIP_TAC THEN
    X86_STEPS_TAC SHA3_KECCAK4_F1600_AVX512VL_EXEC (1--78) THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[YMM0; YMM1; YMM2; YMM3; YMM4; YMM5; YMM6; YMM7; YMM8; YMM9;
                YMM10; YMM11; YMM12; YMM13; YMM14; YMM15; YMM16; YMM17; YMM18;
                YMM19; YMM20; YMM21; YMM22; YMM23; YMM24; READ_ZEROTOP_256] THEN
    ASM_REWRITE_TAC[] THEN
    CHANGED_TAC(EXPAND_TAC "A1") THEN
    CHANGED_TAC(EXPAND_TAC "A2") THEN
    CHANGED_TAC(EXPAND_TAC "A3") THEN
    CHANGED_TAC(EXPAND_TAC "A4") THEN
    REWRITE_TAC[keccak; MAP2; CONS_11] THEN
    BITBLAST_TAC;

    (*** Preservation of the invariant including end condition code ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[round_constants] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    MP_TAC(ISPECL [`A1:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A2:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A3:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A4:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
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

    SUBGOAL_THEN
     `read (memory :> bytes64(word_add rc_pointer (word(8 * i)))) s0 =
      EL i round_constants`
    ASSUME_TAC THENL
     [UNDISCH_TAC `i < 24` THEN SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[round_constants; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]; ALL_TAC] THEN

    X86_ABBREV_STEPS_TAC SHA3_KECCAK4_F1600_AVX512VL_EXEC (1--144) THEN
    ENSURES_FINAL_STATE_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAP2; CONS_11]) THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[WORD_ADD];
      CONV_TAC WORD_RULE;
      REWRITE_TAC[keccak; keccak_round] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      (* the vpternlogq truth-table formulas in the stepped chain: theta's
         (imm 0x96) is a 3-way XOR, chi's (imm 0xd2) is a ^^ (~~b && c) *)
      RULE_ASSUM_TAC(REWRITE_RULE[
        WORD_BITWISE_RULE
         `!a b c:N word. (~~a && ~~b && c) || (~~a && b && ~~c) ||
                         (a && ~~b && ~~c) || (a && b && c) = a ^^ b ^^ c`;
        WORD_BITWISE_RULE
         `!a b c:N word. (~~a && ~~b && c) || (a && ~~b && ~~c) ||
                         (a && b && ~~c) || (a && b && c) = a ^^ (~~b && c)`]) THEN
      REWRITE_TAC[MAP2; CONS_11;
        WORD_BITWISE_RULE
         `!a b c:N word. (~~a && ~~b && c) || (~~a && b && ~~c) ||
                         (a && ~~b && ~~c) || (a && b && c) = a ^^ b ^^ c`;
        WORD_BITWISE_RULE
         `!a b c:N word. (~~a && ~~b && c) || (a && ~~b && ~~c) ||
                         (a && b && ~~c) || (a && b && c) = a ^^ (~~b && c)`] THEN
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
    X86_STEPS_TAC SHA3_KECCAK4_F1600_AVX512VL_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The tail of un-transpose and writeback ***)

    MP_TAC(ISPECL [`A1:int64 list`; `24:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A2:int64 list`; `24:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A3:int64 list`; `24:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A4:int64 list`; `24:num`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[MAP2; CONS_11] THEN
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
    X86_STEPS_TAC SHA3_KECCAK4_F1600_AVX512VL_EXEC (1--79) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN
    ENSURES_FINAL_STATE_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ASM_REWRITE_TAC[WORD_SUBWORD_JOIN_EXTRACT_64; CONS_11] THEN
    BITBLAST_TAC]);;

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
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_PROMOTE_RETURN_NOSTACK_TAC sha3_keccak4_f1600_avx512vl_tmc
    (CONV_RULE TWEAK_CONV SHA3_KECCAK4_F1600_AVX512VL_CORRECT));;

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
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
    (CONV_RULE TWEAK_CONV SHA3_KECCAK4_F1600_AVX512VL_NOIBT_SUBROUTINE_CORRECT)));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let sha3_keccak4_f1600_avx512vl_windows_mc = define_from_elf
  "sha3_keccak4_f1600_avx512vl_windows_mc" "x86/sha3/sha3_keccak4_f1600_avx512vl.obj";;

let sha3_keccak4_f1600_avx512vl_windows_tmc = define_trimmed "sha3_keccak4_f1600_avx512vl_windows_tmc" sha3_keccak4_f1600_avx512vl_windows_mc;;

let sha3_keccak4_f1600_avx512vl_windows_tmc_EXEC = X86_MK_EXEC_RULE sha3_keccak4_f1600_avx512vl_windows_tmc;;

let SHA3_KECCAK4_F1600_AVX512VL_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!rc_pointer:int64 bitstate_in:int64 A1 A2 A3 A4 pc:num stackpointer:int64 returnaddress.
  nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_tmc) (word_sub stackpointer (word 0xb0), 0xb0) /\
  nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_tmc) (bitstate_in, 800) /\
  nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_tmc) (rc_pointer, 192) /\
  nonoverlapping (bitstate_in, 800) (rc_pointer, 192) /\
  nonoverlapping (bitstate_in, 800) (word_sub stackpointer (word 0xb0), 0xb0 + 8) /\
  nonoverlapping (word_sub stackpointer (word 0xb0), 0xb0) (rc_pointer, 192)
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
  REPLICATE_TAC 7 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 0xb0 THEN
  REWRITE_TAC[fst sha3_keccak4_f1600_avx512vl_windows_tmc_EXEC] THEN
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
  X86_STEPS_TAC sha3_keccak4_f1600_avx512vl_windows_tmc_EXEC (1--15) THEN

  MP_TAC(SPECL
   [`rc_pointer:int64`; `bitstate_in:int64`;
    `A1:int64 list`; `A2:int64 list`; `A3:int64 list`; `A4:int64 list`;
    `pc + 92`]
   SHA3_KECCAK4_F1600_AVX512VL_CORRECT) THEN
  ANTS_TAC THENL [REPEAT NONOVERLAPPING_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY; DIMINDEX_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN

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
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let SHA3_KECCAK4_F1600_AVX512VL_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!rc_pointer:int64 bitstate_in:int64 A1 A2 A3 A4 pc:num stackpointer:int64 returnaddress.
  nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_mc) (word_sub stackpointer (word 0xb0), 0xb0) /\
  nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_mc) (bitstate_in, 800) /\
  nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_mc) (rc_pointer, 192) /\
  nonoverlapping (bitstate_in, 800) (rc_pointer, 192) /\
  nonoverlapping (bitstate_in, 800) (word_sub stackpointer (word 0xb0), 0xb0 + 8) /\
  nonoverlapping (word_sub stackpointer (word 0xb0), 0xb0) (rc_pointer, 192)
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
        nonoverlapping (word pc,2104) (bitstate_in,800) /\
        nonoverlapping (word pc,2104) (rc_pointer,192) /\
        nonoverlapping (bitstate_in,800) (rc_pointer,192)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) (BUTLAST sha3_keccak4_f1600_avx512vl_tmc) /\
                 read RIP s = word pc /\
                 C_ARGUMENTS [bitstate_in; rc_pointer] s /\
                 read events s = e)
            (\s.
                 read RIP s = word (pc + 2103) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc_pointer bitstate_in pc /\
                      memaccess_inbounds e2 [bitstate_in,800; rc_pointer,192]
                      [bitstate_in,800]))
            (MAYCHANGE [RIP; RAX; RSI] ,,
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
  nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_tmc) (word_sub stackpointer (word 0xb0), 0xb0) /\
  nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_tmc) (bitstate_in, 800) /\
  nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_tmc) (rc_pointer, 192) /\
  nonoverlapping (bitstate_in, 800) (rc_pointer, 192) /\
  nonoverlapping (bitstate_in, 800) (word_sub stackpointer (word 0xb0), 0xb0 + 8) /\
  nonoverlapping (word_sub stackpointer (word 0xb0), 0xb0) (rc_pointer, 192)
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
  REPLICATE_TAC 4 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 0xb0 THEN
  REWRITE_TAC[fst sha3_keccak4_f1600_avx512vl_windows_tmc_EXEC] THEN
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
                         `pc + 92`])) THEN
  ASM_REWRITE_TAC[C_ARGUMENTS] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN

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
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ DISCHARGE_SAFETY_PROPERTY_TAC; ALL_TAC ] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let SHA3_KECCAK4_F1600_AVX512VL_WINDOWS_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e rc_pointer:int64 bitstate_in:int64 pc:num stackpointer:int64 returnaddress.
  nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_mc) (word_sub stackpointer (word 0xb0), 0xb0) /\
  nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_mc) (bitstate_in, 800) /\
  nonoverlapping (word pc, LENGTH sha3_keccak4_f1600_avx512vl_windows_mc) (rc_pointer, 192) /\
  nonoverlapping (bitstate_in, 800) (rc_pointer, 192) /\
  nonoverlapping (bitstate_in, 800) (word_sub stackpointer (word 0xb0), 0xb0 + 8) /\
  nonoverlapping (word_sub stackpointer (word 0xb0), 0xb0) (rc_pointer, 192)
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

