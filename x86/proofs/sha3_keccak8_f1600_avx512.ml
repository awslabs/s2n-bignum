(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 8-fold Keccak-f1600 using AVX-512 (full 512-bit ZMM, 8 lanes/register).    *)
(*                                                                           *)
(* Kernel = x86/sha3/sha3_keccak8_f1600_avx512.S, an s2n-vendored single-     *)
(* function form modelled on XKCP's public-domain (CC0) KeccakP-1600-times8-  *)
(* AVX512. It processes eight independent 200-byte Keccak states, one per     *)
(* 64-bit ZMM lane. The lane<->instance transpose (XKCP uses gather/scatter)  *)
(* is realised with a vpunpck/vshufi64x2 shuffle network so the object is     *)
(* gather-free; the round-constant table is a pointer argument (rsi). The     *)
(* per-round theta/rho/pi/chi/iota arithmetic is identical to the 4x          *)
(* avx512vl kernel widened ymm->zmm, so the round body mirrors                *)
(* x86/proofs/sha3_keccak4_f1600_avx512vl.ml exactly (25 ZMM reads, DEFAULT   *)
(* ZMM view). State register-resident in zmm0..zmm24; scratch zmm25..zmm31.   *)
(*                                                                           *)
(* C arguments: rdi = bitstate_in (8 states x 200 bytes = 1600), rsi = rc.    *)
(*                                                                           *)
(* STATUS: PROVED. Functional correctness of the full 24-round permutation    *)
(* over eight independent states is established: the round-body lemma          *)
(* SHA3_KECCAK8_F1600_AVX512_ROUND_CORRECT (scalar-lane per-bit discharge,     *)
(* cold-loads with axioms()=3, no cheats) + the top-level                      *)
(* SHA3_KECCAK8_F1600_AVX512_CORRECT (24-round loop, prologue/tail transpose   *)
(* discharged per-output-bit) + the SysV and Windows NOIBT/IBT SUBROUTINE      *)
(* wrappers, mirroring sha3_keccak4_f1600_avx512vl.ml. The .S assembles to a   *)
(* relocation-free object; every encoding decodes in the HOL x86 model         *)
(* (incl. EVEX.512 VINSERTI32X4/VEXTRACTI32X4 imm 1/2/3 and the Word512        *)
(* VMOVDQU64/VSHUFI64X2/VPROLQ/VPTERNLOGQ/VPBROADCASTQ forms), and the kernel  *)
(* is validated functionally against the scalar reference. The full-ZMM        *)
(* (8 lanes/register) BITBLAST blowup is avoided by the per-round ROUND_CORRECT *)
(* lemma (proved once, applied 24x by the loop) with scalar-lane projection +  *)
(* per-output-bit BITBLAST, rather than a monolithic 24-round blast.           *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/keccak_spec.ml";;

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
  0x41; 0xba; 0x18; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 24)) *)
  0x49; 0x89; 0xf3;        (* MOV (% r11) (% rsi) *)
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
  0x62; 0x42; 0xfd; 0x48; 0x59; 0x2b;
                           (* VPBROADCASTQ (%_% zmm29) (Memop Quadword (%% (r11,0))) *)
  0x49; 0x83; 0xc3; 0x08;  (* ADD (% r11) (Imm8 (word 8)) *)
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
  0x41; 0xff; 0xca;        (* DEC (% r10d) *)
  0x0f; 0x85; 0x4c; 0xfc; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294966348)) *)
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

let sha3_keccak8_f1600_avx512_tmc =
  define_trimmed "sha3_keccak8_f1600_avx512_tmc" sha3_keccak8_f1600_avx512_mc;;

let SHA3_KECCAK8_F1600_AVX512_EXEC =
  X86_MK_CORE_EXEC_RULE sha3_keccak8_f1600_avx512_tmc;;

(* ------------------------------------------------------------------------- *)
(* 8-way packing SPECIFICATION (analog of keccak4_pack in the 4x proof).      *)
(*                                                                           *)
(* The register-resident layout holds Keccak lane k of eight independent     *)
(* states in one 512-bit lane register zmm_k: state j's word k occupies bits *)
(* [64*j .. 64*j+63].  keccak8_pack assembles the eight per-state lane lists  *)
(* B1..B8 (Bj = state j's 25 words, j=1..8) into the 25-element int512     *)
(* list the round body operates on -- B1 in the low 64 bits, ... , B8 in the *)
(* top 64.  It is keccak4_pack's word_join tree with one extra level: two     *)
(* int256 halves (B1..B4 low, B5..B8 high) joined into each int512.        *)
(* ------------------------------------------------------------------------- *)

let keccak8_pack = define
 `keccak8_pack (B1:int64 list) (B2:int64 list) (B3:int64 list) (B4:int64 list)
               (B5:int64 list) (B6:int64 list) (B7:int64 list) (B8:int64 list)
    :(int512)list =
    MAP2 word_join
      ((MAP2 word_join
          ((MAP2 word_join B8 B7):int128 list)
          ((MAP2 word_join B6 B5):int128 list)):int256 list)
      ((MAP2 word_join
          ((MAP2 word_join B4 B3):int128 list)
          ((MAP2 word_join B2 B1):int128 list)):int256 list)`;;

(* Lanewise decomposition helper (analog of INT256_EQ_LANES): a 512-bit lane *)
(* register equals another iff its eight int64 sublanes agree.  As in the 4x *)
(* proof, this splits each per-round ROUND_CORRECT lane goal into eight       *)
(* per-buffer sub-BITBLASTs (one per state) instead of one ~12800-bit blast,  *)
(* which is the crux of keeping the deferred discharge tractable.            *)
let INT512_EQ_LANES = prove
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
   [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    BITBLAST_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Round-body SPECIFICATION (goal term; analog of the 4x ROUND_CORRECT).      *)
(*                                                                           *)
(* Proved below as ..._ROUND_CORRECT (see STATUS). One trip through the      *)
(* resident round body [loop head pc+0x401 .. dec at pc+0x7ac] carries the    *)
(* (tmc offsets = objdump/mc offsets minus 4: define_trimmed drops leading     *)
(* ENDBR64).                                                                   *)
(* 8-way packed state through one keccak_round of each of the eight lanes;    *)
(* the round constant rc is broadcast to all 8 lanes (vpbroadcastq (%r11))    *)
(* and r11 is advanced to the next constant. Reads/writes the full ZMM0..24.  *)
(* ------------------------------------------------------------------------- *)

let sha3_keccak8_f1600_avx512_ROUND_SPEC_GOAL = `
    !pc rcptr rc B1 B2 B3 B4 B5 B6 B7 B8 d rp cnt.
     LENGTH B1 = 25 /\ LENGTH B2 = 25 /\ LENGTH B3 = 25 /\ LENGTH B4 = 25 /\
     LENGTH B5 = 25 /\ LENGTH B6 = 25 /\ LENGTH B7 = 25 /\ LENGTH B8 = 25
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (BUTLAST sha3_keccak8_f1600_avx512_tmc) /\
            read RIP s = word (pc + 0x401) /\
            read RDI s = d /\ read RSI s = rp /\ read R10 s = cnt /\
            read R11 s = rcptr /\
            read (memory :> bytes64 rcptr) s = rc /\
            wordlist_from_memory(rp,24) s = round_constants /\
            [read ZMM0 s; read ZMM1 s; read ZMM2 s; read ZMM3 s; read ZMM4 s;
             read ZMM5 s; read ZMM6 s; read ZMM7 s; read ZMM8 s; read ZMM9 s;
             read ZMM10 s; read ZMM11 s; read ZMM12 s; read ZMM13 s; read ZMM14 s;
             read ZMM15 s; read ZMM16 s; read ZMM17 s; read ZMM18 s; read ZMM19 s;
             read ZMM20 s; read ZMM21 s; read ZMM22 s; read ZMM23 s; read ZMM24 s] =
            keccak8_pack B1 B2 B3 B4 B5 B6 B7 B8)
       (\s. bytes_loaded s (word pc) (BUTLAST sha3_keccak8_f1600_avx512_tmc) /\
            read RIP s = word (pc + 0x7ac) /\
            read RDI s = d /\ read RSI s = rp /\ read R10 s = cnt /\
            read R11 s = word_add rcptr (word 8) /\
            wordlist_from_memory(rp,24) s = round_constants /\
            [read ZMM0 s; read ZMM1 s; read ZMM2 s; read ZMM3 s; read ZMM4 s;
             read ZMM5 s; read ZMM6 s; read ZMM7 s; read ZMM8 s; read ZMM9 s;
             read ZMM10 s; read ZMM11 s; read ZMM12 s; read ZMM13 s; read ZMM14 s;
             read ZMM15 s; read ZMM16 s; read ZMM17 s; read ZMM18 s; read ZMM19 s;
             read ZMM20 s; read ZMM21 s; read ZMM22 s; read ZMM23 s; read ZMM24 s] =
            keccak8_pack (keccak_round rc B1) (keccak_round rc B2)
                         (keccak_round rc B3) (keccak_round rc B4)
                         (keccak_round rc B5) (keccak_round rc B6)
                         (keccak_round rc B7) (keccak_round rc B8))
       (MAYCHANGE [RIP; R11] ,,
        MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17; ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23; ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`;;

(* ------------------------------------------------------------------------- *)
(* Reusable tactics for the scalar-lane per-bit discharge of ROUND_CORRECT.   *)
(*                                                                           *)
(* The 8-way (512-bit) round body defeats a direct BITBLAST (theta diffusion  *)
(* over 8 SIMD lanes). Strategy: (1) keep the 142-instruction symbolic        *)
(* execution bounded by abbreviating every freshly-written ZMM value to a     *)
(* fresh variable (ZMM_ABBREV_TAC) so terms never nest; (2) split each packed  *)
(* output register into its 8 independent 64-bit sublanes (INT512_EQ_LANES);  *)
(* (3) project the abbreviation chain to one 64-bit sublane (proj_lane/SWP) -  *)
(* one scalar Keccak lane over one state's inputs; (4) fold the theta          *)
(* vpternlogq (0x96) DNF back to XOR3 (XOR3_FOLD) to shrink the term ~37x;     *)
(* (5) close with per-output-bit BITBLAST (PERBIT_BITBLAST), tiny BDDs.        *)
(* ------------------------------------------------------------------------- *)

let is_read t = try fst(dest_const(fst(strip_comb t)))="read" with _ -> false;;

(* Per-step: abbreviate each non-var `read ZMMk sN = rhs` to a fresh var. *)
let ZMM_ABBREV_TAC (sname:string) : tactic =
  fun (asl,w) ->
    let st = mk_var(sname, `:x86state`) in
    let is_zmm_read t = (match t with
      | Comb(Comb(Const("read",_), Const(n,_)), s) ->
          s = st && String.length n >= 3 && String.sub n 0 3 = "ZMM"
      | _ -> false) in
    let tgts = filter (fun (_,th) -> let c=concl th in
        is_eq c && is_zmm_read(lhand c) && not(is_var(rand c))) asl in
    (EVERY (map (fun (_,th) -> let r=rand(concl th) in
        ABBREV_TAC(mk_eq(genvar(type_of r),r))) tgts)) (asl,w);;

(* Push word_subword inward through and/or/xor/not and word_join/subword, *)
(* i.e. project a 512-bit lane expression down to one 64-bit sublane.     *)
let SWP : conv =
  let aox = GEN_REWRITE_CONV I [WORD_SUBWORD_AND; WORD_SUBWORD_OR; WORD_SUBWORD_XOR] in
  let notm = PART_MATCH (lhs o rand) WORD_SUBWORD_NOT in
  let dis = (REWRITE_CONV[DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;DIMINDEX_512] THENC NUM_REDUCE_CONV) in
  let push1 t =
    (try WORD_SIMPLE_SUBWORD_CONV t with Failure _ ->
     try aox t with Failure _ ->
     let th = notm t in MP th (EQT_ELIM(dis (lhand(concl th))))) in
  TOP_DEPTH_CONV push1;;

(* Project a 512-bit word-equation assumption (chain `e = _v` or `zg = ...`) *)
(* to sublane j: `word_subword <var> (64j,64) = SWP(word_subword <e> (64j,64))`. *)
let proj_lane j th =
  let c = concl th in
  let a,e = if is_var(lhand c) then (lhand c,rand c) else (rand c,lhand c) in
  if not(is_var a) || type_of a <> `:int512` then failwith "proj_lane" else
  let eqth = if lhand c = a then th else SYM th in
  let pos = mk_pair(mk_small_numeral(64*j),`64`) in
  let f = mk_abs(`x:int512`,
                 list_mk_comb(`word_subword:int512->num#num->int64`,[`x:int512`;pos])) in
  CONV_RULE(RAND_CONV SWP)(BETA_RULE(AP_TERM f eqth));;

(* Theta vpternlogq (imm 0x96) DNF folded to XOR3. *)
let XOR3_FOLD = prove
 (`!a b c:int64. (~~a && ~~b && c) || (~~a && b && ~~c) || (a && ~~b && ~~c) ||
                 (a && b && c) = a ^^ b ^^ c`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* Per-output-bit BITBLAST with a Gc throttle: one tiny BDD per bit. *)
let PERBIT_BITBLAST : tactic =
  let cnt = ref 0 in
  BITBLAST_THEN (fun vars ->
    REPEAT CONJ_TAC THEN
    W(fun (_,w) -> let th = prove(w, CONV_TAC(BDD_DEFTAUT vars)) in
       incr cnt; (if !cnt mod 128 = 0 then Gc.compact()); ACCEPT_TAC th));;

(* Discharge one sublane goal `word_subword _a (64j,64) = word_subword RHS (64j,64)`: *)
(* reduce spec RHS to scalar (SWP), unfold the assembly LHS via the projected chain, *)
(* fold theta DNFs, drop the (now-irrelevant) 512-bit chain, per-bit BITBLAST.        *)
let SUBLANE_AUTO : tactic =
  W(fun (_,w) ->
     let j = (dest_small_numeral(fst(dest_pair(rand(lhand w)))))/64 in
     CONV_TAC SWP THEN
     W(fun (asl,_) -> REWRITE_TAC(mapfilter (fun (_,th) -> proj_lane j th) asl)) THEN
     REWRITE_TAC[XOR3_FOLD] THEN
     POP_ASSUM_LIST(K ALL_TAC) THEN PERBIT_BITBLAST);;

(* ------------------------------------------------------------------------- *)
(* M1 round-body correctness, PROVED.  One trip through the register-resident *)
(* round body [pc+0x401 .. pc+0x7ac] carries the 8-way packed state through   *)
(* one keccak_round of each of the eight lanes.  Normalize (defer packing,    *)
(* ghost the 25 ZMM regs) -> 142 abbreviated symbolic-execution steps ->      *)
(* per-lane split -> scalar-lane per-bit discharge (tactics above).           *)
(* Runs in ~40min on a 61GB box (stepping ~40s; ~90s per output lane x 25).   *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK8_F1600_AVX512_ROUND_CORRECT = prove
 (sha3_keccak8_f1600_avx512_ROUND_SPEC_GOAL,
  REWRITE_TAC[SOME_FLAGS; fst SHA3_KECCAK8_F1600_AVX512_EXEC] THEN
  MAP_EVERY X_GEN_TAC
   [`pc:num`; `rcptr:int64`; `rc:int64`;
    `B1:int64 list`; `B2:int64 list`; `B3:int64 list`; `B4:int64 list`;
    `B5:int64 list`; `B6:int64 list`; `B7:int64 list`; `B8:int64 list`;
    `d:int64`; `rp:int64`; `cnt:int64`] THEN
  REWRITE_TAC[LENGTH_EQ_25] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[round_constants] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
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
  MAP_EVERY (fun n -> X86_STEPS_TAC SHA3_KECCAK8_F1600_AVX512_EXEC [n] THEN
                      ZMM_ABBREV_TAC ("s"^string_of_int n)) (1--142) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[keccak8_pack; MAP2; CONS_11]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check(is_conj o concl))) THEN
  REWRITE_TAC[keccak8_pack; keccak_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MAP2; CONS_11] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REPEAT CONJ_TAC THEN
  ONCE_REWRITE_TAC[INT512_EQ_LANES] THEN
  REPEAT CONJ_TAC THEN
  SUBLANE_AUTO);;

(* ------------------------------------------------------------------------- *)
(* Top-level functional-correctness SPECIFICATION (goal term).                *)
(*                                                                           *)
(* Proved below (see STATUS above). Bound as a term rather than a            *)
(* `prove(...)` so this file loads cleanly and the axiom set stays empty; the*)
(* code length 0xbb5 (2997 bytes) and end offset 0xbb4 are read off the       *)
(* assembled object and were reconfirmed against the *_tmc trimming for      *)
(* the proof below. Mirrors SHA3_KECCAK4_F1600_AVX512VL_CORRECT with         *)
(* eight independent states A1..A8 (offsets 0,200,...,1400; total 1600 bytes) *)
(* and rc read from rc_pointer.                                               *)
(* ------------------------------------------------------------------------- *)

let sha3_keccak8_f1600_avx512_SPEC_GOAL = `
    !rc_pointer:int64 bitstate_in:int64 A1 A2 A3 A4 A5 A6 A7 A8 pc:num.
    nonoverlapping (word pc, 0xbb1) (bitstate_in, 1600) /\
    nonoverlapping (word pc, 0xbb1) (rc_pointer, 192) /\
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
             (\s. read RIP s = word(pc + 0xbb0) /\
                  wordlist_from_memory(bitstate_in,25) s = keccak 24 A1 /\
                  wordlist_from_memory(word_add bitstate_in (word 200),25) s = keccak 24 A2 /\
                  wordlist_from_memory(word_add bitstate_in (word 400),25) s = keccak 24 A3 /\
                  wordlist_from_memory(word_add bitstate_in (word 600),25) s = keccak 24 A4 /\
                  wordlist_from_memory(word_add bitstate_in (word 800),25) s = keccak 24 A5 /\
                  wordlist_from_memory(word_add bitstate_in (word 1000),25) s = keccak 24 A6 /\
                  wordlist_from_memory(word_add bitstate_in (word 1200),25) s = keccak 24 A7 /\
                  wordlist_from_memory(word_add bitstate_in (word 1400),25) s = keccak 24 A8)
           (MAYCHANGE [RIP; R10; R11] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17; ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23; ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes (bitstate_in, 1600)])`;;

(* 512-bit analog of keccak_spec's MEMORY_256_FROM_64_TAC: merge eight adjacent
   64-bit memory reads into one bytes512 read, for relating the prologue's
   `vmovdqu64 zmm,[..]` loads to the per-state input lanes. (Defining it is
   side-effect-free; READ_MEMORY_MERGE_CONV/bytes512 are only invoked at call
   time.) *)
(* READ_MEMORY_MERGE_CONV caps at bytes256 (level<=2), so decompose a 512-bit
   read as two 256-bit halves first, then merge each to 64-bit. VALIDATED. *)
let READ_BYTES512_JOIN = prove
 (`read (memory :> bytes512 x) (s:x86state) : int512 =
     word_join (read (memory :> bytes256 (word_add x (word 32))) s)
               (read (memory :> bytes256 x) s)`,
  ONCE_REWRITE_TAC[el 5 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN
  CONV_TAC WORD_BLAST);;
let MERGE512_CONV : conv =
  GEN_REWRITE_CONV I [READ_BYTES512_JOIN] THENC BINOP_CONV (READ_MEMORY_MERGE_CONV 2);;
let MEMORY_512_FROM_64_TAC =
  let a_tm = `a:int64` and n_tm = `n:num` and i64_ty = `:int64`
  and pat = `read (memory :> bytes512(word_add a (word n))) s0` in
  fun v boff n ->
    let pat' = subst[mk_var(v,i64_ty),a_tm] pat in
    let f i = MERGE512_CONV (subst[mk_small_numeral(boff + 64*i),n_tm] pat') in
    MP_TAC(end_itlist CONJ (map f (0--(n-1))));;

(* rc-at-r11: element i of the round-constant wordlist in memory (mirror of the
   4x RC_AT_R11), used by the preservation subgoal to feed ROUND_CORRECT. *)
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
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  ASM_REWRITE_TAC[round_constants; WORD_ADD_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Transpose-lane / memory-frame discharge for the prologue (subgoal 2) and    *)
(* tail (subgoal 5).  After per-step ZMM_ABBREV stepping the load/store values  *)
(* are fresh genvars chained (via `expr = _v` assumptions) to the digit/EL      *)
(* variables.  LANE_DISCHARGE3 unfolds that chain (GSYM the `expr = _v` and     *)
(* `.. = EL k Bj` assumptions, NOT the `read .. = _v` ones) then closes each    *)
(* 64-bit output bit with PERBIT_BITBLAST (tiny BDDs, ~1s/lane; the transpose   *)
(* is a pure digit permutation).                                                *)
(*                                                                             *)
(* The tail's 512-bit stores leave `memory :> bytes512` in the accumulated      *)
(* MAYCHANGE frame, and ENSURES_FINAL_STATE_TAC leaves that frame subgoal as an *)
(* un-eta-reduced relational lambda.  The stock SUBSUMED_MAYCHANGE_TAC breaks    *)
(* twice on this: MAYCHANGE_CANON_CONV chokes on the lambda, and the SUBSUMED    *)
(* leaf has no ASSIGNS_BYTES512.  FRAME_CLOSER lifts the accumulated MAYCHANGE   *)
(* assumption to a `subsumed` goal, eta-reduces, then discharges via a patched   *)
(* leaf that peels `memory :>` with SUBSUMED_ASSIGNS_SUBCOMPONENTS and rewrites  *)
(* ASSIGNS_BYTES512 before SUBSUMED_ASSIGNS_BYTES + CONTAINED_TAC.               *)
(* ------------------------------------------------------------------------- *)

let is_read t = try fst(dest_const(fst(strip_comb t))) = "read" with _ -> false;;

let LANE_DISCHARGE3 : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check(is_conj o concl))) THEN
  W(fun (asl,_) ->
     let chain = mapfilter (fun (_,th) -> let c = concl th in
        if is_eq c && is_var(rand c) &&
           (let n = fst(dest_var(rand c)) in String.length n > 0 && n.[0] = '_') &&
           not(is_read(lhand c))
        then GSYM th else fail()) asl in
     let eldefs = mapfilter (fun (_,th) -> let c = concl th in
        if is_eq c &&
           (try fst(dest_const(fst(strip_comb(rand c)))) = "EL" with _ -> false)
        then GSYM th else fail()) asl in
     REWRITE_TAC (chain @ eldefs)) THEN
  PERBIT_BITBLAST;;

let ASSIGNS_BYTES512 = prove
 (`!a. ASSIGNS (bytes512 a) = ASSIGNS(bytes(a,64))`,
  GEN_TAC THEN REWRITE_TAC[bytes512] THEN MATCH_MP_TAC ASSIGNS_BYTES_ASWORD THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let SUBSUMED_ASSIGNS_TAC_512 =
  MATCH_ACCEPT_TAC SUBSUMED_REFL ORELSE
  (MATCH_MP_TAC SUBSUMED_ID_EXTENSIONALLY_VALID_COMPONENT THEN
   CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV THEN NO_TAC) ORELSE
  (MATCH_MP_TAC SUBSUMED_ASSIGNS_SUBCOMPONENTS THEN
   GEN_REWRITE_TAC (BINOP_CONV o TRY_CONV)
     [ASSIGNS_BYTES8; ASSIGNS_BYTES16; ASSIGNS_BYTES32; ASSIGNS_BYTES64;
      ASSIGNS_BYTES128; ASSIGNS_BYTES256; ASSIGNS_BYTES512] THEN
   MATCH_MP_TAC SUBSUMED_ASSIGNS_BYTES THEN CONTAINED_TAC) ORELSE
  (CONV_TAC(BINOP_CONV(RAND_CONV COMPONENT_CANON_CONV)) THEN
   REPEAT(MATCH_MP_TAC SUBSUMED_ASSIGNS_SUBCOMPONENTS) THEN
   TRY(MATCH_ACCEPT_TAC SUBSUMED_ASSIGNS_SUBCOMPONENT) THEN
   GEN_REWRITE_TAC (BINOP_CONV o TRY_CONV)
     [ASSIGNS_BYTES8; ASSIGNS_BYTES16; ASSIGNS_BYTES32; ASSIGNS_BYTES64;
      ASSIGNS_BYTES128; ASSIGNS_BYTES256; ASSIGNS_BYTES512] THEN
   MATCH_MP_TAC SUBSUMED_ASSIGNS_BYTES THEN CONTAINED_TAC);;

let SUBSUMED_MAYCHANGE_TAC_512 =
  let lemma_step = prove
   (`(D ,, D = D ==> C1 subsumed D) /\ (D ,, D = D ==> C2 subsumed D)
     ==> (D ,, D = D ==> (C1 ,, C2) subsumed D)`, MESON_TAC[SUBSUMED_FOR_SEQ])
  and lemma_start = prove
   (`D ,, D = D /\ (D ,, D = D ==> C1 subsumed D) /\ (D ,, D = D ==> C2 subsumed D)
    ==> (C1 ,, C2) subsumed D`, MESON_TAC[SUBSUMED_FOR_SEQ]) in
  let rec tac gl =
   ((MATCH_MP_TAC SUBSUMED_SEQ_LEFT THEN CONJ_TAC THENL
       [tac; SUBSUMED_ID_MAYCHANGE_TAC]) ORELSE
    (MATCH_MP_TAC SUBSUMED_SEQ_RIGHT THEN CONJ_TAC THENL
       [SUBSUMED_ID_MAYCHANGE_TAC; tac]) ORELSE
    SUBSUMED_ASSIGNS_TAC_512) gl in
  MATCH_ACCEPT_TAC SUBSUMED_TRIVIAL ORELSE (
  CONV_TAC(BINOP_CONV MAYCHANGE_CANON_CONV) THEN
  TRY(MATCH_MP_TAC lemma_start THEN CONJ_TAC THENL
       [MAYCHANGE_IDEMPOT_TAC THEN NO_TAC; CONJ_TAC] THEN
      REPEAT(MATCH_MP_TAC lemma_step THEN CONJ_TAC) THEN DISCH_THEN(K ALL_TAC)) THEN
  ((POP_ASSUM_LIST(K ALL_TAC) THEN tac) ORELSE tac));;

let FRAME_CLOSER =
  let pth = prove(`R s s' ==> R subsumed R' ==> R' s s'`,
                  REWRITE_TAC[subsumed] THEN MESON_TAC[]) in
  FIRST_X_ASSUM(fun th -> if maychange_term(concl th)
                          then MATCH_MP_TAC(MATCH_MP pth th) else fail()) THEN
  CONV_TAC(TOP_DEPTH_CONV ETA_CONV) THEN
  SUBSUMED_MAYCHANGE_TAC_512;;

(* Per-subgoal router: the memory-frame goal (contains MAYCHANGE) goes to        *)
(* FRAME_CLOSER, every transpose-lane word equality to LANE_DISCHARGE3.          *)
let LANE_OR_FRAME =
  W(fun (_,w) ->
    if can (find_term (fun u -> try fst(dest_const(fst(strip_comb u))) = "MAYCHANGE"
                                with _ -> false)) w
    then FRAME_CLOSER else LANE_DISCHARGE3);;

(* ------------------------------------------------------------------------- *)
(* Top-level correctness: eight independent Keccak-f1600 states, register-     *)
(* resident (zmm0..24), 24-round loop.  Flat-kernel (tmc) offsets: entry 0x0   *)
(* (transpose prologue); loop head 0x401; ROUND body 0x401..0x7ac; dec 0x7ac;  *)
(* jne->0x401 @0x7af; epilogue (untranspose+store) 0x7b5; vzeroupper 0xbad;    *)
(* ret 0xbb0.  Mirrors SHA3_KECCAK4_F1600_AVX512VL_CORRECT (8 states, native   *)
(* ZMM).  Prologue (subgoal 2) & tail (subgoal 5) transpose lanes are          *)
(* discharged per-output-bit (PERBIT_BITBLAST) — the 8-way 512-bit word_join   *)
(* trees make monolithic per-lane BITBLAST impractical.  Preservation applies  *)
(* the round-body lemma SHA3_KECCAK8_F1600_AVX512_ROUND_CORRECT 24 times.       *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK8_F1600_AVX512_CORRECT = prove
 (sha3_keccak8_f1600_avx512_SPEC_GOAL,
  REWRITE_TAC[SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              fst SHA3_KECCAK8_F1600_AVX512_EXEC] THEN
  MAP_EVERY X_GEN_TAC
   [`rc_pointer:int64`;`bitstate_in:int64`;`A1:int64 list`;`A2:int64 list`;
    `A3:int64 list`;`A4:int64 list`;`A5:int64 list`;`A6:int64 list`;
    `A7:int64 list`;`A8:int64 list`;`pc:num`] THEN
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
  ENSURES_WHILE_PAUP_TAC `0` `24` `pc + 0x401` `pc + 0x7af`
  `\i s.
      (read RDI s = bitstate_in /\ read RSI s = rc_pointer /\
       read R10 s = word (24 - i) /\
       read R11 s = word_add rc_pointer (word (8 * i)) /\
       wordlist_from_memory(rc_pointer,24) s = round_constants /\
       [read ZMM0 s; read ZMM1 s; read ZMM2 s; read ZMM3 s; read ZMM4 s;
        read ZMM5 s; read ZMM6 s; read ZMM7 s; read ZMM8 s; read ZMM9 s;
        read ZMM10 s; read ZMM11 s; read ZMM12 s; read ZMM13 s; read ZMM14 s;
        read ZMM15 s; read ZMM16 s; read ZMM17 s; read ZMM18 s; read ZMM19 s;
        read ZMM20 s; read ZMM21 s; read ZMM22 s; read ZMM23 s; read ZMM24 s] =
         keccak8_pack (keccak i A1) (keccak i A2) (keccak i A3) (keccak i A4)
                      (keccak i A5) (keccak i A6) (keccak i A7) (keccak i A8)) /\
      (read ZF s <=> i = 24)` THEN
  REPEAT CONJ_TAC THENL
   [(*** 1: 0 < 24 ***) ARITH_TAC;

    (*** 2: prologue (entry -> 0x401): load+transpose; per-output-bit lanes ***)
    REWRITE_TAC[ARITH_RULE `24 - 0 = 24`; ARITH_RULE `8 * 0 = 0`; WORD_ADD_0;
                CONJUNCT1 keccak; keccak8_pack] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_EQ_25]) THEN
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check(is_conj o concl))) THEN
    REPEAT(FIRST_X_ASSUM(fun th ->
       let l,r = dest_eq(concl th) in
       if is_var l && List.mem (fst(dest_var l))
            ["A1";"A2";"A3";"A4";"A5";"A6";"A7";"A8"]
       then SUBST_ALL_TAC th else failwith "keep")) THEN
    REWRITE_TAC[MAP2; CONS_11] THEN
    CONV_TAC(TOP_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (bitstate_in,8 * 200)) s0` THEN
    MEMORY_512_FROM_64_TAC "bitstate_in" 0 3 THEN
    MEMORY_512_FROM_64_TAC "bitstate_in" 200 3 THEN
    MEMORY_512_FROM_64_TAC "bitstate_in" 400 3 THEN
    MEMORY_512_FROM_64_TAC "bitstate_in" 600 3 THEN
    MEMORY_512_FROM_64_TAC "bitstate_in" 800 3 THEN
    MEMORY_512_FROM_64_TAC "bitstate_in" 1000 3 THEN
    MEMORY_512_FROM_64_TAC "bitstate_in" 1200 3 THEN
    MEMORY_512_FROM_64_TAC "bitstate_in" 1400 3 THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY (fun n -> X86_STEPS_TAC SHA3_KECCAK8_F1600_AVX512_EXEC [n] THEN
                        ZMM_ABBREV_TAC ("s"^string_of_int n)) (1--145) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CONS_11]) THEN
    ASM_REWRITE_TAC[WORD_SUBWORD_JOIN_EXTRACT_64; WORD_SUBWORD_JOIN_EXTRACT_128;
                    MAP2; CONS_11] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN
    (* route conjuncts: non-lane (register/flag/offset/wordlist) closed cheaply;
       only the per-lane word equalities go to per-output-bit BITBLAST (a lane is
       never sent to the monolithic WORD_BLAST). *)
    REPEAT CONJ_TAC THEN
    TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN TRY REFL_TAC THEN TRY ARITH_TAC THEN
    LANE_OR_FRAME;

    (*** 3: preservation (0x401 -> 0x7af) = ROUND_CORRECT + dec ***)
    REPEAT STRIP_TAC THEN
    ENSURES_SEQUENCE_TAC `pc + 0x7ac`
     `\s. read RDI s = bitstate_in /\ read RSI s = rc_pointer /\
          read R10 s = word (24 - i) /\
          read R11 s = word_add rc_pointer (word (8 * (i + 1))) /\
          wordlist_from_memory(rc_pointer,24) s = round_constants /\
          [read ZMM0 s; read ZMM1 s; read ZMM2 s; read ZMM3 s; read ZMM4 s;
           read ZMM5 s; read ZMM6 s; read ZMM7 s; read ZMM8 s; read ZMM9 s;
           read ZMM10 s; read ZMM11 s; read ZMM12 s; read ZMM13 s; read ZMM14 s;
           read ZMM15 s; read ZMM16 s; read ZMM17 s; read ZMM18 s; read ZMM19 s;
           read ZMM20 s; read ZMM21 s; read ZMM22 s; read ZMM23 s; read ZMM24 s] =
            keccak8_pack (keccak (i+1) A1) (keccak (i+1) A2) (keccak (i+1) A3)
                         (keccak (i+1) A4) (keccak (i+1) A5) (keccak (i+1) A6)
                         (keccak (i+1) A7) (keccak (i+1) A8)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[keccak] THEN
      MATCH_MP_TAC ENSURES_PRECONDITION_THM_GEN THEN
      MAP_EVERY EXISTS_TAC
       [`\(s:x86state). bytes_loaded s (word pc) (BUTLAST sha3_keccak8_f1600_avx512_tmc) /\
             read RIP s = word (pc + 0x401) /\
             read RDI s = bitstate_in /\ read RSI s = rc_pointer /\
             read R10 s = word (24 - i) /\
             read R11 s = word_add rc_pointer (word (8 * i)) /\
             read (memory :> bytes64 (word_add rc_pointer (word (8 * i)))) s =
               EL i round_constants /\
             wordlist_from_memory(rc_pointer,24) s = round_constants /\
             [read ZMM0 s; read ZMM1 s; read ZMM2 s; read ZMM3 s; read ZMM4 s;
              read ZMM5 s; read ZMM6 s; read ZMM7 s; read ZMM8 s; read ZMM9 s;
              read ZMM10 s; read ZMM11 s; read ZMM12 s; read ZMM13 s; read ZMM14 s;
              read ZMM15 s; read ZMM16 s; read ZMM17 s; read ZMM18 s; read ZMM19 s;
              read ZMM20 s; read ZMM21 s; read ZMM22 s; read ZMM23 s; read ZMM24 s] =
               keccak8_pack (keccak i A1) (keccak i A2) (keccak i A3) (keccak i A4)
                            (keccak i A5) (keccak i A6) (keccak i A7) (keccak i A8)`;
        `MAYCHANGE [RIP; R11] ,,
         MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17; ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23; ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`] THEN
      REPEAT CONJ_TAC THENL
       [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`s:x86state`; `rc_pointer:int64`; `i:num`] RC_AT_R11) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[SOME_FLAGS] THEN
        CONV_TAC(REWR_CONV(GSYM subsumed)) THEN
        REWRITE_TAC[ETA_AX] THEN SUBSUMED_MAYCHANGE_TAC;
        REWRITE_TAC[WORD_RULE
          `word_add (rc_pointer:int64) (word (8 * (i + 1))) =
           word_add (word_add rc_pointer (word (8 * i))) (word 8)`] THEN
        MATCH_MP_TAC(ISPECL
          [`pc:num`; `(word_add rc_pointer (word (8 * i))):int64`;
           `(EL i round_constants):int64`;
           `keccak i A1`; `keccak i A2`; `keccak i A3`; `keccak i A4`;
           `keccak i A5`; `keccak i A6`; `keccak i A7`; `keccak i A8`;
           `bitstate_in:int64`; `rc_pointer:int64`; `(word (24 - i)):int64`]
          SHA3_KECCAK8_F1600_AVX512_ROUND_CORRECT) THEN
        REPEAT CONJ_TAC THEN MATCH_MP_TAC LENGTH_KECCAK THEN ASM_REWRITE_TAC[]];
      ENSURES_INIT_TAC "s0" THEN
      CONV_TAC(TOP_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
      X86_STEPS_TAC SHA3_KECCAK8_F1600_AVX512_EXEC (1--1) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `i < 24`)) THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST];

    (*** 4: backedge (0x7af -> 0x401): jne taken (ZF=F) ***)
    REPEAT STRIP_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `~(read ZF s0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    X86_STEPS_TAC SHA3_KECCAK8_F1600_AVX512_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** 5: tail (0x7af -> 0xbb0): i=24, epilogue untranspose+store ***)
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
    REWRITE_TAC[keccak8_pack] THEN
    REWRITE_TAC[MAP2; CONS_11] THEN
    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun n -> X86_STEPS_TAC SHA3_KECCAK8_F1600_AVX512_EXEC [n] THEN
                        ZMM_ABBREV_TAC ("s"^string_of_int n)) (1--145) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (can (term_match [] `read qqq s:int512 = xxx`) o concl))) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ENSURES_FINAL_STATE_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[WORD_SUBWORD_JOIN_EXTRACT_64; WORD_SUBWORD_JOIN_EXTRACT_128;
                    MAP2; CONS_11] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN
    (* route conjuncts: non-lane (register/flag/offset/wordlist) closed cheaply;
       only the per-lane word equalities go to per-output-bit BITBLAST (a lane is
       never sent to the monolithic WORD_BLAST). *)
    REPEAT CONJ_TAC THEN
    TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN TRY REFL_TAC THEN TRY ARITH_TAC THEN
    LANE_OR_FRAME]);;

(* ------------------------------------------------------------------------- *)
(* SysV ABI subroutine wrappers (register-resident kernel: NOSTACK promote).  *)
(* ------------------------------------------------------------------------- *)

let sha3_keccak8_f1600_avx512_saved_precanon = !simulation_precanon_thms;;
simulation_precanon_thms := union [WORDLIST_FROM_MEMORY] (!simulation_precanon_thms);;

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
  X86_PROMOTE_RETURN_NOSTACK_TAC sha3_keccak8_f1600_avx512_tmc
    SHA3_KECCAK8_F1600_AVX512_CORRECT);;

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
  MATCH_ACCEPT_TAC(ADD_IBT_RULE SHA3_KECCAK8_F1600_AVX512_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Windows ABI subroutine wrappers. Same .S with -DWINDOWS_ABI=1: endbr +      *)
(* spill of callee-saved XMM6-15/RDI/RSI (frame 0xb0), Microsoft args RCX,RDX  *)
(* shuffled into SysV RDI,RSI, then mirror restore + ret. The core body sits   *)
(* at offset 92 in the trimmed Windows object and is reused via                *)
(* BYTES_LOADED_SUBPROGRAM_RULE (identical trampoline to the 4x avx512vl).      *)
(* ------------------------------------------------------------------------- *)

let sha3_keccak8_f1600_avx512_windows_mc = define_from_elf
  "sha3_keccak8_f1600_avx512_windows_mc" "x86/sha3/sha3_keccak8_f1600_avx512.obj";;

let sha3_keccak8_f1600_avx512_windows_tmc =
  define_trimmed "sha3_keccak8_f1600_avx512_windows_tmc"
                 sha3_keccak8_f1600_avx512_windows_mc;;

let sha3_keccak8_f1600_avx512_windows_tmc_EXEC =
  X86_MK_EXEC_RULE sha3_keccak8_f1600_avx512_windows_tmc;;

let SHA3_KECCAK8_F1600_AVX512_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!rc_pointer:int64 bitstate_in:int64 A1 A2 A3 A4 A5 A6 A7 A8 pc:num stackpointer:int64 returnaddress.
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak8_f1600_avx512_windows_tmc) (val (word_sub stackpointer (word 0xb0)), 0xb0) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak8_f1600_avx512_windows_tmc) (val bitstate_in, 1600) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak8_f1600_avx512_windows_tmc) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in, 1600) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in, 1600) (val (word_sub stackpointer (word 0xb0)), 0xb0 + 8) /\
  nonoverlapping_modulo (2 EXP 64) (val (word_sub stackpointer (word 0xb0)), 0xb0) (val rc_pointer, 192)
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
  REPLICATE_TAC 11 GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  WORD_FORALL_OFFSET_TAC 0xb0 THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fst sha3_keccak8_f1600_avx512_windows_tmc_EXEC] THEN
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
  REWRITE_TAC[fst sha3_keccak8_f1600_avx512_windows_tmc_EXEC] THEN
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
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN REWRITE_TAC[ALL] THEN
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
  X86_STEPS_TAC sha3_keccak8_f1600_avx512_windows_tmc_EXEC (17--30) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let SHA3_KECCAK8_F1600_AVX512_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!rc_pointer:int64 bitstate_in:int64 A1 A2 A3 A4 A5 A6 A7 A8 pc:num stackpointer:int64 returnaddress.
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak8_f1600_avx512_windows_mc) (val (word_sub stackpointer (word 0xb0)), 0xb0) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak8_f1600_avx512_windows_mc) (val bitstate_in, 1600) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak8_f1600_avx512_windows_mc) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in, 1600) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in, 1600) (val (word_sub stackpointer (word 0xb0)), 0xb0 + 8) /\
  nonoverlapping_modulo (2 EXP 64) (val (word_sub stackpointer (word 0xb0)), 0xb0) (val rc_pointer, 192)
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
(*                                                                           *)
(* Mirrors the 4x AVX-512VL kernel's _SAFE chain, widened for 8 states        *)
(* (1600-byte state buffer).                                                  *)
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
        nonoverlapping (word pc,2993) (bitstate_in,1600) /\
        nonoverlapping (word pc,2993) (rc_pointer,192) /\
        nonoverlapping (bitstate_in,1600) (rc_pointer,192)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc)
                 (BUTLAST sha3_keccak8_f1600_avx512_tmc) /\
                 read RIP s = word pc /\
                 C_ARGUMENTS [bitstate_in; rc_pointer] s /\
                 read events s = e)
            (\s.
                 read RIP s = word (pc + 2992) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc_pointer bitstate_in pc /\
                      memaccess_inbounds e2
                      [bitstate_in,1600; rc_pointer,192]
                      [bitstate_in,1600]))
            (MAYCHANGE [RIP; R10; R11] ,,
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
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak8_f1600_avx512_windows_tmc) (val (word_sub stackpointer (word 0xb0)), 0xb0) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak8_f1600_avx512_windows_tmc) (val bitstate_in, 1600) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak8_f1600_avx512_windows_tmc) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in, 1600) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in, 1600) (val (word_sub stackpointer (word 0xb0)), 0xb0 + 8) /\
  nonoverlapping_modulo (2 EXP 64) (val (word_sub stackpointer (word 0xb0)), 0xb0) (val rc_pointer, 192)
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
  REPLICATE_TAC 4 GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  WORD_FORALL_OFFSET_TAC 0xb0 THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fst sha3_keccak8_f1600_avx512_windows_tmc_EXEC] THEN
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

  REWRITE_TAC[fst sha3_keccak8_f1600_avx512_windows_tmc_EXEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN

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
                         `pc + 92`]))
  THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; ALL] THEN
  ANTS_TAC THENL [REPEAT NONOVERLAPPING_TAC; ALL_TAC] THEN

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
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ DISCHARGE_SAFETY_PROPERTY_TAC; ALL_TAC ] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let SHA3_KECCAK8_F1600_AVX512_WINDOWS_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e rc_pointer:int64 bitstate_in:int64 pc:num stackpointer:int64 returnaddress.
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak8_f1600_avx512_windows_mc) (val (word_sub stackpointer (word 0xb0)), 0xb0) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak8_f1600_avx512_windows_mc) (val bitstate_in, 1600) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak8_f1600_avx512_windows_mc) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in, 1600) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in, 1600) (val (word_sub stackpointer (word 0xb0)), 0xb0 + 8) /\
  nonoverlapping_modulo (2 EXP 64) (val (word_sub stackpointer (word 0xb0)), 0xb0) (val rc_pointer, 192)
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

simulation_precanon_thms := sha3_keccak8_f1600_avx512_saved_precanon;;
