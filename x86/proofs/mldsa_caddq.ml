(*
 * Copyright (c) The mldsa-native project authors
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Functional correctness of poly_caddq:                                     *)
(* Modular reduction of polynomial coefficients from (-q, q) to [0, q)       *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "x86/mldsa/mldsa_caddq.o";;
 ****)

let mldsa_caddq_mc = define_assert_from_elf "mldsa_caddq_mc" "x86/mldsa/mldsa_caddq.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xc5; 0xe9; 0xef; 0xd2;  (* VPXOR (%_% xmm2) (%_% xmm2) (%_% xmm2) *)
  0xb8; 0x01; 0xe0; 0x7f; 0x00;
                           (* MOV (% eax) (Imm32 (word 8380417)) *)
  0xc5; 0xf9; 0x6e; 0xc8;  (* VMOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xc5; 0xed; 0x66; 0x07;  (* VPCMPGTD (%_% ymm0) (%_% ymm2) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0xdb; 0xc1;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0xfe; 0x07;  (* VPADDD (%_% ymm0) (%_% ymm0) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x7f; 0x07;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm0) *)
  0xc5; 0xed; 0x66; 0x5f; 0x20;
                           (* VPCMPGTD (%_% ymm3) (%_% ymm2) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xe5; 0xdb; 0xd9;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xe5; 0xfe; 0x5f; 0x20;
                           (* VPADDD (%_% ymm3) (%_% ymm3) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfd; 0x7f; 0x5f; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm3) *)
  0xc5; 0xed; 0x66; 0x67; 0x40;
                           (* VPCMPGTD (%_% ymm4) (%_% ymm2) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xfe; 0x67; 0x40;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm4) *)
  0xc5; 0xed; 0x66; 0x6f; 0x60;
                           (* VPCMPGTD (%_% ymm5) (%_% ymm2) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0xd5; 0xdb; 0xe9;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0xfe; 0x6f; 0x60;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0xfd; 0x7f; 0x6f; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm5) *)
  0xc5; 0xed; 0x66; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm0) (%_% ymm2) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0xfd; 0xdb; 0xc1;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0xfe; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VPADDD (%_% ymm0) (%_% ymm0) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm0) *)
  0xc5; 0xed; 0x66; 0x9f; 0xa0; 0x00; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm3) (%_% ymm2) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0xe5; 0xdb; 0xd9;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xe5; 0xfe; 0x9f; 0xa0; 0x00; 0x00; 0x00;
                           (* VPADDD (%_% ymm3) (%_% ymm3) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm3) *)
  0xc5; 0xed; 0x66; 0xa7; 0xc0; 0x00; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm4) (%_% ymm2) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xfe; 0xa7; 0xc0; 0x00; 0x00; 0x00;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm4) *)
  0xc5; 0xed; 0x66; 0xaf; 0xe0; 0x00; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm5) (%_% ymm2) (Memop Word256 (%% (rdi,224))) *)
  0xc5; 0xd5; 0xdb; 0xe9;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0xfe; 0xaf; 0xe0; 0x00; 0x00; 0x00;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (Memop Word256 (%% (rdi,224))) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm5) *)
  0xc5; 0xed; 0x66; 0x87; 0x00; 0x01; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm0) (%_% ymm2) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0xfd; 0xdb; 0xc1;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0xfe; 0x87; 0x00; 0x01; 0x00; 0x00;
                           (* VPADDD (%_% ymm0) (%_% ymm0) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm0) *)
  0xc5; 0xed; 0x66; 0x9f; 0x20; 0x01; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm3) (%_% ymm2) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0xe5; 0xdb; 0xd9;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xe5; 0xfe; 0x9f; 0x20; 0x01; 0x00; 0x00;
                           (* VPADDD (%_% ymm3) (%_% ymm3) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm3) *)
  0xc5; 0xed; 0x66; 0xa7; 0x40; 0x01; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm4) (%_% ymm2) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xfe; 0xa7; 0x40; 0x01; 0x00; 0x00;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm4) *)
  0xc5; 0xed; 0x66; 0xaf; 0x60; 0x01; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm5) (%_% ymm2) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0xd5; 0xdb; 0xe9;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0xfe; 0xaf; 0x60; 0x01; 0x00; 0x00;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm5) *)
  0xc5; 0xed; 0x66; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm0) (%_% ymm2) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0xfd; 0xdb; 0xc1;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0xfe; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* VPADDD (%_% ymm0) (%_% ymm0) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm0) *)
  0xc5; 0xed; 0x66; 0x9f; 0xa0; 0x01; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm3) (%_% ymm2) (Memop Word256 (%% (rdi,416))) *)
  0xc5; 0xe5; 0xdb; 0xd9;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xe5; 0xfe; 0x9f; 0xa0; 0x01; 0x00; 0x00;
                           (* VPADDD (%_% ymm3) (%_% ymm3) (Memop Word256 (%% (rdi,416))) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm3) *)
  0xc5; 0xed; 0x66; 0xa7; 0xc0; 0x01; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm4) (%_% ymm2) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xfe; 0xa7; 0xc0; 0x01; 0x00; 0x00;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm4) *)
  0xc5; 0xed; 0x66; 0xaf; 0xe0; 0x01; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm5) (%_% ymm2) (Memop Word256 (%% (rdi,480))) *)
  0xc5; 0xd5; 0xdb; 0xe9;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0xfe; 0xaf; 0xe0; 0x01; 0x00; 0x00;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (Memop Word256 (%% (rdi,480))) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm5) *)
  0xc5; 0xed; 0x66; 0x87; 0x00; 0x02; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm0) (%_% ymm2) (Memop Word256 (%% (rdi,512))) *)
  0xc5; 0xfd; 0xdb; 0xc1;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0xfe; 0x87; 0x00; 0x02; 0x00; 0x00;
                           (* VPADDD (%_% ymm0) (%_% ymm0) (Memop Word256 (%% (rdi,512))) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,512))) (%_% ymm0) *)
  0xc5; 0xed; 0x66; 0x9f; 0x20; 0x02; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm3) (%_% ymm2) (Memop Word256 (%% (rdi,544))) *)
  0xc5; 0xe5; 0xdb; 0xd9;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xe5; 0xfe; 0x9f; 0x20; 0x02; 0x00; 0x00;
                           (* VPADDD (%_% ymm3) (%_% ymm3) (Memop Word256 (%% (rdi,544))) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,544))) (%_% ymm3) *)
  0xc5; 0xed; 0x66; 0xa7; 0x40; 0x02; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm4) (%_% ymm2) (Memop Word256 (%% (rdi,576))) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xfe; 0xa7; 0x40; 0x02; 0x00; 0x00;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (Memop Word256 (%% (rdi,576))) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,576))) (%_% ymm4) *)
  0xc5; 0xed; 0x66; 0xaf; 0x60; 0x02; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm5) (%_% ymm2) (Memop Word256 (%% (rdi,608))) *)
  0xc5; 0xd5; 0xdb; 0xe9;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0xfe; 0xaf; 0x60; 0x02; 0x00; 0x00;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (Memop Word256 (%% (rdi,608))) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,608))) (%_% ymm5) *)
  0xc5; 0xed; 0x66; 0x87; 0x80; 0x02; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm0) (%_% ymm2) (Memop Word256 (%% (rdi,640))) *)
  0xc5; 0xfd; 0xdb; 0xc1;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0xfe; 0x87; 0x80; 0x02; 0x00; 0x00;
                           (* VPADDD (%_% ymm0) (%_% ymm0) (Memop Word256 (%% (rdi,640))) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,640))) (%_% ymm0) *)
  0xc5; 0xed; 0x66; 0x9f; 0xa0; 0x02; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm3) (%_% ymm2) (Memop Word256 (%% (rdi,672))) *)
  0xc5; 0xe5; 0xdb; 0xd9;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xe5; 0xfe; 0x9f; 0xa0; 0x02; 0x00; 0x00;
                           (* VPADDD (%_% ymm3) (%_% ymm3) (Memop Word256 (%% (rdi,672))) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,672))) (%_% ymm3) *)
  0xc5; 0xed; 0x66; 0xa7; 0xc0; 0x02; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm4) (%_% ymm2) (Memop Word256 (%% (rdi,704))) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xfe; 0xa7; 0xc0; 0x02; 0x00; 0x00;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (Memop Word256 (%% (rdi,704))) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,704))) (%_% ymm4) *)
  0xc5; 0xed; 0x66; 0xaf; 0xe0; 0x02; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm5) (%_% ymm2) (Memop Word256 (%% (rdi,736))) *)
  0xc5; 0xd5; 0xdb; 0xe9;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0xfe; 0xaf; 0xe0; 0x02; 0x00; 0x00;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (Memop Word256 (%% (rdi,736))) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,736))) (%_% ymm5) *)
  0xc5; 0xed; 0x66; 0x87; 0x00; 0x03; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm0) (%_% ymm2) (Memop Word256 (%% (rdi,768))) *)
  0xc5; 0xfd; 0xdb; 0xc1;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0xfe; 0x87; 0x00; 0x03; 0x00; 0x00;
                           (* VPADDD (%_% ymm0) (%_% ymm0) (Memop Word256 (%% (rdi,768))) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,768))) (%_% ymm0) *)
  0xc5; 0xed; 0x66; 0x9f; 0x20; 0x03; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm3) (%_% ymm2) (Memop Word256 (%% (rdi,800))) *)
  0xc5; 0xe5; 0xdb; 0xd9;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xe5; 0xfe; 0x9f; 0x20; 0x03; 0x00; 0x00;
                           (* VPADDD (%_% ymm3) (%_% ymm3) (Memop Word256 (%% (rdi,800))) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,800))) (%_% ymm3) *)
  0xc5; 0xed; 0x66; 0xa7; 0x40; 0x03; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm4) (%_% ymm2) (Memop Word256 (%% (rdi,832))) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xfe; 0xa7; 0x40; 0x03; 0x00; 0x00;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (Memop Word256 (%% (rdi,832))) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,832))) (%_% ymm4) *)
  0xc5; 0xed; 0x66; 0xaf; 0x60; 0x03; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm5) (%_% ymm2) (Memop Word256 (%% (rdi,864))) *)
  0xc5; 0xd5; 0xdb; 0xe9;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0xfe; 0xaf; 0x60; 0x03; 0x00; 0x00;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (Memop Word256 (%% (rdi,864))) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,864))) (%_% ymm5) *)
  0xc5; 0xed; 0x66; 0x87; 0x80; 0x03; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm0) (%_% ymm2) (Memop Word256 (%% (rdi,896))) *)
  0xc5; 0xfd; 0xdb; 0xc1;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0xfe; 0x87; 0x80; 0x03; 0x00; 0x00;
                           (* VPADDD (%_% ymm0) (%_% ymm0) (Memop Word256 (%% (rdi,896))) *)
  0xc5; 0xfd; 0x7f; 0x87; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,896))) (%_% ymm0) *)
  0xc5; 0xed; 0x66; 0x9f; 0xa0; 0x03; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm3) (%_% ymm2) (Memop Word256 (%% (rdi,928))) *)
  0xc5; 0xe5; 0xdb; 0xd9;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xe5; 0xfe; 0x9f; 0xa0; 0x03; 0x00; 0x00;
                           (* VPADDD (%_% ymm3) (%_% ymm3) (Memop Word256 (%% (rdi,928))) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,928))) (%_% ymm3) *)
  0xc5; 0xed; 0x66; 0xa7; 0xc0; 0x03; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm4) (%_% ymm2) (Memop Word256 (%% (rdi,960))) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xfe; 0xa7; 0xc0; 0x03; 0x00; 0x00;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (Memop Word256 (%% (rdi,960))) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,960))) (%_% ymm4) *)
  0xc5; 0xed; 0x66; 0xaf; 0xe0; 0x03; 0x00; 0x00;
                           (* VPCMPGTD (%_% ymm5) (%_% ymm2) (Memop Word256 (%% (rdi,992))) *)
  0xc5; 0xd5; 0xdb; 0xe9;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0xfe; 0xaf; 0xe0; 0x03; 0x00; 0x00;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (Memop Word256 (%% (rdi,992))) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,992))) (%_% ymm5) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let mldsa_caddq_tmc = define_trimmed "mldsa_caddq_tmc" mldsa_caddq_mc;;
let MLDSA_CADDQ_TMC_EXEC = X86_MK_CORE_EXEC_RULE mldsa_caddq_tmc;;

(* ------------------------------------------------------------------------- *)
(* Functional specification of mldsa_caddq                                   *)
(* ------------------------------------------------------------------------- *)

let mldsa_caddq = define
 `(mldsa_caddq:int32->int32) x =
   word_add x
    (word_and
      (if word_igt (word 0:int32) x then word 0xffffffff else word 0)
      (word 8380417))`;;

let mldsa_caddq_direct = prove
 (`!x:int32.
    ival(mldsa_caddq x) = if ival x < &0 then ival x + &8380417 else ival x`,
  REWRITE_TAC[mldsa_caddq] THEN BITBLAST_TAC);;

let mldsa_caddq_rem = prove
 (`!x:int32. abs(ival x) < &8380417
    ==> ival(mldsa_caddq x) = ival x rem &8380417`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mldsa_caddq_direct] THEN
  COND_CASES_TAC THENL [
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    REWRITE_TAC[INT_REM_UNIQUE] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    CONJ_TAC THENL [ASM_INT_ARITH_TAC; CONV_TAC INTEGER_RULE];
    MATCH_MP_TAC(GSYM INT_REM_LT) THEN
    ASM_INT_ARITH_TAC
  ]);;

let mldsa_caddq_bound = prove
 (`!x:int32. abs(ival x) < &8380417
    ==> &0 <= ival(mldsa_caddq x) /\ ival(mldsa_caddq x) < &8380417`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:int32` mldsa_caddq_rem) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`ival(x:int32)`; `&8380417:int`] INT_REM_POS) THEN
    INT_ARITH_TAC;
    MP_TAC(SPECL [`ival(x:int32)`; `&8380417:int`] INT_LT_REM) THEN
    INT_ARITH_TAC]);;

let mldsa_caddq_lower = prove
 (`!x:int32. abs(ival x) < &8380417
    ==> &0 <= ival(mldsa_caddq x)`,
  MESON_TAC[mldsa_caddq_bound]);;

let mldsa_caddq_upper = prove
 (`!x:int32. abs(ival x) < &8380417
    ==> ival(mldsa_caddq x) < &8380417`,
  MESON_TAC[mldsa_caddq_bound]);;

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_CADDQ_CORRECT = time prove
 (`!a x pc.
        aligned 32 a /\
        nonoverlapping (word pc,876) (a, 1024)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_caddq_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                          x i) /\
                  (!i. i < 256 ==> abs(ival(x i)) < &8380417))
             (\s. read RIP s = word(pc + 875) /\
                  (!i. i < 256
                      ==> ival(read(memory :> bytes32
                                 (word_add a (word(4 * i)))) s) =
                          ival(x i) rem &8380417) /\
                  (!i. i < 256
                      ==> &0 <= ival(read(memory :> bytes32
                                 (word_add a (word(4 * i)))) s) /\
                          ival(read(memory :> bytes32
                                 (word_add a (word(4 * i)))) s) < &8380417))
             (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5] ,,
              MAYCHANGE [RAX] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bytes(a,1024)])`,

  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; fst MLDSA_CADDQ_TMC_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [SOME_FLAGS; fst MLDSA_CADDQ_TMC_EXEC] THEN
  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `init_ymm1:int256` `read YMM1` THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 3
              (subst[mk_small_numeral(32*n),`n:num`]
                    `read (memory :> bytes256(word_add a (word n))) s0`))
              (0--31))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
  STRIP_TAC THEN
  MAP_EVERY (fun n ->
      X86_STEPS_TAC MLDSA_CADDQ_TMC_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[mldsa_caddq])
             (1--132) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
     CONV_RULE(SIMD_SIMPLIFY_CONV[mldsa_caddq]) o
     CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
     check (can (term_match [] `read qqq s132:int256 = xxx`) o concl))) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
           ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_ADD_SYM] THEN
  REWRITE_TAC[GSYM mldsa_caddq] THEN
  DISCARD_NONMATCHING_ASSUMPTIONS [`abs (ival t) < &8380417`] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC mldsa_caddq_rem) THEN
  TRY(MATCH_MP_TAC mldsa_caddq_lower) THEN
  TRY(MATCH_MP_TAC mldsa_caddq_upper) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine correctness theorem (includes return)                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_CADDQ_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mldsa_caddq_tmc) (a,1024) /\
        nonoverlapping (stackpointer,8) (a,1024)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_caddq_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                          x i) /\
                  (!i. i < 256 ==> abs(ival(x i)) < &8380417))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                      ==> ival(read(memory :> bytes32
                                 (word_add a (word(4 * i)))) s) =
                          ival(x i) rem &8380417) /\
                  (!i. i < 256
                      ==> &0 <= ival(read(memory :> bytes32
                                 (word_add a (word(4 * i)))) s) /\
                          ival(read(memory :> bytes32
                                 (word_add a (word(4 * i)))) s) < &8380417))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_caddq_tmc MLDSA_CADDQ_CORRECT);;

let MLDSA_CADDQ_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mldsa_caddq_mc) (a,1024) /\
        nonoverlapping (stackpointer,8) (a,1024)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_caddq_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                          x i) /\
                  (!i. i < 256 ==> abs(ival(x i)) < &8380417))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                      ==> ival(read(memory :> bytes32
                                 (word_add a (word(4 * i)))) s) =
                          ival(x i) rem &8380417) /\
                  (!i. i < 256
                      ==> &0 <= ival(read(memory :> bytes32
                                 (word_add a (word(4 * i)))) s) /\
                          ival(read(memory :> bytes32
                                 (word_add a (word(4 * i)))) s) < &8380417))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_CADDQ_NOIBT_SUBROUTINE_CORRECT));;

(* ========================================================================= *)
(* Constant-time and memory safety proof.                                    *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mldsa_caddq" subroutine_signatures)
    (REWRITE_RULE[SOME_FLAGS] MLDSA_CADDQ_CORRECT)
    MLDSA_CADDQ_TMC_EXEC;;

let MLDSA_CADDQ_SAFE = time prove
 (full_spec,
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLDSA_CADDQ_TMC_EXEC);;

let MLDSA_CADDQ_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a pc stackpointer returnaddress.
          aligned 32 a /\
          nonoverlapping (word pc, LENGTH mldsa_caddq_tmc) (a, 1024) /\
          nonoverlapping (stackpointer, 8) (a, 1024)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_caddq_tmc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [a,1024; stackpointer,8]
                                               [a,1024; stackpointer,8]))
               (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_caddq_tmc MLDSA_CADDQ_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLDSA_CADDQ_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a pc stackpointer returnaddress.
          aligned 32 a /\
          nonoverlapping (word pc, LENGTH mldsa_caddq_mc) (a, 1024) /\
          nonoverlapping (stackpointer, 8) (a, 1024)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_caddq_mc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [a,1024; stackpointer,8]
                                               [a,1024; stackpointer,8]))
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_CADDQ_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let mldsa_caddq_windows_mc = define_from_elf
   "mldsa_caddq_windows_mc" "x86/mldsa/mldsa_caddq.obj";;

let mldsa_caddq_windows_tmc =
  define_trimmed "mldsa_caddq_windows_tmc" mldsa_caddq_windows_mc;;

let MLDSA_CADDQ_WINDOWS_TMC_EXEC =
  X86_MK_EXEC_RULE mldsa_caddq_windows_tmc;;

let MLDSA_CADDQ_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mldsa_caddq_windows_tmc) (a,1024) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (a,1024) /\
        nonoverlapping (word pc,LENGTH mldsa_caddq_windows_tmc)
                       (word_sub stackpointer (word 16),16)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) mldsa_caddq_windows_tmc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a] s /\
                   (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           x i) /\
                   (!i. i < 256 ==> abs(ival(x i)) < &8380417))
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   (!i. i < 256
                       ==> ival(read(memory :> bytes32
                                  (word_add a (word(4 * i)))) s) =
                           ival(x i) rem &8380417) /\
                   (!i. i < 256
                       ==> &0 <= ival(read(memory :> bytes32
                                  (word_add a (word(4 * i)))) s) /\
                           ival(read(memory :> bytes32
                                  (word_add a (word(4 * i)))) s) < &8380417))
              (MAYCHANGE [RSP] ,,
               WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)] ,,
               MAYCHANGE [memory :> bytes(a,1024)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC mldsa_caddq_windows_tmc mldsa_caddq_tmc
      MLDSA_CADDQ_CORRECT);;

let MLDSA_CADDQ_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mldsa_caddq_windows_mc) (a,1024) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (a,1024) /\
        nonoverlapping (word pc,LENGTH mldsa_caddq_windows_mc)
                       (word_sub stackpointer (word 16),16)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) mldsa_caddq_windows_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a] s /\
                   (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           x i) /\
                   (!i. i < 256 ==> abs(ival(x i)) < &8380417))
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   (!i. i < 256
                       ==> ival(read(memory :> bytes32
                                  (word_add a (word(4 * i)))) s) =
                           ival(x i) rem &8380417) /\
                   (!i. i < 256
                       ==> &0 <= ival(read(memory :> bytes32
                                  (word_add a (word(4 * i)))) s) /\
                           ival(read(memory :> bytes32
                                  (word_add a (word(4 * i)))) s) < &8380417))
              (MAYCHANGE [RSP] ,,
               WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)] ,,
               MAYCHANGE [memory :> bytes(a,1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_CADDQ_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

(* Windows safety proofs *)

let MLDSA_CADDQ_NOIBT_WINDOWS_SUBROUTINE_SAFE = prove
 (`exists f_events. forall e a pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc, LENGTH mldsa_caddq_windows_tmc) (a, 1024) /\
        nonoverlapping (word_sub stackpointer (word 16), 24) (a, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_caddq_windows_tmc)
                       (word_sub stackpointer (word 16), 16)
        ==> ensures x86
              (\s.
                  bytes_loaded s (word pc) mldsa_caddq_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [a] s /\
                  read events s = e)
              (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a pc (word_sub stackpointer (word 16)) returnaddress /\
                        memaccess_inbounds e2
                          [a,1024; word_sub stackpointer (word 16),24]
                          [a,1024; word_sub stackpointer (word 16),16]))
              (MAYCHANGE [RSP] ,,
               WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16), 16)] ,,
               MAYCHANGE [memory :> bytes(a, 1024)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC mldsa_caddq_windows_tmc mldsa_caddq_tmc
      MLDSA_CADDQ_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLDSA_CADDQ_WINDOWS_SUBROUTINE_SAFE = prove
 (`exists f_events. forall e a pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc, LENGTH mldsa_caddq_windows_mc) (a, 1024) /\
        nonoverlapping (word_sub stackpointer (word 16), 24) (a, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_caddq_windows_mc)
                       (word_sub stackpointer (word 16), 16)
        ==> ensures x86
              (\s.
                  bytes_loaded s (word pc) mldsa_caddq_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [a] s /\
                  read events s = e)
              (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a pc (word_sub stackpointer (word 16)) returnaddress /\
                        memaccess_inbounds e2
                          [a,1024; word_sub stackpointer (word 16),24]
                          [a,1024; word_sub stackpointer (word 16),16]))
              (MAYCHANGE [RSP] ,,
               WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16), 16)] ,,
               MAYCHANGE [memory :> bytes(a, 1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_CADDQ_NOIBT_WINDOWS_SUBROUTINE_SAFE));;
