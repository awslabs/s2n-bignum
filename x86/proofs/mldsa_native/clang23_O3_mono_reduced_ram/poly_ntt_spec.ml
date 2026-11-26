(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform: the statement. This is the code for   *)
(* mldsa_poly_ntt (mld_poly_ntt in poly.c, which calls mld_poly_ntt_c) from  *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3 as *)
(* one translation unit with MLD_CONFIG_REDUCE_RAM (see                      *)
(* mldsa_native/README.md). clang has unrolled the loops over the 8 layers:  *)
(* layers 1 to 3 are SSE loops that process 4 coefficients per instruction,  *)
(* with the zetas in constants (mldsa_poly_ntt_consts, 256 bytes of read-    *)
(* only data), and layers 4 to 8 are loops over the blocks of the layer in   *)
(* scalar and SSE code, which read the zetas from the table mld_zetas. It is *)
(* verified in the whole image (see libmldsa.ml) against mld_poly_ntt of     *)
(* common/mldsa_native_poly.ml. It is also shown to be constant time and     *)
(* memory safe: the readable memory includes the constants.                  *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_poly.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_ntt:
       +0x0: mov     $0xfffffffffffffe00,%rax
       +0x7: pxor    %xmm2,%xmm2
       +0xb: movdqa  0x1d5dd(%rip),%xmm3
      +0x13: movdqa  0x1d5e5(%rip),%xmm4
      +0x1b: movdqa  0x1d5ed(%rip),%xmm0
      +0x23: movdqa  0x1d5f5(%rip),%xmm1
      +0x2b: nopl    0x0(%rax,%rax,1)
      +0x30: movdqu  0x200(%rdi,%rax,1),%xmm5
      +0x39: movdqu  0x400(%rdi,%rax,1),%xmm6
      +0x42: pxor    %xmm8,%xmm8
      +0x47: pcmpgtd %xmm6,%xmm8
      +0x4c: pshufd  $0xee,%xmm6,%xmm7
      +0x51: punpckldq %xmm8,%xmm6
      +0x56: pxor    %xmm9,%xmm9
      +0x5b: pcmpgtd %xmm7,%xmm9
      +0x60: punpckldq %xmm9,%xmm7
      +0x65: movdqa  %xmm7,%xmm10
      +0x6a: pmuludq %xmm3,%xmm10
      +0x6f: punpckldq %xmm2,%xmm9
      +0x74: pmuludq %xmm3,%xmm9
      +0x79: psllq   $0x20,%xmm9
      +0x7f: paddq   %xmm10,%xmm9
      +0x84: movdqa  %xmm6,%xmm10
      +0x89: pmuludq %xmm3,%xmm10
      +0x8e: punpckldq %xmm2,%xmm8
      +0x93: pmuludq %xmm3,%xmm8
      +0x98: psllq   $0x20,%xmm8
      +0x9e: paddq   %xmm10,%xmm8
      +0xa3: pmuludq %xmm4,%xmm7
      +0xa7: pmuludq %xmm4,%xmm6
      +0xab: pshufd  $0xe8,%xmm6,%xmm10
      +0xb1: psllq   $0x20,%xmm6
      +0xb6: psrad   $0x1f,%xmm6
      +0xbb: pshufd  $0xed,%xmm6,%xmm11
      +0xc1: punpckldq %xmm11,%xmm10
      +0xc6: pshufd  $0xe8,%xmm7,%xmm11
      +0xcc: psllq   $0x20,%xmm7
      +0xd1: psrad   $0x1f,%xmm7
      +0xd6: pshufd  $0xed,%xmm7,%xmm12
      +0xdc: punpckldq %xmm12,%xmm11
      +0xe1: movdqa  %xmm11,%xmm12
      +0xe6: pmuludq %xmm0,%xmm12
      +0xeb: paddq   %xmm9,%xmm12
      +0xf0: pmuludq %xmm1,%xmm11
      +0xf5: psrlq   $0x20,%xmm7
      +0xfa: pmuludq %xmm0,%xmm7
      +0xfe: paddq   %xmm11,%xmm7
     +0x103: psllq   $0x20,%xmm7
     +0x108: paddq   %xmm12,%xmm7
     +0x10d: movdqa  %xmm10,%xmm9
     +0x112: pmuludq %xmm0,%xmm9
     +0x117: paddq   %xmm8,%xmm9
     +0x11c: pmuludq %xmm1,%xmm10
     +0x121: psrlq   $0x20,%xmm6
     +0x126: pmuludq %xmm0,%xmm6
     +0x12a: paddq   %xmm10,%xmm6
     +0x12f: psllq   $0x20,%xmm6
     +0x134: paddq   %xmm9,%xmm6
     +0x139: shufps  $0xdd,%xmm7,%xmm6
     +0x13d: movdqa  %xmm5,%xmm7
     +0x141: psubd   %xmm6,%xmm7
     +0x145: movdqu  %xmm7,0x400(%rdi,%rax,1)
     +0x14e: paddd   %xmm5,%xmm6
     +0x152: movdqu  %xmm6,0x200(%rdi,%rax,1)
     +0x15b: add     $0x10,%rax
     +0x15f: jne     <mldsa_poly_ntt+0x30>
     +0x165: mov     $0xffffffffffffff00,%rax
     +0x16c: pxor    %xmm2,%xmm2
     +0x170: movdqa  0x1d4b8(%rip),%xmm3
     +0x178: movdqa  0x1d4c0(%rip),%xmm4
     +0x180: movdqu  0x100(%rdi,%rax,1),%xmm5
     +0x189: movdqu  0x200(%rdi,%rax,1),%xmm6
     +0x192: pxor    %xmm8,%xmm8
     +0x197: pcmpgtd %xmm6,%xmm8
     +0x19c: pshufd  $0xee,%xmm6,%xmm7
     +0x1a1: punpckldq %xmm8,%xmm6
     +0x1a6: pxor    %xmm9,%xmm9
     +0x1ab: pcmpgtd %xmm7,%xmm9
     +0x1b0: punpckldq %xmm9,%xmm7
     +0x1b5: movdqa  %xmm7,%xmm10
     +0x1ba: pmuludq %xmm3,%xmm10
     +0x1bf: movdqa  %xmm7,%xmm11
     +0x1c4: pmuludq %xmm1,%xmm11
     +0x1c9: punpckldq %xmm2,%xmm9
     +0x1ce: pmuludq %xmm3,%xmm9
     +0x1d3: paddq   %xmm11,%xmm9
     +0x1d8: psllq   $0x20,%xmm9
     +0x1de: paddq   %xmm10,%xmm9
     +0x1e3: movdqa  %xmm6,%xmm10
     +0x1e8: pmuludq %xmm3,%xmm10
     +0x1ed: movdqa  %xmm6,%xmm11
     +0x1f2: pmuludq %xmm1,%xmm11
     +0x1f7: punpckldq %xmm2,%xmm8
     +0x1fc: pmuludq %xmm3,%xmm8
     +0x201: paddq   %xmm11,%xmm8
     +0x206: psllq   $0x20,%xmm8
     +0x20c: paddq   %xmm10,%xmm8
     +0x211: pmuludq %xmm4,%xmm7
     +0x215: pmuludq %xmm4,%xmm6
     +0x219: pshufd  $0xe8,%xmm6,%xmm10
     +0x21f: psllq   $0x20,%xmm6
     +0x224: psrad   $0x1f,%xmm6
     +0x229: pshufd  $0xed,%xmm6,%xmm11
     +0x22f: punpckldq %xmm11,%xmm10
     +0x234: pshufd  $0xe8,%xmm7,%xmm11
     +0x23a: psllq   $0x20,%xmm7
     +0x23f: psrad   $0x1f,%xmm7
     +0x244: pshufd  $0xed,%xmm7,%xmm12
     +0x24a: punpckldq %xmm12,%xmm11
     +0x24f: movdqa  %xmm11,%xmm12
     +0x254: pmuludq %xmm0,%xmm12
     +0x259: paddq   %xmm9,%xmm12
     +0x25e: pmuludq %xmm1,%xmm11
     +0x263: psrlq   $0x20,%xmm7
     +0x268: pmuludq %xmm0,%xmm7
     +0x26c: paddq   %xmm11,%xmm7
     +0x271: psllq   $0x20,%xmm7
     +0x276: paddq   %xmm12,%xmm7
     +0x27b: movdqa  %xmm10,%xmm9
     +0x280: pmuludq %xmm0,%xmm9
     +0x285: paddq   %xmm8,%xmm9
     +0x28a: pmuludq %xmm1,%xmm10
     +0x28f: psrlq   $0x20,%xmm6
     +0x294: pmuludq %xmm0,%xmm6
     +0x298: paddq   %xmm10,%xmm6
     +0x29d: psllq   $0x20,%xmm6
     +0x2a2: paddq   %xmm9,%xmm6
     +0x2a7: shufps  $0xdd,%xmm7,%xmm6
     +0x2ab: movdqa  %xmm5,%xmm7
     +0x2af: psubd   %xmm6,%xmm7
     +0x2b3: movdqu  %xmm7,0x200(%rdi,%rax,1)
     +0x2bc: paddd   %xmm5,%xmm6
     +0x2c0: movdqu  %xmm6,0x100(%rdi,%rax,1)
     +0x2c9: add     $0x10,%rax
     +0x2cd: jne     <mldsa_poly_ntt+0x180>
     +0x2d3: mov     $0xffffffffffffff00,%rax
     +0x2da: pxor    %xmm2,%xmm2
     +0x2de: movdqa  0x1d36a(%rip),%xmm3
     +0x2e6: movdqa  0x1d372(%rip),%xmm4
     +0x2ee: xchg    %ax,%ax
     +0x2f0: movdqu  0x300(%rdi,%rax,1),%xmm5
     +0x2f9: movdqu  0x400(%rdi,%rax,1),%xmm6
     +0x302: pxor    %xmm8,%xmm8
     +0x307: pcmpgtd %xmm6,%xmm8
     +0x30c: pshufd  $0xee,%xmm6,%xmm7
     +0x311: punpckldq %xmm8,%xmm6
     +0x316: pxor    %xmm9,%xmm9
     +0x31b: pcmpgtd %xmm7,%xmm9
     +0x320: punpckldq %xmm9,%xmm7
     +0x325: movdqa  %xmm7,%xmm10
     +0x32a: pmuludq %xmm3,%xmm10
     +0x32f: movdqa  %xmm7,%xmm11
     +0x334: pmuludq %xmm1,%xmm11
     +0x339: punpckldq %xmm2,%xmm9
     +0x33e: pmuludq %xmm3,%xmm9
     +0x343: paddq   %xmm11,%xmm9
     +0x348: psllq   $0x20,%xmm9
     +0x34e: paddq   %xmm10,%xmm9
     +0x353: movdqa  %xmm6,%xmm10
     +0x358: pmuludq %xmm3,%xmm10
     +0x35d: movdqa  %xmm6,%xmm11
     +0x362: pmuludq %xmm1,%xmm11
     +0x367: punpckldq %xmm2,%xmm8
     +0x36c: pmuludq %xmm3,%xmm8
     +0x371: paddq   %xmm11,%xmm8
     +0x376: psllq   $0x20,%xmm8
     +0x37c: paddq   %xmm10,%xmm8
     +0x381: pmuludq %xmm4,%xmm7
     +0x385: pmuludq %xmm4,%xmm6
     +0x389: pshufd  $0xe8,%xmm6,%xmm10
     +0x38f: psllq   $0x20,%xmm6
     +0x394: psrad   $0x1f,%xmm6
     +0x399: pshufd  $0xed,%xmm6,%xmm11
     +0x39f: punpckldq %xmm11,%xmm10
     +0x3a4: pshufd  $0xe8,%xmm7,%xmm11
     +0x3aa: psllq   $0x20,%xmm7
     +0x3af: psrad   $0x1f,%xmm7
     +0x3b4: pshufd  $0xed,%xmm7,%xmm12
     +0x3ba: punpckldq %xmm12,%xmm11
     +0x3bf: movdqa  %xmm11,%xmm12
     +0x3c4: pmuludq %xmm0,%xmm12
     +0x3c9: paddq   %xmm9,%xmm12
     +0x3ce: pmuludq %xmm1,%xmm11
     +0x3d3: psrlq   $0x20,%xmm7
     +0x3d8: pmuludq %xmm0,%xmm7
     +0x3dc: paddq   %xmm11,%xmm7
     +0x3e1: psllq   $0x20,%xmm7
     +0x3e6: paddq   %xmm12,%xmm7
     +0x3eb: movdqa  %xmm10,%xmm9
     +0x3f0: pmuludq %xmm0,%xmm9
     +0x3f5: paddq   %xmm8,%xmm9
     +0x3fa: pmuludq %xmm1,%xmm10
     +0x3ff: psrlq   $0x20,%xmm6
     +0x404: pmuludq %xmm0,%xmm6
     +0x408: paddq   %xmm10,%xmm6
     +0x40d: psllq   $0x20,%xmm6
     +0x412: paddq   %xmm9,%xmm6
     +0x417: shufps  $0xdd,%xmm7,%xmm6
     +0x41b: movdqa  %xmm5,%xmm7
     +0x41f: psubd   %xmm6,%xmm7
     +0x423: movdqu  %xmm7,0x400(%rdi,%rax,1)
     +0x42c: paddd   %xmm5,%xmm6
     +0x430: movdqu  %xmm6,0x300(%rdi,%rax,1)
     +0x439: add     $0x10,%rax
     +0x43d: jne     <mldsa_poly_ntt+0x2f0>
     +0x443: mov     $0xffffffffffffff80,%rax
     +0x44a: pxor    %xmm2,%xmm2
     +0x44e: movdqa  0x1d21a(%rip),%xmm3
     +0x456: movdqa  0x1d222(%rip),%xmm4
     +0x45e: xchg    %ax,%ax
     +0x460: movdqu  0x80(%rdi,%rax,1),%xmm5
     +0x469: movdqu  0x100(%rdi,%rax,1),%xmm6
     +0x472: pxor    %xmm8,%xmm8
     +0x477: pcmpgtd %xmm6,%xmm8
     +0x47c: pshufd  $0xee,%xmm6,%xmm7
     +0x481: punpckldq %xmm8,%xmm6
     +0x486: pxor    %xmm9,%xmm9
     +0x48b: pcmpgtd %xmm7,%xmm9
     +0x490: punpckldq %xmm9,%xmm7
     +0x495: movdqa  %xmm7,%xmm10
     +0x49a: pmuludq %xmm3,%xmm10
     +0x49f: punpckldq %xmm2,%xmm9
     +0x4a4: pmuludq %xmm3,%xmm9
     +0x4a9: psllq   $0x20,%xmm9
     +0x4af: paddq   %xmm10,%xmm9
     +0x4b4: movdqa  %xmm6,%xmm10
     +0x4b9: pmuludq %xmm3,%xmm10
     +0x4be: punpckldq %xmm2,%xmm8
     +0x4c3: pmuludq %xmm3,%xmm8
     +0x4c8: psllq   $0x20,%xmm8
     +0x4ce: paddq   %xmm10,%xmm8
     +0x4d3: pmuludq %xmm4,%xmm7
     +0x4d7: pmuludq %xmm4,%xmm6
     +0x4db: pshufd  $0xe8,%xmm6,%xmm10
     +0x4e1: psllq   $0x20,%xmm6
     +0x4e6: psrad   $0x1f,%xmm6
     +0x4eb: pshufd  $0xed,%xmm6,%xmm11
     +0x4f1: punpckldq %xmm11,%xmm10
     +0x4f6: pshufd  $0xe8,%xmm7,%xmm11
     +0x4fc: psllq   $0x20,%xmm7
     +0x501: psrad   $0x1f,%xmm7
     +0x506: pshufd  $0xed,%xmm7,%xmm12
     +0x50c: punpckldq %xmm12,%xmm11
     +0x511: movdqa  %xmm11,%xmm12
     +0x516: pmuludq %xmm0,%xmm12
     +0x51b: paddq   %xmm9,%xmm12
     +0x520: pmuludq %xmm1,%xmm11
     +0x525: psrlq   $0x20,%xmm7
     +0x52a: pmuludq %xmm0,%xmm7
     +0x52e: paddq   %xmm11,%xmm7
     +0x533: psllq   $0x20,%xmm7
     +0x538: paddq   %xmm12,%xmm7
     +0x53d: movdqa  %xmm10,%xmm9
     +0x542: pmuludq %xmm0,%xmm9
     +0x547: paddq   %xmm8,%xmm9
     +0x54c: pmuludq %xmm1,%xmm10
     +0x551: psrlq   $0x20,%xmm6
     +0x556: pmuludq %xmm0,%xmm6
     +0x55a: paddq   %xmm10,%xmm6
     +0x55f: psllq   $0x20,%xmm6
     +0x564: paddq   %xmm9,%xmm6
     +0x569: shufps  $0xdd,%xmm7,%xmm6
     +0x56d: movdqa  %xmm5,%xmm7
     +0x571: psubd   %xmm6,%xmm7
     +0x575: movdqu  %xmm7,0x100(%rdi,%rax,1)
     +0x57e: paddd   %xmm5,%xmm6
     +0x582: movdqu  %xmm6,0x80(%rdi,%rax,1)
     +0x58b: add     $0x10,%rax
     +0x58f: jne     <mldsa_poly_ntt+0x460>
     +0x595: mov     $0xffffffffffffff80,%rax
     +0x59c: pxor    %xmm2,%xmm2
     +0x5a0: movdqa  0x1d0e8(%rip),%xmm3
     +0x5a8: movdqa  0x1d0f0(%rip),%xmm4
     +0x5b0: movdqu  0x180(%rdi,%rax,1),%xmm5
     +0x5b9: movdqu  0x200(%rdi,%rax,1),%xmm6
     +0x5c2: pxor    %xmm8,%xmm8
     +0x5c7: pcmpgtd %xmm6,%xmm8
     +0x5cc: pshufd  $0xee,%xmm6,%xmm7
     +0x5d1: punpckldq %xmm8,%xmm6
     +0x5d6: pxor    %xmm9,%xmm9
     +0x5db: pcmpgtd %xmm7,%xmm9
     +0x5e0: punpckldq %xmm9,%xmm7
     +0x5e5: movdqa  %xmm7,%xmm10
     +0x5ea: pmuludq %xmm3,%xmm10
     +0x5ef: movdqa  %xmm7,%xmm11
     +0x5f4: pmuludq %xmm1,%xmm11
     +0x5f9: punpckldq %xmm2,%xmm9
     +0x5fe: pmuludq %xmm3,%xmm9
     +0x603: paddq   %xmm11,%xmm9
     +0x608: psllq   $0x20,%xmm9
     +0x60e: paddq   %xmm10,%xmm9
     +0x613: movdqa  %xmm6,%xmm10
     +0x618: pmuludq %xmm3,%xmm10
     +0x61d: movdqa  %xmm6,%xmm11
     +0x622: pmuludq %xmm1,%xmm11
     +0x627: punpckldq %xmm2,%xmm8
     +0x62c: pmuludq %xmm3,%xmm8
     +0x631: paddq   %xmm11,%xmm8
     +0x636: psllq   $0x20,%xmm8
     +0x63c: paddq   %xmm10,%xmm8
     +0x641: pmuludq %xmm4,%xmm7
     +0x645: pmuludq %xmm4,%xmm6
     +0x649: pshufd  $0xe8,%xmm6,%xmm10
     +0x64f: psllq   $0x20,%xmm6
     +0x654: psrad   $0x1f,%xmm6
     +0x659: pshufd  $0xed,%xmm6,%xmm11
     +0x65f: punpckldq %xmm11,%xmm10
     +0x664: pshufd  $0xe8,%xmm7,%xmm11
     +0x66a: psllq   $0x20,%xmm7
     +0x66f: psrad   $0x1f,%xmm7
     +0x674: pshufd  $0xed,%xmm7,%xmm12
     +0x67a: punpckldq %xmm12,%xmm11
     +0x67f: movdqa  %xmm11,%xmm12
     +0x684: pmuludq %xmm0,%xmm12
     +0x689: paddq   %xmm9,%xmm12
     +0x68e: pmuludq %xmm1,%xmm11
     +0x693: psrlq   $0x20,%xmm7
     +0x698: pmuludq %xmm0,%xmm7
     +0x69c: paddq   %xmm11,%xmm7
     +0x6a1: psllq   $0x20,%xmm7
     +0x6a6: paddq   %xmm12,%xmm7
     +0x6ab: movdqa  %xmm10,%xmm9
     +0x6b0: pmuludq %xmm0,%xmm9
     +0x6b5: paddq   %xmm8,%xmm9
     +0x6ba: pmuludq %xmm1,%xmm10
     +0x6bf: psrlq   $0x20,%xmm6
     +0x6c4: pmuludq %xmm0,%xmm6
     +0x6c8: paddq   %xmm10,%xmm6
     +0x6cd: psllq   $0x20,%xmm6
     +0x6d2: paddq   %xmm9,%xmm6
     +0x6d7: shufps  $0xdd,%xmm7,%xmm6
     +0x6db: movdqa  %xmm5,%xmm7
     +0x6df: psubd   %xmm6,%xmm7
     +0x6e3: movdqu  %xmm7,0x200(%rdi,%rax,1)
     +0x6ec: paddd   %xmm5,%xmm6
     +0x6f0: movdqu  %xmm6,0x180(%rdi,%rax,1)
     +0x6f9: add     $0x10,%rax
     +0x6fd: jne     <mldsa_poly_ntt+0x5b0>
     +0x703: mov     $0xffffffffffffff80,%rax
     +0x70a: pxor    %xmm2,%xmm2
     +0x70e: movdqa  0x1cf9a(%rip),%xmm3
     +0x716: movdqa  0x1cfa2(%rip),%xmm4
     +0x71e: xchg    %ax,%ax
     +0x720: movdqu  0x280(%rdi,%rax,1),%xmm5
     +0x729: movdqu  0x300(%rdi,%rax,1),%xmm6
     +0x732: pxor    %xmm8,%xmm8
     +0x737: pcmpgtd %xmm6,%xmm8
     +0x73c: pshufd  $0xee,%xmm6,%xmm7
     +0x741: punpckldq %xmm8,%xmm6
     +0x746: pxor    %xmm9,%xmm9
     +0x74b: pcmpgtd %xmm7,%xmm9
     +0x750: punpckldq %xmm9,%xmm7
     +0x755: movdqa  %xmm7,%xmm10
     +0x75a: pmuludq %xmm3,%xmm10
     +0x75f: movdqa  %xmm7,%xmm11
     +0x764: pmuludq %xmm1,%xmm11
     +0x769: punpckldq %xmm2,%xmm9
     +0x76e: pmuludq %xmm3,%xmm9
     +0x773: paddq   %xmm11,%xmm9
     +0x778: psllq   $0x20,%xmm9
     +0x77e: paddq   %xmm10,%xmm9
     +0x783: movdqa  %xmm6,%xmm10
     +0x788: pmuludq %xmm3,%xmm10
     +0x78d: movdqa  %xmm6,%xmm11
     +0x792: pmuludq %xmm1,%xmm11
     +0x797: punpckldq %xmm2,%xmm8
     +0x79c: pmuludq %xmm3,%xmm8
     +0x7a1: paddq   %xmm11,%xmm8
     +0x7a6: psllq   $0x20,%xmm8
     +0x7ac: paddq   %xmm10,%xmm8
     +0x7b1: pmuludq %xmm4,%xmm7
     +0x7b5: pmuludq %xmm4,%xmm6
     +0x7b9: pshufd  $0xe8,%xmm6,%xmm10
     +0x7bf: psllq   $0x20,%xmm6
     +0x7c4: psrad   $0x1f,%xmm6
     +0x7c9: pshufd  $0xed,%xmm6,%xmm11
     +0x7cf: punpckldq %xmm11,%xmm10
     +0x7d4: pshufd  $0xe8,%xmm7,%xmm11
     +0x7da: psllq   $0x20,%xmm7
     +0x7df: psrad   $0x1f,%xmm7
     +0x7e4: pshufd  $0xed,%xmm7,%xmm12
     +0x7ea: punpckldq %xmm12,%xmm11
     +0x7ef: movdqa  %xmm11,%xmm12
     +0x7f4: pmuludq %xmm0,%xmm12
     +0x7f9: paddq   %xmm9,%xmm12
     +0x7fe: pmuludq %xmm1,%xmm11
     +0x803: psrlq   $0x20,%xmm7
     +0x808: pmuludq %xmm0,%xmm7
     +0x80c: paddq   %xmm11,%xmm7
     +0x811: psllq   $0x20,%xmm7
     +0x816: paddq   %xmm12,%xmm7
     +0x81b: movdqa  %xmm10,%xmm9
     +0x820: pmuludq %xmm0,%xmm9
     +0x825: paddq   %xmm8,%xmm9
     +0x82a: pmuludq %xmm1,%xmm10
     +0x82f: psrlq   $0x20,%xmm6
     +0x834: pmuludq %xmm0,%xmm6
     +0x838: paddq   %xmm10,%xmm6
     +0x83d: psllq   $0x20,%xmm6
     +0x842: paddq   %xmm9,%xmm6
     +0x847: shufps  $0xdd,%xmm7,%xmm6
     +0x84b: movdqa  %xmm5,%xmm7
     +0x84f: psubd   %xmm6,%xmm7
     +0x853: movdqu  %xmm7,0x300(%rdi,%rax,1)
     +0x85c: paddd   %xmm5,%xmm6
     +0x860: movdqu  %xmm6,0x280(%rdi,%rax,1)
     +0x869: add     $0x10,%rax
     +0x86d: jne     <mldsa_poly_ntt+0x720>
     +0x873: mov     $0xffffffffffffff80,%rax
     +0x87a: pxor    %xmm2,%xmm2
     +0x87e: movdqa  0x1ce4a(%rip),%xmm3
     +0x886: movdqa  0x1ce52(%rip),%xmm4
     +0x88e: xchg    %ax,%ax
     +0x890: movdqu  0x380(%rdi,%rax,1),%xmm5
     +0x899: movdqu  0x400(%rdi,%rax,1),%xmm6
     +0x8a2: pxor    %xmm8,%xmm8
     +0x8a7: pcmpgtd %xmm6,%xmm8
     +0x8ac: pshufd  $0xee,%xmm6,%xmm7
     +0x8b1: punpckldq %xmm8,%xmm6
     +0x8b6: pxor    %xmm9,%xmm9
     +0x8bb: pcmpgtd %xmm7,%xmm9
     +0x8c0: punpckldq %xmm9,%xmm7
     +0x8c5: movdqa  %xmm7,%xmm10
     +0x8ca: pmuludq %xmm3,%xmm10
     +0x8cf: punpckldq %xmm2,%xmm9
     +0x8d4: pmuludq %xmm3,%xmm9
     +0x8d9: psllq   $0x20,%xmm9
     +0x8df: paddq   %xmm10,%xmm9
     +0x8e4: movdqa  %xmm6,%xmm10
     +0x8e9: pmuludq %xmm3,%xmm10
     +0x8ee: punpckldq %xmm2,%xmm8
     +0x8f3: pmuludq %xmm3,%xmm8
     +0x8f8: psllq   $0x20,%xmm8
     +0x8fe: paddq   %xmm10,%xmm8
     +0x903: pmuludq %xmm4,%xmm7
     +0x907: pmuludq %xmm4,%xmm6
     +0x90b: pshufd  $0xe8,%xmm6,%xmm10
     +0x911: psllq   $0x20,%xmm6
     +0x916: psrad   $0x1f,%xmm6
     +0x91b: pshufd  $0xed,%xmm6,%xmm11
     +0x921: punpckldq %xmm11,%xmm10
     +0x926: pshufd  $0xe8,%xmm7,%xmm11
     +0x92c: psllq   $0x20,%xmm7
     +0x931: psrad   $0x1f,%xmm7
     +0x936: pshufd  $0xed,%xmm7,%xmm12
     +0x93c: punpckldq %xmm12,%xmm11
     +0x941: movdqa  %xmm11,%xmm12
     +0x946: pmuludq %xmm0,%xmm12
     +0x94b: paddq   %xmm9,%xmm12
     +0x950: pmuludq %xmm1,%xmm11
     +0x955: psrlq   $0x20,%xmm7
     +0x95a: pmuludq %xmm0,%xmm7
     +0x95e: paddq   %xmm11,%xmm7
     +0x963: psllq   $0x20,%xmm7
     +0x968: paddq   %xmm12,%xmm7
     +0x96d: movdqa  %xmm10,%xmm9
     +0x972: pmuludq %xmm0,%xmm9
     +0x977: paddq   %xmm8,%xmm9
     +0x97c: pmuludq %xmm1,%xmm10
     +0x981: psrlq   $0x20,%xmm6
     +0x986: pmuludq %xmm0,%xmm6
     +0x98a: paddq   %xmm10,%xmm6
     +0x98f: psllq   $0x20,%xmm6
     +0x994: paddq   %xmm9,%xmm6
     +0x999: shufps  $0xdd,%xmm7,%xmm6
     +0x99d: movdqa  %xmm5,%xmm7
     +0x9a1: psubd   %xmm6,%xmm7
     +0x9a5: movdqu  %xmm7,0x400(%rdi,%rax,1)
     +0x9ae: paddd   %xmm5,%xmm6
     +0x9b2: movdqu  %xmm6,0x380(%rdi,%rax,1)
     +0x9bb: add     $0x10,%rax
     +0x9bf: jne     <mldsa_poly_ntt+0x890>
     +0x9c5: push    %rbx
     +0x9c6: movabs  $0x380200100000000,%rax
     +0x9d0: lea     0x7c(%rdi),%rdx
     +0x9d4: xor     %esi,%esi
     +0x9d6: lea     0x1d013(%rip),%rcx
     +0x9dd: nopl    (%rax)
     +0x9e0: movslq  0x20(%rcx,%rsi,4),%r8
     +0x9e5: movslq  -0x3c(%rdx),%r9
     +0x9e9: imul    %r8,%r9
     +0x9ed: mov     %r9,%r10
     +0x9f0: imul    %rax,%r10
     +0x9f4: sar     $0x20,%r10
     +0x9f8: imul    $0xffffffffff801fff,%r10,%r10
     +0x9ff: add     %r9,%r10
     +0xa02: shr     $0x20,%r10
     +0xa06: mov     -0x7c(%rdx),%r9d
     +0xa0a: mov     -0x78(%rdx),%r11d
     +0xa0e: mov     %r9d,%ebx
     +0xa11: sub     %r10d,%ebx
     +0xa14: mov     %ebx,-0x3c(%rdx)
     +0xa17: add     %r10d,%r9d
     +0xa1a: mov     %r9d,-0x7c(%rdx)
     +0xa1e: movslq  -0x38(%rdx),%r9
     +0xa22: imul    %r8,%r9
     +0xa26: mov     %r9,%r10
     +0xa29: imul    %rax,%r10
     +0xa2d: sar     $0x20,%r10
     +0xa31: imul    $0xffffffffff801fff,%r10,%r10
     +0xa38: add     %r9,%r10
     +0xa3b: shr     $0x20,%r10
     +0xa3f: mov     %r11d,%r9d
     +0xa42: sub     %r10d,%r9d
     +0xa45: mov     %r9d,-0x38(%rdx)
     +0xa49: add     %r10d,%r11d
     +0xa4c: mov     %r11d,-0x78(%rdx)
     +0xa50: movslq  -0x34(%rdx),%r9
     +0xa54: imul    %r8,%r9
     +0xa58: mov     %r9,%r10
     +0xa5b: imul    %rax,%r10
     +0xa5f: sar     $0x20,%r10
     +0xa63: imul    $0xffffffffff801fff,%r10,%r10
     +0xa6a: add     %r9,%r10
     +0xa6d: shr     $0x20,%r10
     +0xa71: mov     -0x74(%rdx),%r9d
     +0xa75: mov     %r9d,%r11d
     +0xa78: sub     %r10d,%r11d
     +0xa7b: mov     %r11d,-0x34(%rdx)
     +0xa7f: add     %r10d,%r9d
     +0xa82: mov     %r9d,-0x74(%rdx)
     +0xa86: movslq  -0x30(%rdx),%r9
     +0xa8a: imul    %r8,%r9
     +0xa8e: mov     %r9,%r10
     +0xa91: imul    %rax,%r10
     +0xa95: sar     $0x20,%r10
     +0xa99: imul    $0xffffffffff801fff,%r10,%r10
     +0xaa0: add     %r9,%r10
     +0xaa3: shr     $0x20,%r10
     +0xaa7: mov     -0x70(%rdx),%r9d
     +0xaab: mov     %r9d,%r11d
     +0xaae: sub     %r10d,%r11d
     +0xab1: mov     %r11d,-0x30(%rdx)
     +0xab5: add     %r10d,%r9d
     +0xab8: mov     %r9d,-0x70(%rdx)
     +0xabc: movslq  -0x2c(%rdx),%r9
     +0xac0: imul    %r8,%r9
     +0xac4: mov     %r9,%r10
     +0xac7: imul    %rax,%r10
     +0xacb: sar     $0x20,%r10
     +0xacf: imul    $0xffffffffff801fff,%r10,%r10
     +0xad6: add     %r9,%r10
     +0xad9: shr     $0x20,%r10
     +0xadd: mov     -0x6c(%rdx),%r9d
     +0xae1: mov     %r9d,%r11d
     +0xae4: sub     %r10d,%r11d
     +0xae7: mov     %r11d,-0x2c(%rdx)
     +0xaeb: add     %r10d,%r9d
     +0xaee: mov     %r9d,-0x6c(%rdx)
     +0xaf2: movslq  -0x28(%rdx),%r9
     +0xaf6: imul    %r8,%r9
     +0xafa: mov     %r9,%r10
     +0xafd: imul    %rax,%r10
     +0xb01: sar     $0x20,%r10
     +0xb05: imul    $0xffffffffff801fff,%r10,%r10
     +0xb0c: add     %r9,%r10
     +0xb0f: shr     $0x20,%r10
     +0xb13: mov     -0x68(%rdx),%r9d
     +0xb17: mov     %r9d,%r11d
     +0xb1a: sub     %r10d,%r11d
     +0xb1d: mov     %r11d,-0x28(%rdx)
     +0xb21: add     %r10d,%r9d
     +0xb24: mov     %r9d,-0x68(%rdx)
     +0xb28: movslq  -0x24(%rdx),%r9
     +0xb2c: imul    %r8,%r9
     +0xb30: mov     %r9,%r10
     +0xb33: imul    %rax,%r10
     +0xb37: sar     $0x20,%r10
     +0xb3b: imul    $0xffffffffff801fff,%r10,%r10
     +0xb42: add     %r9,%r10
     +0xb45: shr     $0x20,%r10
     +0xb49: mov     -0x64(%rdx),%r9d
     +0xb4d: mov     %r9d,%r11d
     +0xb50: sub     %r10d,%r11d
     +0xb53: mov     %r11d,-0x24(%rdx)
     +0xb57: add     %r10d,%r9d
     +0xb5a: mov     %r9d,-0x64(%rdx)
     +0xb5e: movslq  -0x20(%rdx),%r9
     +0xb62: imul    %r8,%r9
     +0xb66: mov     %r9,%r10
     +0xb69: imul    %rax,%r10
     +0xb6d: sar     $0x20,%r10
     +0xb71: imul    $0xffffffffff801fff,%r10,%r10
     +0xb78: add     %r9,%r10
     +0xb7b: shr     $0x20,%r10
     +0xb7f: mov     -0x60(%rdx),%r9d
     +0xb83: mov     %r9d,%r11d
     +0xb86: sub     %r10d,%r11d
     +0xb89: mov     %r11d,-0x20(%rdx)
     +0xb8d: add     %r10d,%r9d
     +0xb90: mov     %r9d,-0x60(%rdx)
     +0xb94: movslq  -0x1c(%rdx),%r9
     +0xb98: imul    %r8,%r9
     +0xb9c: mov     %r9,%r10
     +0xb9f: imul    %rax,%r10
     +0xba3: sar     $0x20,%r10
     +0xba7: imul    $0xffffffffff801fff,%r10,%r10
     +0xbae: add     %r9,%r10
     +0xbb1: shr     $0x20,%r10
     +0xbb5: mov     -0x5c(%rdx),%r9d
     +0xbb9: mov     %r9d,%r11d
     +0xbbc: sub     %r10d,%r11d
     +0xbbf: mov     %r11d,-0x1c(%rdx)
     +0xbc3: add     %r10d,%r9d
     +0xbc6: mov     %r9d,-0x5c(%rdx)
     +0xbca: movslq  -0x18(%rdx),%r9
     +0xbce: imul    %r8,%r9
     +0xbd2: mov     %r9,%r10
     +0xbd5: imul    %rax,%r10
     +0xbd9: sar     $0x20,%r10
     +0xbdd: imul    $0xffffffffff801fff,%r10,%r10
     +0xbe4: add     %r9,%r10
     +0xbe7: shr     $0x20,%r10
     +0xbeb: mov     -0x58(%rdx),%r9d
     +0xbef: mov     %r9d,%r11d
     +0xbf2: sub     %r10d,%r11d
     +0xbf5: mov     %r11d,-0x18(%rdx)
     +0xbf9: add     %r10d,%r9d
     +0xbfc: mov     %r9d,-0x58(%rdx)
     +0xc00: movslq  -0x14(%rdx),%r9
     +0xc04: imul    %r8,%r9
     +0xc08: mov     %r9,%r10
     +0xc0b: imul    %rax,%r10
     +0xc0f: sar     $0x20,%r10
     +0xc13: imul    $0xffffffffff801fff,%r10,%r10
     +0xc1a: add     %r9,%r10
     +0xc1d: shr     $0x20,%r10
     +0xc21: mov     -0x54(%rdx),%r9d
     +0xc25: mov     %r9d,%r11d
     +0xc28: sub     %r10d,%r11d
     +0xc2b: mov     %r11d,-0x14(%rdx)
     +0xc2f: add     %r10d,%r9d
     +0xc32: mov     %r9d,-0x54(%rdx)
     +0xc36: movslq  -0x10(%rdx),%r9
     +0xc3a: imul    %r8,%r9
     +0xc3e: mov     %r9,%r10
     +0xc41: imul    %rax,%r10
     +0xc45: sar     $0x20,%r10
     +0xc49: imul    $0xffffffffff801fff,%r10,%r10
     +0xc50: add     %r9,%r10
     +0xc53: shr     $0x20,%r10
     +0xc57: mov     -0x50(%rdx),%r9d
     +0xc5b: mov     %r9d,%r11d
     +0xc5e: sub     %r10d,%r11d
     +0xc61: mov     %r11d,-0x10(%rdx)
     +0xc65: add     %r10d,%r9d
     +0xc68: mov     %r9d,-0x50(%rdx)
     +0xc6c: movslq  -0xc(%rdx),%r9
     +0xc70: imul    %r8,%r9
     +0xc74: mov     %r9,%r10
     +0xc77: imul    %rax,%r10
     +0xc7b: sar     $0x20,%r10
     +0xc7f: imul    $0xffffffffff801fff,%r10,%r10
     +0xc86: add     %r9,%r10
     +0xc89: shr     $0x20,%r10
     +0xc8d: mov     -0x4c(%rdx),%r9d
     +0xc91: mov     %r9d,%r11d
     +0xc94: sub     %r10d,%r11d
     +0xc97: mov     %r11d,-0xc(%rdx)
     +0xc9b: add     %r10d,%r9d
     +0xc9e: mov     %r9d,-0x4c(%rdx)
     +0xca2: movslq  -0x8(%rdx),%r9
     +0xca6: imul    %r8,%r9
     +0xcaa: mov     %r9,%r10
     +0xcad: imul    %rax,%r10
     +0xcb1: sar     $0x20,%r10
     +0xcb5: imul    $0xffffffffff801fff,%r10,%r10
     +0xcbc: add     %r9,%r10
     +0xcbf: shr     $0x20,%r10
     +0xcc3: mov     -0x48(%rdx),%r9d
     +0xcc7: mov     %r9d,%r11d
     +0xcca: sub     %r10d,%r11d
     +0xccd: mov     %r11d,-0x8(%rdx)
     +0xcd1: add     %r10d,%r9d
     +0xcd4: mov     %r9d,-0x48(%rdx)
     +0xcd8: movslq  -0x4(%rdx),%r9
     +0xcdc: imul    %r8,%r9
     +0xce0: mov     %r9,%r10
     +0xce3: imul    %rax,%r10
     +0xce7: sar     $0x20,%r10
     +0xceb: imul    $0xffffffffff801fff,%r10,%r10
     +0xcf2: add     %r9,%r10
     +0xcf5: shr     $0x20,%r10
     +0xcf9: mov     -0x44(%rdx),%r9d
     +0xcfd: mov     %r9d,%r11d
     +0xd00: sub     %r10d,%r11d
     +0xd03: mov     %r11d,-0x4(%rdx)
     +0xd07: add     %r10d,%r9d
     +0xd0a: mov     %r9d,-0x44(%rdx)
     +0xd0e: movslq  (%rdx),%r9
     +0xd11: imul    %r8,%r9
     +0xd15: mov     %r9,%r8
     +0xd18: imul    %rax,%r8
     +0xd1c: sar     $0x20,%r8
     +0xd20: imul    $0xffffffffff801fff,%r8,%r8
     +0xd27: add     %r9,%r8
     +0xd2a: shr     $0x20,%r8
     +0xd2e: mov     -0x40(%rdx),%r9d
     +0xd32: mov     %r9d,%r10d
     +0xd35: sub     %r8d,%r10d
     +0xd38: mov     %r10d,(%rdx)
     +0xd3b: add     %r8d,%r9d
     +0xd3e: mov     %r9d,-0x40(%rdx)
     +0xd42: inc     %rsi
     +0xd45: sub     $0xffffffffffffff80,%rdx
     +0xd49: cmp     $0x8,%rsi
     +0xd4d: jne     <mldsa_poly_ntt+0x9e0>
     +0xd53: lea     0x3c(%rdi),%rdx
     +0xd57: xor     %esi,%esi
     +0xd59: nopl    0x0(%rax)
     +0xd60: movslq  0x40(%rcx,%rsi,4),%r8
     +0xd65: movslq  -0x1c(%rdx),%r9
     +0xd69: imul    %r8,%r9
     +0xd6d: mov     %r9,%r10
     +0xd70: imul    %rax,%r10
     +0xd74: sar     $0x20,%r10
     +0xd78: imul    $0xffffffffff801fff,%r10,%r10
     +0xd7f: add     %r9,%r10
     +0xd82: shr     $0x20,%r10
     +0xd86: mov     -0x3c(%rdx),%r9d
     +0xd8a: mov     -0x38(%rdx),%r11d
     +0xd8e: mov     %r9d,%ebx
     +0xd91: sub     %r10d,%ebx
     +0xd94: mov     %ebx,-0x1c(%rdx)
     +0xd97: add     %r10d,%r9d
     +0xd9a: mov     %r9d,-0x3c(%rdx)
     +0xd9e: movslq  -0x18(%rdx),%r9
     +0xda2: imul    %r8,%r9
     +0xda6: mov     %r9,%r10
     +0xda9: imul    %rax,%r10
     +0xdad: sar     $0x20,%r10
     +0xdb1: imul    $0xffffffffff801fff,%r10,%r10
     +0xdb8: add     %r9,%r10
     +0xdbb: shr     $0x20,%r10
     +0xdbf: mov     %r11d,%r9d
     +0xdc2: sub     %r10d,%r9d
     +0xdc5: mov     %r9d,-0x18(%rdx)
     +0xdc9: add     %r10d,%r11d
     +0xdcc: mov     %r11d,-0x38(%rdx)
     +0xdd0: movslq  -0x14(%rdx),%r9
     +0xdd4: imul    %r8,%r9
     +0xdd8: mov     %r9,%r10
     +0xddb: imul    %rax,%r10
     +0xddf: sar     $0x20,%r10
     +0xde3: imul    $0xffffffffff801fff,%r10,%r10
     +0xdea: add     %r9,%r10
     +0xded: shr     $0x20,%r10
     +0xdf1: mov     -0x34(%rdx),%r9d
     +0xdf5: mov     %r9d,%r11d
     +0xdf8: sub     %r10d,%r11d
     +0xdfb: mov     %r11d,-0x14(%rdx)
     +0xdff: add     %r10d,%r9d
     +0xe02: mov     %r9d,-0x34(%rdx)
     +0xe06: movslq  -0x10(%rdx),%r9
     +0xe0a: imul    %r8,%r9
     +0xe0e: mov     %r9,%r10
     +0xe11: imul    %rax,%r10
     +0xe15: sar     $0x20,%r10
     +0xe19: imul    $0xffffffffff801fff,%r10,%r10
     +0xe20: add     %r9,%r10
     +0xe23: shr     $0x20,%r10
     +0xe27: mov     -0x30(%rdx),%r9d
     +0xe2b: mov     %r9d,%r11d
     +0xe2e: sub     %r10d,%r11d
     +0xe31: mov     %r11d,-0x10(%rdx)
     +0xe35: add     %r10d,%r9d
     +0xe38: mov     %r9d,-0x30(%rdx)
     +0xe3c: movslq  -0xc(%rdx),%r9
     +0xe40: imul    %r8,%r9
     +0xe44: mov     %r9,%r10
     +0xe47: imul    %rax,%r10
     +0xe4b: sar     $0x20,%r10
     +0xe4f: imul    $0xffffffffff801fff,%r10,%r10
     +0xe56: add     %r9,%r10
     +0xe59: shr     $0x20,%r10
     +0xe5d: mov     -0x2c(%rdx),%r9d
     +0xe61: mov     %r9d,%r11d
     +0xe64: sub     %r10d,%r11d
     +0xe67: mov     %r11d,-0xc(%rdx)
     +0xe6b: add     %r10d,%r9d
     +0xe6e: mov     %r9d,-0x2c(%rdx)
     +0xe72: movslq  -0x8(%rdx),%r9
     +0xe76: imul    %r8,%r9
     +0xe7a: mov     %r9,%r10
     +0xe7d: imul    %rax,%r10
     +0xe81: sar     $0x20,%r10
     +0xe85: imul    $0xffffffffff801fff,%r10,%r10
     +0xe8c: add     %r9,%r10
     +0xe8f: shr     $0x20,%r10
     +0xe93: mov     -0x28(%rdx),%r9d
     +0xe97: mov     %r9d,%r11d
     +0xe9a: sub     %r10d,%r11d
     +0xe9d: mov     %r11d,-0x8(%rdx)
     +0xea1: add     %r10d,%r9d
     +0xea4: mov     %r9d,-0x28(%rdx)
     +0xea8: movslq  -0x4(%rdx),%r9
     +0xeac: imul    %r8,%r9
     +0xeb0: mov     %r9,%r10
     +0xeb3: imul    %rax,%r10
     +0xeb7: sar     $0x20,%r10
     +0xebb: imul    $0xffffffffff801fff,%r10,%r10
     +0xec2: add     %r9,%r10
     +0xec5: shr     $0x20,%r10
     +0xec9: mov     -0x24(%rdx),%r9d
     +0xecd: mov     %r9d,%r11d
     +0xed0: sub     %r10d,%r11d
     +0xed3: mov     %r11d,-0x4(%rdx)
     +0xed7: add     %r10d,%r9d
     +0xeda: mov     %r9d,-0x24(%rdx)
     +0xede: movslq  (%rdx),%r9
     +0xee1: imul    %r8,%r9
     +0xee5: mov     %r9,%r8
     +0xee8: imul    %rax,%r8
     +0xeec: sar     $0x20,%r8
     +0xef0: imul    $0xffffffffff801fff,%r8,%r8
     +0xef7: add     %r9,%r8
     +0xefa: shr     $0x20,%r8
     +0xefe: mov     -0x20(%rdx),%r9d
     +0xf02: mov     %r9d,%r10d
     +0xf05: sub     %r8d,%r10d
     +0xf08: mov     %r10d,(%rdx)
     +0xf0b: add     %r8d,%r9d
     +0xf0e: mov     %r9d,-0x20(%rdx)
     +0xf12: inc     %rsi
     +0xf15: add     $0x40,%rdx
     +0xf19: cmp     $0x10,%rsi
     +0xf1d: jne     <mldsa_poly_ntt+0xd60>
     +0xf23: xor     %edx,%edx
     +0xf25: pop     %rbx
     +0xf26: cs      nopw 0x0(%rax,%rax,1)
     +0xf30: movslq  0x80(%rdx,%rcx,1),%r11
     +0xf38: movslq  0x1c(%rdi,%rdx,8),%r10
     +0xf3d: movslq  0x18(%rdi,%rdx,8),%r9
     +0xf42: movslq  0x14(%rdi,%rdx,8),%r8
     +0xf47: movslq  0x10(%rdi,%rdx,8),%rsi
     +0xf4c: imul    %r11,%r10
     +0xf50: imul    %r11,%r9
     +0xf54: imul    %r11,%r8
     +0xf58: imul    %r11,%rsi
     +0xf5c: movq    %r10,%xmm0
     +0xf61: imul    %rax,%r10
     +0xf65: movq    %r9,%xmm1
     +0xf6a: imul    %rax,%r9
     +0xf6e: movq    %r8,%xmm2
     +0xf73: imul    %rax,%r8
     +0xf77: movq    %rsi,%xmm3
     +0xf7c: imul    %rax,%rsi
     +0xf80: sar     $0x20,%r10
     +0xf84: sar     $0x20,%r9
     +0xf88: sar     $0x20,%r8
     +0xf8c: sar     $0x20,%rsi
     +0xf90: imul    $0xffffffffff801fff,%r10,%r10
     +0xf97: imul    $0xffffffffff801fff,%r9,%r9
     +0xf9e: imul    $0xffffffffff801fff,%r8,%r8
     +0xfa5: imul    $0xffffffffff801fff,%rsi,%rsi
     +0xfac: movq    %r8,%xmm4
     +0xfb1: movq    %rsi,%xmm5
     +0xfb6: punpcklqdq %xmm4,%xmm5
     +0xfba: movq    %r10,%xmm4
     +0xfbf: movq    %r9,%xmm6
     +0xfc4: punpcklqdq %xmm4,%xmm6
     +0xfc8: punpcklqdq %xmm2,%xmm3
     +0xfcc: paddq   %xmm5,%xmm3
     +0xfd0: punpcklqdq %xmm0,%xmm1
     +0xfd4: paddq   %xmm6,%xmm1
     +0xfd8: shufps  $0xdd,%xmm1,%xmm3
     +0xfdc: movdqu  (%rdi,%rdx,8),%xmm0
     +0xfe1: movdqa  %xmm0,%xmm1
     +0xfe5: paddd   %xmm3,%xmm1
     +0xfe9: psubd   %xmm3,%xmm0
     +0xfed: movdqu  %xmm1,(%rdi,%rdx,8)
     +0xff2: movdqu  %xmm0,0x10(%rdi,%rdx,8)
     +0xff8: add     $0x4,%rdx
     +0xffc: cmp     $0x80,%rdx
    +0x1003: jne     <mldsa_poly_ntt+0xf30>
    +0x1009: xor     %edx,%edx
    +0x100b: nopl    0x0(%rax,%rax,1)
    +0x1010: movslq  0x100(%rdx,%rcx,1),%rsi
    +0x1018: movslq  0xc(%rdi,%rdx,4),%r8
    +0x101d: movslq  0x8(%rdi,%rdx,4),%r9
    +0x1022: imul    %rsi,%r8
    +0x1026: imul    %rsi,%r9
    +0x102a: movq    %r8,%xmm0
    +0x102f: imul    %rax,%r8
    +0x1033: movq    %r9,%xmm1
    +0x1038: imul    %rax,%r9
    +0x103c: sar     $0x20,%r8
    +0x1040: sar     $0x20,%r9
    +0x1044: imul    $0xffffffffff801fff,%r8,%rsi
    +0x104b: imul    $0xffffffffff801fff,%r9,%r8
    +0x1052: movq    %rsi,%xmm2
    +0x1057: movq    %r8,%xmm3
    +0x105c: punpcklqdq %xmm2,%xmm3
    +0x1060: punpcklqdq %xmm0,%xmm1
    +0x1064: paddq   %xmm3,%xmm1
    +0x1068: pshufd  $0xdd,%xmm1,%xmm0
    +0x106d: movq    (%rdi,%rdx,4),%xmm1
    +0x1072: pshufd  $0x44,%xmm1,%xmm2
    +0x1077: paddd   %xmm0,%xmm1
    +0x107b: psubd   %xmm0,%xmm2
    +0x107f: movsd   %xmm1,%xmm2
    +0x1083: movupd  %xmm2,(%rdi,%rdx,4)
    +0x1088: add     $0x4,%rdx
    +0x108c: cmp     $0x100,%rdx
    +0x1093: jne     <mldsa_poly_ntt+0x1010>
    +0x1099: xor     %edx,%edx
    +0x109b: nopl    0x0(%rax,%rax,1)
    +0x10a0: movslq  0x200(%rcx,%rdx,4),%rsi
    +0x10a8: movslq  0x4(%rdi,%rdx,8),%r8
    +0x10ad: imul    %rsi,%r8
    +0x10b1: mov     %r8,%rsi
    +0x10b4: imul    %rax,%rsi
    +0x10b8: sar     $0x20,%rsi
    +0x10bc: imul    $0xffffffffff801fff,%rsi,%rsi
    +0x10c3: add     %r8,%rsi
    +0x10c6: shr     $0x20,%rsi
    +0x10ca: mov     (%rdi,%rdx,8),%r8d
    +0x10ce: mov     %r8d,%r9d
    +0x10d1: sub     %esi,%r9d
    +0x10d4: mov     %r9d,0x4(%rdi,%rdx,8)
    +0x10d9: add     %esi,%r8d
    +0x10dc: mov     %r8d,(%rdi,%rdx,8)
    +0x10e0: inc     %rdx
    +0x10e3: cmp     $0x80,%rdx
    +0x10ea: jne     <mldsa_poly_ntt+0x10a0>
    +0x10ec: xor     %eax,%eax
    +0x10ee: xor     %ecx,%ecx
    +0x10f0: xor     %edi,%edi
    +0x10f2: xor     %edx,%edx
    +0x10f4: xor     %esi,%esi
    +0x10f6: xor     %r8d,%r8d
    +0x10f9: xor     %r9d,%r9d
    +0x10fc: xor     %r10d,%r10d
    +0x10ff: xor     %r11d,%r11d
    +0x1102: ret     
 ***)

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa_poly_ntt"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomial x at a, 256 coefficients of 32 bits each,     *)
(* becomes mld_poly_ntt x. The function saves RBX, RBP and R12-R15 below the *)
(* return address and keeps a temporary in the 8 bytes below them (the red   *)
(* zone), the stack frame of 56 bytes.                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 8),8)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa_poly_ntt) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i))))
                            s = mld_poly_ntt x i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* polynomial, the table of zetas in the image, the stack frame and the slot *)
(* of the return address, and the writes within the polynomial and the stack *)
(* frame.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 8),8)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa_poly_ntt) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = mld_poly_ntt x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc (word_sub stackpointer (word 8))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_ntt_consts),256;
                       word_sub stackpointer (word 8),8; stackpointer,8]
                      [a,1024; word_sub stackpointer (word 8),8]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 8),8)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa_poly_ntt) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc (word_sub stackpointer (word 8))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_ntt_consts),256;
                       word_sub stackpointer (word 8),8; stackpointer,8]
                      [a,1024; word_sub stackpointer (word 8),8]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
