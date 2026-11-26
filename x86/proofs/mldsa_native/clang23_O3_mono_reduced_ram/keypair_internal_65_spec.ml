(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the statement. This is the code for                       *)
(* mldsa65_keypair_internal (mld_sign_keypair_internal in sign.c) from       *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3    *)
(* and MLD_CONFIG_REDUCE_RAM (the monolithic build, see                      *)
(* mldsa_native/README.md). Clang inlines most of it: the SHAKE256 of the    *)
(* seed that gives rho, rho' and the key (one permutation with               *)
(* mldsa_keccakf1600_permute), the packing of each polynomial of s2 and s1   *)
(* into the secret key (mld_polyeta_pack, vectorised with SSE2), the copies  *)
(* of rho, the key and tr into the keys, and the SHAKE256 of the public key  *)
(* into tr (15 permutations). It calls mldsa65_poly_uniform_eta_4x three     *)
(* times, for the last four polynomials of s2, then the last of s1, the      *)
(* first two of s2 and one with the irrelevant nonce 255, and then the first *)
(* four of s1, mldsa_poly_ntt for each polynomial of s1 and                  *)
(* mld_compute_pack_t0_t165, which computes t and packs t1 into the public   *)
(* key and t0 into the secret key, and clears its buffers with SSE stores    *)
(* and memset. It aligns its frame to 32 bytes (see                          *)
(* utils/mldsa_native_realign.ml). It is verified in the whole image (see    *)
(* libmldsa.ml) against mld_keypair_pk_65 and mld_keypair_sk_65 of           *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and for   *)
(* the inlined regions (keypair_internal_65_lemmas.ml), assuming that the    *)
(* sampling of the matrix and of each polynomial terminates, and shown to be *)
(* constant time and memory safe, with the events depending only on the      *)
(* addresses and the values that the C code declassifies (rho and            *)
(* mld_keypair_declass_65).                                                  *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa65_keypair_internal:
       +0x0: push    %rbp
       +0x1: mov     %rsp,%rbp
       +0x4: push    %r15
       +0x6: push    %r14
       +0x8: push    %r13
       +0xa: push    %r12
       +0xc: push    %rbx
       +0xd: and     $0xffffffffffffffe0,%rsp
      +0x11: sub     $0xfe0,%rsp
      +0x18: movq    $0x0,(%rsp)
      +0x20: sub     $0x620,%rsp
      +0x27: mov     %rsi,%rbx
      +0x2a: movups  (%rdx),%xmm0
      +0x2d: movups  0x10(%rdx),%xmm1
      +0x31: movaps  %xmm1,0xf0(%rsp)
      +0x39: movaps  %xmm0,0xe0(%rsp)
      +0x41: movw    $0x506,0x100(%rsp)
      +0x4b: xorps   %xmm0,%xmm0
      +0x4e: movups  %xmm0,0x298(%rsp)
      +0x56: movups  %xmm0,0x288(%rsp)
      +0x5e: movups  %xmm0,0x278(%rsp)
      +0x66: movups  %xmm0,0x268(%rsp)
      +0x6e: movups  %xmm0,0x258(%rsp)
      +0x76: movups  %xmm0,0x248(%rsp)
      +0x7e: movups  %xmm0,0x238(%rsp)
      +0x86: movups  %xmm0,0x228(%rsp)
      +0x8e: movups  %xmm0,0x218(%rsp)
      +0x96: movups  %xmm0,0x208(%rsp)
      +0x9e: movups  %xmm0,0x1f8(%rsp)
      +0xa6: movl    $0x0,0x2a8(%rsp)
      +0xb1: movaps  0xe0(%rsp),%xmm0
      +0xb9: movaps  %xmm0,0x1e0(%rsp)
      +0xc1: movzbl  0xf0(%rsp),%eax
      +0xc9: mov     %al,0x1f0(%rsp)
      +0xd0: mov     0x1f9(%rsp),%rax
      +0xd8: xor     0xf9(%rsp),%rax
      +0xe0: movq    %rax,%xmm0
      +0xe5: movq    0xf1(%rsp),%xmm1
      +0xee: punpcklqdq %xmm0,%xmm1
      +0xf2: movdqu  %xmm1,0x1f1(%rsp)
      +0xfb: movzbl  0x101(%rsp),%eax
     +0x103: xor     %al,0x201(%rsp)
     +0x10a: mov     %rdi,%r14
     +0x10d: xorb    $0x1f,0x202(%rsp)
     +0x115: xorb    $0x80,0x267(%rsp)
     +0x11d: movl    $0x88,0x2a8(%rsp)
     +0x128: lea     0x1e0(%rsp),%r12
     +0x130: mov     %r12,%rdi
     +0x133: call    <mldsa_keccakf1600_permute>
     +0x138: movaps  0x250(%rsp),%xmm0
     +0x140: movaps  %xmm0,0x1d0(%rsp)
     +0x148: movaps  0x240(%rsp),%xmm0
     +0x150: movaps  %xmm0,0x1c0(%rsp)
     +0x158: movaps  0x230(%rsp),%xmm0
     +0x160: movaps  %xmm0,0x1b0(%rsp)
     +0x168: movaps  0x220(%rsp),%xmm0
     +0x170: movaps  %xmm0,0x1a0(%rsp)
     +0x178: movdqa  0x1e0(%rsp),%xmm0
     +0x181: movdqa  0x1f0(%rsp),%xmm1
     +0x18a: movdqa  0x200(%rsp),%xmm2
     +0x193: movdqa  0x210(%rsp),%xmm3
     +0x19c: movdqa  %xmm3,0x190(%rsp)
     +0x1a5: movdqa  %xmm2,0x180(%rsp)
     +0x1ae: movdqa  %xmm1,0x170(%rsp)
     +0x1b7: movdqa  %xmm0,0x160(%rsp)
     +0x1c0: lea     0x180(%rsp),%r15
     +0x1c8: pxor    %xmm0,%xmm0
     +0x1cc: movdqa  %xmm0,0x260(%rsp)
     +0x1d5: movdqa  %xmm0,0x270(%rsp)
     +0x1de: movdqa  %xmm0,0x280(%rsp)
     +0x1e7: movdqa  %xmm0,0x290(%rsp)
     +0x1f0: movdqa  %xmm0,0x2a0(%rsp)
     +0x1f9: movdqa  %xmm0,0x1e0(%rsp)
     +0x202: movdqa  %xmm0,0x1f0(%rsp)
     +0x20b: movdqa  %xmm0,0x200(%rsp)
     +0x214: movdqa  %xmm0,0x210(%rsp)
     +0x21d: movdqa  %xmm0,0x220(%rsp)
     +0x226: movdqa  %xmm0,0x230(%rsp)
     +0x22f: movdqa  %xmm0,0x240(%rsp)
     +0x238: movdqa  %xmm0,0x250(%rsp)
     +0x241: lea     0x5e0(%rsp),%r13
     +0x249: lea     0x9e0(%rsp),%r12
     +0x251: lea     0xde0(%rsp),%rcx
     +0x259: sub     $0x8,%rsp
     +0x25d: lea     0x1e8(%rsp),%rdi
     +0x265: mov     %r13,%rsi
     +0x268: mov     %r12,%rdx
     +0x26b: mov     %r15,%r8
     +0x26e: mov     $0x7,%r9d
     +0x274: push    $0xa
     +0x276: push    $0x9
     +0x278: push    $0x8
     +0x27a: call    <mldsa65_poly_uniform_eta_4x>
     +0x27f: add     $0x20,%rsp
     +0x283: xor     %eax,%eax
     +0x285: movdqa  0x193e2(%rip),%xmm8
     +0x28e: movdqa  0x193e9(%rip),%xmm9
     +0x297: movdqa  0x193f0(%rip),%xmm10
     +0x2a0: movdqa  0x193f7(%rip),%xmm11
     +0x2a9: movdqa  0x193fe(%rip),%xmm12
     +0x2b2: movdqa  0x19405(%rip),%xmm13
     +0x2bb: nopl    0x0(%rax,%rax,1)
     +0x2c0: movdqa  0x1e0(%rsp,%rax,8),%xmm4
     +0x2c9: movdqa  0x1f0(%rsp,%rax,8),%xmm5
     +0x2d2: movdqa  0x200(%rsp,%rax,8),%xmm7
     +0x2db: movdqa  0x210(%rsp,%rax,8),%xmm1
     +0x2e4: pshufd  $0xe7,%xmm5,%xmm2
     +0x2e9: pand    %xmm8,%xmm5
     +0x2ee: pshufd  $0xe7,%xmm4,%xmm3
     +0x2f3: pand    %xmm8,%xmm4
     +0x2f8: packuswb %xmm5,%xmm4
     +0x2fc: packuswb %xmm4,%xmm4
     +0x300: packuswb %xmm4,%xmm4
     +0x304: pshufd  $0xe7,%xmm1,%xmm5
     +0x309: pand    %xmm8,%xmm1
     +0x30e: pshufd  $0xe7,%xmm7,%xmm6
     +0x313: pand    %xmm8,%xmm7
     +0x318: packuswb %xmm1,%xmm7
     +0x31c: packuswb %xmm7,%xmm7
     +0x320: packuswb %xmm7,%xmm7
     +0x324: movdqa  %xmm9,%xmm1
     +0x329: psubb   %xmm4,%xmm1
     +0x32d: movdqa  %xmm9,%xmm0
     +0x332: psubb   %xmm7,%xmm0
     +0x336: pand    %xmm10,%xmm2
     +0x33b: pshuflw $0x24,%xmm2,%xmm2
     +0x340: packuswb %xmm2,%xmm2
     +0x344: movdqa  %xmm11,%xmm4
     +0x349: pandn   %xmm2,%xmm4
     +0x34d: pand    %xmm10,%xmm3
     +0x352: pshuflw $0xe2,%xmm3,%xmm2
     +0x357: packuswb %xmm2,%xmm2
     +0x35b: pand    %xmm11,%xmm2
     +0x360: por     %xmm4,%xmm2
     +0x364: pand    %xmm10,%xmm5
     +0x369: pshuflw $0x24,%xmm5,%xmm3
     +0x36e: packuswb %xmm3,%xmm3
     +0x372: movdqa  %xmm11,%xmm4
     +0x377: pandn   %xmm3,%xmm4
     +0x37b: pand    %xmm10,%xmm6
     +0x380: pshuflw $0xe2,%xmm6,%xmm3
     +0x385: packuswb %xmm3,%xmm3
     +0x389: pand    %xmm11,%xmm3
     +0x38e: por     %xmm4,%xmm3
     +0x392: psllw   $0x4,%xmm2
     +0x397: pand    %xmm12,%xmm2
     +0x39c: psllw   $0x4,%xmm3
     +0x3a1: pand    %xmm12,%xmm3
     +0x3a6: movdqa  %xmm13,%xmm4
     +0x3ab: psubb   %xmm2,%xmm4
     +0x3af: por     %xmm1,%xmm4
     +0x3b3: movdqa  %xmm13,%xmm1
     +0x3b8: psubb   %xmm3,%xmm1
     +0x3bc: por     %xmm0,%xmm1
     +0x3c0: movd    %xmm4,0x400(%rbx,%rax,1)
     +0x3c9: movd    %xmm1,0x404(%rbx,%rax,1)
     +0x3d2: add     $0x8,%rax
     +0x3d6: cmp     $0x80,%rax
     +0x3dc: jne     <mldsa65_keypair_internal+0x2c0>
     +0x3e2: movq    $0x0,0x10(%rsp)
     +0x3eb: lea     0x10(%rsp),%rax
     +0x3f0: mov     $0x480,%eax
     +0x3f5: data16  cs nopw 0x0(%rax,%rax,1)
     +0x400: movdqa  -0x1e20(%rsp,%rax,8),%xmm4
     +0x409: movdqa  -0x1e10(%rsp,%rax,8),%xmm5
     +0x412: movdqa  -0x1e00(%rsp,%rax,8),%xmm7
     +0x41b: movdqa  -0x1df0(%rsp,%rax,8),%xmm1
     +0x424: pshufd  $0xe7,%xmm5,%xmm2
     +0x429: pand    %xmm8,%xmm5
     +0x42e: pshufd  $0xe7,%xmm4,%xmm3
     +0x433: pand    %xmm8,%xmm4
     +0x438: packuswb %xmm5,%xmm4
     +0x43c: packuswb %xmm4,%xmm4
     +0x440: packuswb %xmm4,%xmm4
     +0x444: pshufd  $0xe7,%xmm1,%xmm5
     +0x449: pand    %xmm8,%xmm1
     +0x44e: pshufd  $0xe7,%xmm7,%xmm6
     +0x453: pand    %xmm8,%xmm7
     +0x458: packuswb %xmm1,%xmm7
     +0x45c: packuswb %xmm7,%xmm7
     +0x460: packuswb %xmm7,%xmm7
     +0x464: movdqa  %xmm9,%xmm1
     +0x469: psubb   %xmm4,%xmm1
     +0x46d: movdqa  %xmm9,%xmm0
     +0x472: psubb   %xmm7,%xmm0
     +0x476: pand    %xmm10,%xmm2
     +0x47b: pshuflw $0x24,%xmm2,%xmm2
     +0x480: packuswb %xmm2,%xmm2
     +0x484: movdqa  %xmm11,%xmm4
     +0x489: pandn   %xmm2,%xmm4
     +0x48d: pand    %xmm10,%xmm3
     +0x492: pshuflw $0xe2,%xmm3,%xmm2
     +0x497: packuswb %xmm2,%xmm2
     +0x49b: pand    %xmm11,%xmm2
     +0x4a0: por     %xmm4,%xmm2
     +0x4a4: pand    %xmm10,%xmm5
     +0x4a9: pshuflw $0x24,%xmm5,%xmm3
     +0x4ae: packuswb %xmm3,%xmm3
     +0x4b2: movdqa  %xmm11,%xmm4
     +0x4b7: pandn   %xmm3,%xmm4
     +0x4bb: pand    %xmm10,%xmm6
     +0x4c0: pshuflw $0xe2,%xmm6,%xmm3
     +0x4c5: packuswb %xmm3,%xmm3
     +0x4c9: pand    %xmm11,%xmm3
     +0x4ce: por     %xmm4,%xmm3
     +0x4d2: psllw   $0x4,%xmm2
     +0x4d7: pand    %xmm12,%xmm2
     +0x4dc: psllw   $0x4,%xmm3
     +0x4e1: pand    %xmm12,%xmm3
     +0x4e6: movdqa  %xmm13,%xmm4
     +0x4eb: psubb   %xmm2,%xmm4
     +0x4ef: por     %xmm1,%xmm4
     +0x4f3: movdqa  %xmm13,%xmm1
     +0x4f8: psubb   %xmm3,%xmm1
     +0x4fc: por     %xmm0,%xmm1
     +0x500: movd    %xmm4,(%rbx,%rax,1)
     +0x505: movd    %xmm1,0x4(%rbx,%rax,1)
     +0x50b: add     $0x8,%rax
     +0x50f: cmp     $0x500,%rax
     +0x515: jne     <mldsa65_keypair_internal+0x400>
     +0x51b: movq    $0x0,0x10(%rsp)
     +0x524: lea     0x10(%rsp),%rax
     +0x529: mov     $0x500,%eax
     +0x52e: xchg    %ax,%ax
     +0x530: movdqa  -0x1e20(%rsp,%rax,8),%xmm4
     +0x539: movdqa  -0x1e10(%rsp,%rax,8),%xmm5
     +0x542: movdqa  -0x1e00(%rsp,%rax,8),%xmm7
     +0x54b: movdqa  -0x1df0(%rsp,%rax,8),%xmm1
     +0x554: pshufd  $0xe7,%xmm5,%xmm2
     +0x559: pand    %xmm8,%xmm5
     +0x55e: pshufd  $0xe7,%xmm4,%xmm3
     +0x563: pand    %xmm8,%xmm4
     +0x568: packuswb %xmm5,%xmm4
     +0x56c: packuswb %xmm4,%xmm4
     +0x570: packuswb %xmm4,%xmm4
     +0x574: pshufd  $0xe7,%xmm1,%xmm5
     +0x579: pand    %xmm8,%xmm1
     +0x57e: pshufd  $0xe7,%xmm7,%xmm6
     +0x583: pand    %xmm8,%xmm7
     +0x588: packuswb %xmm1,%xmm7
     +0x58c: packuswb %xmm7,%xmm7
     +0x590: packuswb %xmm7,%xmm7
     +0x594: movdqa  %xmm9,%xmm1
     +0x599: psubb   %xmm4,%xmm1
     +0x59d: movdqa  %xmm9,%xmm0
     +0x5a2: psubb   %xmm7,%xmm0
     +0x5a6: pand    %xmm10,%xmm2
     +0x5ab: pshuflw $0x24,%xmm2,%xmm2
     +0x5b0: packuswb %xmm2,%xmm2
     +0x5b4: movdqa  %xmm11,%xmm4
     +0x5b9: pandn   %xmm2,%xmm4
     +0x5bd: pand    %xmm10,%xmm3
     +0x5c2: pshuflw $0xe2,%xmm3,%xmm2
     +0x5c7: packuswb %xmm2,%xmm2
     +0x5cb: pand    %xmm11,%xmm2
     +0x5d0: por     %xmm4,%xmm2
     +0x5d4: pand    %xmm10,%xmm5
     +0x5d9: pshuflw $0x24,%xmm5,%xmm3
     +0x5de: packuswb %xmm3,%xmm3
     +0x5e2: movdqa  %xmm11,%xmm4
     +0x5e7: pandn   %xmm3,%xmm4
     +0x5eb: pand    %xmm10,%xmm6
     +0x5f0: pshuflw $0xe2,%xmm6,%xmm3
     +0x5f5: packuswb %xmm3,%xmm3
     +0x5f9: pand    %xmm11,%xmm3
     +0x5fe: por     %xmm4,%xmm3
     +0x602: psllw   $0x4,%xmm2
     +0x607: pand    %xmm12,%xmm2
     +0x60c: psllw   $0x4,%xmm3
     +0x611: pand    %xmm12,%xmm3
     +0x616: movdqa  %xmm13,%xmm4
     +0x61b: psubb   %xmm2,%xmm4
     +0x61f: por     %xmm1,%xmm4
     +0x623: movdqa  %xmm13,%xmm1
     +0x628: psubb   %xmm3,%xmm1
     +0x62c: por     %xmm0,%xmm1
     +0x630: movd    %xmm4,(%rbx,%rax,1)
     +0x635: movd    %xmm1,0x4(%rbx,%rax,1)
     +0x63b: add     $0x8,%rax
     +0x63f: cmp     $0x580,%rax
     +0x645: jne     <mldsa65_keypair_internal+0x530>
     +0x64b: movq    $0x0,0x10(%rsp)
     +0x654: lea     0x10(%rsp),%rax
     +0x659: mov     $0x580,%eax
     +0x65e: xchg    %ax,%ax
     +0x660: movdqa  -0x1e20(%rsp,%rax,8),%xmm4
     +0x669: movdqa  -0x1e10(%rsp,%rax,8),%xmm5
     +0x672: movdqa  -0x1e00(%rsp,%rax,8),%xmm7
     +0x67b: movdqa  -0x1df0(%rsp,%rax,8),%xmm1
     +0x684: pshufd  $0xe7,%xmm5,%xmm2
     +0x689: pand    %xmm8,%xmm5
     +0x68e: pshufd  $0xe7,%xmm4,%xmm3
     +0x693: pand    %xmm8,%xmm4
     +0x698: packuswb %xmm5,%xmm4
     +0x69c: packuswb %xmm4,%xmm4
     +0x6a0: packuswb %xmm4,%xmm4
     +0x6a4: pshufd  $0xe7,%xmm1,%xmm5
     +0x6a9: pand    %xmm8,%xmm1
     +0x6ae: pshufd  $0xe7,%xmm7,%xmm6
     +0x6b3: pand    %xmm8,%xmm7
     +0x6b8: packuswb %xmm1,%xmm7
     +0x6bc: packuswb %xmm7,%xmm7
     +0x6c0: packuswb %xmm7,%xmm7
     +0x6c4: movdqa  %xmm9,%xmm1
     +0x6c9: psubb   %xmm4,%xmm1
     +0x6cd: movdqa  %xmm9,%xmm0
     +0x6d2: psubb   %xmm7,%xmm0
     +0x6d6: pand    %xmm10,%xmm2
     +0x6db: pshuflw $0x24,%xmm2,%xmm2
     +0x6e0: packuswb %xmm2,%xmm2
     +0x6e4: movdqa  %xmm11,%xmm4
     +0x6e9: pandn   %xmm2,%xmm4
     +0x6ed: pand    %xmm10,%xmm3
     +0x6f2: pshuflw $0xe2,%xmm3,%xmm2
     +0x6f7: packuswb %xmm2,%xmm2
     +0x6fb: pand    %xmm11,%xmm2
     +0x700: por     %xmm4,%xmm2
     +0x704: pand    %xmm10,%xmm5
     +0x709: pshuflw $0x24,%xmm5,%xmm3
     +0x70e: packuswb %xmm3,%xmm3
     +0x712: movdqa  %xmm11,%xmm4
     +0x717: pandn   %xmm3,%xmm4
     +0x71b: pand    %xmm10,%xmm6
     +0x720: pshuflw $0xe2,%xmm6,%xmm3
     +0x725: packuswb %xmm3,%xmm3
     +0x729: pand    %xmm11,%xmm3
     +0x72e: por     %xmm4,%xmm3
     +0x732: psllw   $0x4,%xmm2
     +0x737: pand    %xmm12,%xmm2
     +0x73c: psllw   $0x4,%xmm3
     +0x741: pand    %xmm12,%xmm3
     +0x746: movdqa  %xmm13,%xmm4
     +0x74b: psubb   %xmm2,%xmm4
     +0x74f: por     %xmm1,%xmm4
     +0x753: movdqa  %xmm13,%xmm1
     +0x758: psubb   %xmm3,%xmm1
     +0x75c: por     %xmm0,%xmm1
     +0x760: movd    %xmm4,(%rbx,%rax,1)
     +0x765: movd    %xmm1,0x4(%rbx,%rax,1)
     +0x76b: add     $0x8,%rax
     +0x76f: cmp     $0x600,%rax
     +0x775: jne     <mldsa65_keypair_internal+0x660>
     +0x77b: movq    $0x0,0x10(%rsp)
     +0x784: lea     0x10(%rsp),%rax
     +0x789: lea     0x11e0(%rsp),%rdi
     +0x791: sub     $0x8,%rsp
     +0x795: lea     0x1e8(%rsp),%rsi
     +0x79d: mov     %r13,%rdx
     +0x7a0: mov     %r12,%rcx
     +0x7a3: mov     %r15,%r8
     +0x7a6: mov     $0x4,%r9d
     +0x7ac: push    $0xff
     +0x7b1: push    $0x6
     +0x7b3: push    $0x5
     +0x7b5: call    <mldsa65_poly_uniform_eta_4x>
     +0x7ba: movdqa  0x18efd(%rip),%xmm13
     +0x7c3: movdqa  0x18ee4(%rip),%xmm12
     +0x7cc: movdqa  0x18ecb(%rip),%xmm11
     +0x7d5: movdqa  0x18eb2(%rip),%xmm10
     +0x7de: movdqa  0x18e99(%rip),%xmm9
     +0x7e7: movdqa  0x18e80(%rip),%xmm8
     +0x7f0: add     $0x20,%rsp
     +0x7f4: mov     $0x200,%eax
     +0x7f9: nopl    0x0(%rax)
     +0x800: movdqa  0x1e0(%rsp,%rax,8),%xmm4
     +0x809: movdqa  0x1f0(%rsp,%rax,8),%xmm5
     +0x812: movdqa  0x200(%rsp,%rax,8),%xmm7
     +0x81b: movdqa  0x210(%rsp,%rax,8),%xmm1
     +0x824: pshufd  $0xe7,%xmm5,%xmm2
     +0x829: pand    %xmm8,%xmm5
     +0x82e: pshufd  $0xe7,%xmm4,%xmm3
     +0x833: pand    %xmm8,%xmm4
     +0x838: packuswb %xmm5,%xmm4
     +0x83c: packuswb %xmm4,%xmm4
     +0x840: packuswb %xmm4,%xmm4
     +0x844: pshufd  $0xe7,%xmm1,%xmm5
     +0x849: pand    %xmm8,%xmm1
     +0x84e: pshufd  $0xe7,%xmm7,%xmm6
     +0x853: pand    %xmm8,%xmm7
     +0x858: packuswb %xmm1,%xmm7
     +0x85c: packuswb %xmm7,%xmm7
     +0x860: packuswb %xmm7,%xmm7
     +0x864: movdqa  %xmm9,%xmm1
     +0x869: psubb   %xmm4,%xmm1
     +0x86d: movdqa  %xmm9,%xmm0
     +0x872: psubb   %xmm7,%xmm0
     +0x876: pand    %xmm10,%xmm2
     +0x87b: pshuflw $0x24,%xmm2,%xmm2
     +0x880: packuswb %xmm2,%xmm2
     +0x884: movdqa  %xmm11,%xmm4
     +0x889: pandn   %xmm2,%xmm4
     +0x88d: pand    %xmm10,%xmm3
     +0x892: pshuflw $0xe2,%xmm3,%xmm2
     +0x897: packuswb %xmm2,%xmm2
     +0x89b: pand    %xmm11,%xmm2
     +0x8a0: por     %xmm4,%xmm2
     +0x8a4: pand    %xmm10,%xmm5
     +0x8a9: pshuflw $0x24,%xmm5,%xmm3
     +0x8ae: packuswb %xmm3,%xmm3
     +0x8b2: movdqa  %xmm11,%xmm4
     +0x8b7: pandn   %xmm3,%xmm4
     +0x8bb: pand    %xmm10,%xmm6
     +0x8c0: pshuflw $0xe2,%xmm6,%xmm3
     +0x8c5: packuswb %xmm3,%xmm3
     +0x8c9: pand    %xmm11,%xmm3
     +0x8ce: por     %xmm4,%xmm3
     +0x8d2: psllw   $0x4,%xmm2
     +0x8d7: pand    %xmm12,%xmm2
     +0x8dc: psllw   $0x4,%xmm3
     +0x8e1: pand    %xmm12,%xmm3
     +0x8e6: movdqa  %xmm13,%xmm4
     +0x8eb: psubb   %xmm2,%xmm4
     +0x8ef: por     %xmm1,%xmm4
     +0x8f3: movdqa  %xmm13,%xmm1
     +0x8f8: psubb   %xmm3,%xmm1
     +0x8fc: por     %xmm0,%xmm1
     +0x900: movd    %xmm4,0x80(%rbx,%rax,1)
     +0x909: movd    %xmm1,0x84(%rbx,%rax,1)
     +0x912: add     $0x8,%rax
     +0x916: cmp     $0x280,%rax
     +0x91c: jne     <mldsa65_keypair_internal+0x800>
     +0x922: movq    $0x0,0x10(%rsp)
     +0x92b: lea     0x10(%rsp),%rax
     +0x930: xor     %eax,%eax
     +0x932: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x940: movdqa  0x1e0(%rsp,%rax,8),%xmm4
     +0x949: movdqa  0x1f0(%rsp,%rax,8),%xmm5
     +0x952: movdqa  0x200(%rsp,%rax,8),%xmm7
     +0x95b: movdqa  0x210(%rsp,%rax,8),%xmm1
     +0x964: pshufd  $0xe7,%xmm5,%xmm2
     +0x969: pand    %xmm8,%xmm5
     +0x96e: pshufd  $0xe7,%xmm4,%xmm3
     +0x973: pand    %xmm8,%xmm4
     +0x978: packuswb %xmm5,%xmm4
     +0x97c: packuswb %xmm4,%xmm4
     +0x980: packuswb %xmm4,%xmm4
     +0x984: pshufd  $0xe7,%xmm1,%xmm5
     +0x989: pand    %xmm8,%xmm1
     +0x98e: pshufd  $0xe7,%xmm7,%xmm6
     +0x993: pand    %xmm8,%xmm7
     +0x998: packuswb %xmm1,%xmm7
     +0x99c: packuswb %xmm7,%xmm7
     +0x9a0: packuswb %xmm7,%xmm7
     +0x9a4: movdqa  %xmm9,%xmm1
     +0x9a9: psubb   %xmm4,%xmm1
     +0x9ad: movdqa  %xmm9,%xmm0
     +0x9b2: psubb   %xmm7,%xmm0
     +0x9b6: pand    %xmm10,%xmm2
     +0x9bb: pshuflw $0x24,%xmm2,%xmm2
     +0x9c0: packuswb %xmm2,%xmm2
     +0x9c4: movdqa  %xmm11,%xmm4
     +0x9c9: pandn   %xmm2,%xmm4
     +0x9cd: pand    %xmm10,%xmm3
     +0x9d2: pshuflw $0xe2,%xmm3,%xmm2
     +0x9d7: packuswb %xmm2,%xmm2
     +0x9db: pand    %xmm11,%xmm2
     +0x9e0: por     %xmm4,%xmm2
     +0x9e4: pand    %xmm10,%xmm5
     +0x9e9: pshuflw $0x24,%xmm5,%xmm3
     +0x9ee: packuswb %xmm3,%xmm3
     +0x9f2: movdqa  %xmm11,%xmm4
     +0x9f7: pandn   %xmm3,%xmm4
     +0x9fb: pand    %xmm10,%xmm6
     +0xa00: pshuflw $0xe2,%xmm6,%xmm3
     +0xa05: packuswb %xmm3,%xmm3
     +0xa09: pand    %xmm11,%xmm3
     +0xa0e: por     %xmm4,%xmm3
     +0xa12: psllw   $0x4,%xmm2
     +0xa17: pand    %xmm12,%xmm2
     +0xa1c: psllw   $0x4,%xmm3
     +0xa21: pand    %xmm12,%xmm3
     +0xa26: movdqa  %xmm13,%xmm4
     +0xa2b: psubb   %xmm2,%xmm4
     +0xa2f: por     %xmm1,%xmm4
     +0xa33: movdqa  %xmm13,%xmm1
     +0xa38: psubb   %xmm3,%xmm1
     +0xa3c: por     %xmm0,%xmm1
     +0xa40: movd    %xmm4,0x300(%rbx,%rax,1)
     +0xa49: movd    %xmm1,0x304(%rbx,%rax,1)
     +0xa52: add     $0x8,%rax
     +0xa56: cmp     $0x80,%rax
     +0xa5c: jne     <mldsa65_keypair_internal+0x940>
     +0xa62: movq    $0x0,0x10(%rsp)
     +0xa6b: lea     0x10(%rsp),%rax
     +0xa70: mov     $0x380,%eax
     +0xa75: data16  cs nopw 0x0(%rax,%rax,1)
     +0xa80: movdqa  -0x1620(%rsp,%rax,8),%xmm4
     +0xa89: movdqa  -0x1610(%rsp,%rax,8),%xmm5
     +0xa92: movdqa  -0x1600(%rsp,%rax,8),%xmm7
     +0xa9b: movdqa  -0x15f0(%rsp,%rax,8),%xmm1
     +0xaa4: pshufd  $0xe7,%xmm5,%xmm2
     +0xaa9: pand    %xmm8,%xmm5
     +0xaae: pshufd  $0xe7,%xmm4,%xmm3
     +0xab3: pand    %xmm8,%xmm4
     +0xab8: packuswb %xmm5,%xmm4
     +0xabc: packuswb %xmm4,%xmm4
     +0xac0: packuswb %xmm4,%xmm4
     +0xac4: pshufd  $0xe7,%xmm1,%xmm5
     +0xac9: pand    %xmm8,%xmm1
     +0xace: pshufd  $0xe7,%xmm7,%xmm6
     +0xad3: pand    %xmm8,%xmm7
     +0xad8: packuswb %xmm1,%xmm7
     +0xadc: packuswb %xmm7,%xmm7
     +0xae0: packuswb %xmm7,%xmm7
     +0xae4: movdqa  %xmm9,%xmm1
     +0xae9: psubb   %xmm4,%xmm1
     +0xaed: movdqa  %xmm9,%xmm0
     +0xaf2: psubb   %xmm7,%xmm0
     +0xaf6: pand    %xmm10,%xmm2
     +0xafb: pshuflw $0x24,%xmm2,%xmm2
     +0xb00: packuswb %xmm2,%xmm2
     +0xb04: movdqa  %xmm11,%xmm4
     +0xb09: pandn   %xmm2,%xmm4
     +0xb0d: pand    %xmm10,%xmm3
     +0xb12: pshuflw $0xe2,%xmm3,%xmm2
     +0xb17: packuswb %xmm2,%xmm2
     +0xb1b: pand    %xmm11,%xmm2
     +0xb20: por     %xmm4,%xmm2
     +0xb24: pand    %xmm10,%xmm5
     +0xb29: pshuflw $0x24,%xmm5,%xmm3
     +0xb2e: packuswb %xmm3,%xmm3
     +0xb32: movdqa  %xmm11,%xmm4
     +0xb37: pandn   %xmm3,%xmm4
     +0xb3b: pand    %xmm10,%xmm6
     +0xb40: pshuflw $0xe2,%xmm6,%xmm3
     +0xb45: packuswb %xmm3,%xmm3
     +0xb49: pand    %xmm11,%xmm3
     +0xb4e: por     %xmm4,%xmm3
     +0xb52: psllw   $0x4,%xmm2
     +0xb57: pand    %xmm12,%xmm2
     +0xb5c: psllw   $0x4,%xmm3
     +0xb61: pand    %xmm12,%xmm3
     +0xb66: movdqa  %xmm13,%xmm4
     +0xb6b: psubb   %xmm2,%xmm4
     +0xb6f: por     %xmm1,%xmm4
     +0xb73: movdqa  %xmm13,%xmm1
     +0xb78: psubb   %xmm3,%xmm1
     +0xb7c: por     %xmm0,%xmm1
     +0xb80: movd    %xmm4,(%rbx,%rax,1)
     +0xb85: movd    %xmm1,0x4(%rbx,%rax,1)
     +0xb8b: add     $0x8,%rax
     +0xb8f: cmp     $0x400,%rax
     +0xb95: jne     <mldsa65_keypair_internal+0xa80>
     +0xb9b: movq    $0x0,0x10(%rsp)
     +0xba4: lea     0x10(%rsp),%rax
     +0xba9: sub     $0x8,%rsp
     +0xbad: lea     0x1e8(%rsp),%rdi
     +0xbb5: mov     %r13,%rsi
     +0xbb8: mov     %r12,%rdx
     +0xbbb: lea     0xde8(%rsp),%rcx
     +0xbc3: mov     %r15,%r8
     +0xbc6: xor     %r9d,%r9d
     +0xbc9: push    $0x3
     +0xbcb: push    $0x2
     +0xbcd: push    $0x1
     +0xbcf: call    <mldsa65_poly_uniform_eta_4x>
     +0xbd4: movdqa  0x18ae3(%rip),%xmm13
     +0xbdd: movdqa  0x18aca(%rip),%xmm12
     +0xbe6: movdqa  0x18ab1(%rip),%xmm11
     +0xbef: movdqa  0x18a98(%rip),%xmm10
     +0xbf8: movdqa  0x18a7f(%rip),%xmm9
     +0xc01: movdqa  0x18a66(%rip),%xmm8
     +0xc0a: add     $0x20,%rsp
     +0xc0e: mov     $0x4,%eax
     +0xc13: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0xc20: movdqa  0x1c0(%rsp,%rax,8),%xmm4
     +0xc29: movdqa  0x1d0(%rsp,%rax,8),%xmm5
     +0xc32: movdqa  0x1e0(%rsp,%rax,8),%xmm7
     +0xc3b: movdqa  0x1f0(%rsp,%rax,8),%xmm1
     +0xc44: pshufd  $0xe7,%xmm5,%xmm2
     +0xc49: pand    %xmm8,%xmm5
     +0xc4e: pshufd  $0xe7,%xmm4,%xmm3
     +0xc53: pand    %xmm8,%xmm4
     +0xc58: packuswb %xmm5,%xmm4
     +0xc5c: packuswb %xmm4,%xmm4
     +0xc60: packuswb %xmm4,%xmm4
     +0xc64: pshufd  $0xe7,%xmm1,%xmm5
     +0xc69: pand    %xmm8,%xmm1
     +0xc6e: pshufd  $0xe7,%xmm7,%xmm6
     +0xc73: pand    %xmm8,%xmm7
     +0xc78: packuswb %xmm1,%xmm7
     +0xc7c: packuswb %xmm7,%xmm7
     +0xc80: packuswb %xmm7,%xmm7
     +0xc84: movdqa  %xmm9,%xmm1
     +0xc89: psubb   %xmm4,%xmm1
     +0xc8d: movdqa  %xmm9,%xmm0
     +0xc92: psubb   %xmm7,%xmm0
     +0xc96: pand    %xmm10,%xmm2
     +0xc9b: pshuflw $0x24,%xmm2,%xmm2
     +0xca0: packuswb %xmm2,%xmm2
     +0xca4: movdqa  %xmm11,%xmm4
     +0xca9: pandn   %xmm2,%xmm4
     +0xcad: pand    %xmm10,%xmm3
     +0xcb2: pshuflw $0xe2,%xmm3,%xmm2
     +0xcb7: packuswb %xmm2,%xmm2
     +0xcbb: pand    %xmm11,%xmm2
     +0xcc0: por     %xmm4,%xmm2
     +0xcc4: pand    %xmm10,%xmm5
     +0xcc9: pshuflw $0x24,%xmm5,%xmm3
     +0xcce: packuswb %xmm3,%xmm3
     +0xcd2: movdqa  %xmm11,%xmm4
     +0xcd7: pandn   %xmm3,%xmm4
     +0xcdb: pand    %xmm10,%xmm6
     +0xce0: pshuflw $0xe2,%xmm6,%xmm3
     +0xce5: packuswb %xmm3,%xmm3
     +0xce9: pand    %xmm11,%xmm3
     +0xcee: por     %xmm4,%xmm3
     +0xcf2: psllw   $0x4,%xmm2
     +0xcf7: pand    %xmm12,%xmm2
     +0xcfc: psllw   $0x4,%xmm3
     +0xd01: pand    %xmm12,%xmm3
     +0xd06: movdqa  %xmm13,%xmm4
     +0xd0b: psubb   %xmm2,%xmm4
     +0xd0f: por     %xmm1,%xmm4
     +0xd13: movdqa  %xmm13,%xmm1
     +0xd18: psubb   %xmm3,%xmm1
     +0xd1c: por     %xmm0,%xmm1
     +0xd20: movd    %xmm4,0x7c(%rbx,%rax,1)
     +0xd26: movd    %xmm1,0x80(%rbx,%rax,1)
     +0xd2f: add     $0x8,%rax
     +0xd33: cmp     $0x84,%rax
     +0xd39: jne     <mldsa65_keypair_internal+0xc20>
     +0xd3f: movq    $0x0,0x10(%rsp)
     +0xd48: lea     0x10(%rsp),%rax
     +0xd4d: mov     $0x80,%eax
     +0xd52: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0xd60: movdqa  0x1e0(%rsp,%rax,8),%xmm4
     +0xd69: movdqa  0x1f0(%rsp,%rax,8),%xmm5
     +0xd72: movdqa  0x200(%rsp,%rax,8),%xmm7
     +0xd7b: movdqa  0x210(%rsp,%rax,8),%xmm1
     +0xd84: pshufd  $0xe7,%xmm5,%xmm2
     +0xd89: pand    %xmm8,%xmm5
     +0xd8e: pshufd  $0xe7,%xmm4,%xmm3
     +0xd93: pand    %xmm8,%xmm4
     +0xd98: packuswb %xmm5,%xmm4
     +0xd9c: packuswb %xmm4,%xmm4
     +0xda0: packuswb %xmm4,%xmm4
     +0xda4: pshufd  $0xe7,%xmm1,%xmm5
     +0xda9: pand    %xmm8,%xmm1
     +0xdae: pshufd  $0xe7,%xmm7,%xmm6
     +0xdb3: pand    %xmm8,%xmm7
     +0xdb8: packuswb %xmm1,%xmm7
     +0xdbc: packuswb %xmm7,%xmm7
     +0xdc0: packuswb %xmm7,%xmm7
     +0xdc4: movdqa  %xmm9,%xmm1
     +0xdc9: psubb   %xmm4,%xmm1
     +0xdcd: movdqa  %xmm9,%xmm0
     +0xdd2: psubb   %xmm7,%xmm0
     +0xdd6: pand    %xmm10,%xmm2
     +0xddb: pshuflw $0x24,%xmm2,%xmm2
     +0xde0: packuswb %xmm2,%xmm2
     +0xde4: movdqa  %xmm11,%xmm4
     +0xde9: pandn   %xmm2,%xmm4
     +0xded: pand    %xmm10,%xmm3
     +0xdf2: pshuflw $0xe2,%xmm3,%xmm2
     +0xdf7: packuswb %xmm2,%xmm2
     +0xdfb: pand    %xmm11,%xmm2
     +0xe00: por     %xmm4,%xmm2
     +0xe04: pand    %xmm10,%xmm5
     +0xe09: pshuflw $0x24,%xmm5,%xmm3
     +0xe0e: packuswb %xmm3,%xmm3
     +0xe12: movdqa  %xmm11,%xmm4
     +0xe17: pandn   %xmm3,%xmm4
     +0xe1b: pand    %xmm10,%xmm6
     +0xe20: pshuflw $0xe2,%xmm6,%xmm3
     +0xe25: packuswb %xmm3,%xmm3
     +0xe29: pand    %xmm11,%xmm3
     +0xe2e: por     %xmm4,%xmm3
     +0xe32: psllw   $0x4,%xmm2
     +0xe37: pand    %xmm12,%xmm2
     +0xe3c: psllw   $0x4,%xmm3
     +0xe41: pand    %xmm12,%xmm3
     +0xe46: movdqa  %xmm13,%xmm4
     +0xe4b: psubb   %xmm2,%xmm4
     +0xe4f: por     %xmm1,%xmm4
     +0xe53: movdqa  %xmm13,%xmm1
     +0xe58: psubb   %xmm3,%xmm1
     +0xe5c: por     %xmm0,%xmm1
     +0xe60: movd    %xmm4,0x80(%rbx,%rax,1)
     +0xe69: movd    %xmm1,0x84(%rbx,%rax,1)
     +0xe72: add     $0x8,%rax
     +0xe76: cmp     $0x100,%rax
     +0xe7c: jne     <mldsa65_keypair_internal+0xd60>
     +0xe82: movq    $0x0,0x10(%rsp)
     +0xe8b: lea     0x10(%rsp),%rax
     +0xe90: mov     $0x100,%eax
     +0xe95: data16  cs nopw 0x0(%rax,%rax,1)
     +0xea0: movdqa  0x1e0(%rsp,%rax,8),%xmm4
     +0xea9: movdqa  0x1f0(%rsp,%rax,8),%xmm5
     +0xeb2: movdqa  0x200(%rsp,%rax,8),%xmm7
     +0xebb: movdqa  0x210(%rsp,%rax,8),%xmm1
     +0xec4: pshufd  $0xe7,%xmm5,%xmm2
     +0xec9: pand    %xmm8,%xmm5
     +0xece: pshufd  $0xe7,%xmm4,%xmm3
     +0xed3: pand    %xmm8,%xmm4
     +0xed8: packuswb %xmm5,%xmm4
     +0xedc: packuswb %xmm4,%xmm4
     +0xee0: packuswb %xmm4,%xmm4
     +0xee4: pshufd  $0xe7,%xmm1,%xmm5
     +0xee9: pand    %xmm8,%xmm1
     +0xeee: pshufd  $0xe7,%xmm7,%xmm6
     +0xef3: pand    %xmm8,%xmm7
     +0xef8: packuswb %xmm1,%xmm7
     +0xefc: packuswb %xmm7,%xmm7
     +0xf00: packuswb %xmm7,%xmm7
     +0xf04: movdqa  %xmm9,%xmm1
     +0xf09: psubb   %xmm4,%xmm1
     +0xf0d: movdqa  %xmm9,%xmm0
     +0xf12: psubb   %xmm7,%xmm0
     +0xf16: pand    %xmm10,%xmm2
     +0xf1b: pshuflw $0x24,%xmm2,%xmm2
     +0xf20: packuswb %xmm2,%xmm2
     +0xf24: movdqa  %xmm11,%xmm4
     +0xf29: pandn   %xmm2,%xmm4
     +0xf2d: pand    %xmm10,%xmm3
     +0xf32: pshuflw $0xe2,%xmm3,%xmm2
     +0xf37: packuswb %xmm2,%xmm2
     +0xf3b: pand    %xmm11,%xmm2
     +0xf40: por     %xmm4,%xmm2
     +0xf44: pand    %xmm10,%xmm5
     +0xf49: pshuflw $0x24,%xmm5,%xmm3
     +0xf4e: packuswb %xmm3,%xmm3
     +0xf52: movdqa  %xmm11,%xmm4
     +0xf57: pandn   %xmm3,%xmm4
     +0xf5b: pand    %xmm10,%xmm6
     +0xf60: pshuflw $0xe2,%xmm6,%xmm3
     +0xf65: packuswb %xmm3,%xmm3
     +0xf69: pand    %xmm11,%xmm3
     +0xf6e: por     %xmm4,%xmm3
     +0xf72: psllw   $0x4,%xmm2
     +0xf77: pand    %xmm12,%xmm2
     +0xf7c: psllw   $0x4,%xmm3
     +0xf81: pand    %xmm12,%xmm3
     +0xf86: movdqa  %xmm13,%xmm4
     +0xf8b: psubb   %xmm2,%xmm4
     +0xf8f: por     %xmm1,%xmm4
     +0xf93: movdqa  %xmm13,%xmm1
     +0xf98: psubb   %xmm3,%xmm1
     +0xf9c: por     %xmm0,%xmm1
     +0xfa0: movd    %xmm4,0x80(%rbx,%rax,1)
     +0xfa9: movd    %xmm1,0x84(%rbx,%rax,1)
     +0xfb2: add     $0x8,%rax
     +0xfb6: cmp     $0x180,%rax
     +0xfbc: jne     <mldsa65_keypair_internal+0xea0>
     +0xfc2: movq    $0x0,0x10(%rsp)
     +0xfcb: lea     0x10(%rsp),%rax
     +0xfd0: mov     $0x180,%eax
     +0xfd5: data16  cs nopw 0x0(%rax,%rax,1)
     +0xfe0: movdqa  0x1e0(%rsp,%rax,8),%xmm4
     +0xfe9: movdqa  0x1f0(%rsp,%rax,8),%xmm5
     +0xff2: movdqa  0x200(%rsp,%rax,8),%xmm7
     +0xffb: movdqa  0x210(%rsp,%rax,8),%xmm1
    +0x1004: pshufd  $0xe7,%xmm5,%xmm2
    +0x1009: pand    %xmm8,%xmm5
    +0x100e: pshufd  $0xe7,%xmm4,%xmm3
    +0x1013: pand    %xmm8,%xmm4
    +0x1018: packuswb %xmm5,%xmm4
    +0x101c: packuswb %xmm4,%xmm4
    +0x1020: packuswb %xmm4,%xmm4
    +0x1024: pshufd  $0xe7,%xmm1,%xmm5
    +0x1029: pand    %xmm8,%xmm1
    +0x102e: pshufd  $0xe7,%xmm7,%xmm6
    +0x1033: pand    %xmm8,%xmm7
    +0x1038: packuswb %xmm1,%xmm7
    +0x103c: packuswb %xmm7,%xmm7
    +0x1040: packuswb %xmm7,%xmm7
    +0x1044: movdqa  %xmm9,%xmm1
    +0x1049: psubb   %xmm4,%xmm1
    +0x104d: movdqa  %xmm9,%xmm0
    +0x1052: psubb   %xmm7,%xmm0
    +0x1056: pand    %xmm10,%xmm2
    +0x105b: pshuflw $0x24,%xmm2,%xmm2
    +0x1060: packuswb %xmm2,%xmm2
    +0x1064: movdqa  %xmm11,%xmm4
    +0x1069: pandn   %xmm2,%xmm4
    +0x106d: pand    %xmm10,%xmm3
    +0x1072: pshuflw $0xe2,%xmm3,%xmm2
    +0x1077: packuswb %xmm2,%xmm2
    +0x107b: pand    %xmm11,%xmm2
    +0x1080: por     %xmm4,%xmm2
    +0x1084: pand    %xmm10,%xmm5
    +0x1089: pshuflw $0x24,%xmm5,%xmm3
    +0x108e: packuswb %xmm3,%xmm3
    +0x1092: movdqa  %xmm11,%xmm4
    +0x1097: pandn   %xmm3,%xmm4
    +0x109b: pand    %xmm10,%xmm6
    +0x10a0: pshuflw $0xe2,%xmm6,%xmm3
    +0x10a5: packuswb %xmm3,%xmm3
    +0x10a9: pand    %xmm11,%xmm3
    +0x10ae: por     %xmm4,%xmm3
    +0x10b2: psllw   $0x4,%xmm2
    +0x10b7: pand    %xmm12,%xmm2
    +0x10bc: psllw   $0x4,%xmm3
    +0x10c1: pand    %xmm12,%xmm3
    +0x10c6: movdqa  %xmm13,%xmm4
    +0x10cb: psubb   %xmm2,%xmm4
    +0x10cf: por     %xmm1,%xmm4
    +0x10d3: movdqa  %xmm13,%xmm1
    +0x10d8: psubb   %xmm3,%xmm1
    +0x10dc: por     %xmm0,%xmm1
    +0x10e0: movd    %xmm4,0x80(%rbx,%rax,1)
    +0x10e9: movd    %xmm1,0x84(%rbx,%rax,1)
    +0x10f2: add     $0x8,%rax
    +0x10f6: cmp     $0x200,%rax
    +0x10fc: jne     <mldsa65_keypair_internal+0xfe0>
    +0x1102: movq    $0x0,0x10(%rsp)
    +0x110b: lea     0x10(%rsp),%rax
    +0x1110: lea     0x1e0(%rsp),%r15
    +0x1118: mov     %r15,%rdi
    +0x111b: call    <mldsa_poly_ntt>
    +0x1120: mov     %r13,%rdi
    +0x1123: call    <mldsa_poly_ntt>
    +0x1128: mov     %r12,%rdi
    +0x112b: call    <mldsa_poly_ntt>
    +0x1130: lea     0xde0(%rsp),%rdi
    +0x1138: call    <mldsa_poly_ntt>
    +0x113d: lea     0x11e0(%rsp),%rdi
    +0x1145: call    <mldsa_poly_ntt>
    +0x114a: movaps  0x160(%rsp),%xmm0
    +0x1152: movaps  0x170(%rsp),%xmm1
    +0x115a: movups  %xmm1,0x10(%r14)
    +0x115f: movups  %xmm0,(%r14)
    +0x1163: lea     0x20(%r14),%rdi
    +0x1167: lea     0x600(%rbx),%rsi
    +0x116e: lea     0x160(%rsp),%r12
    +0x1176: mov     %r15,%rdx
    +0x1179: lea     0x300(%rbx),%rcx
    +0x1180: mov     %r12,%r8
    +0x1183: call    <mld_compute_pack_t0_t165>
    +0x1188: xorps   %xmm0,%xmm0
    +0x118b: movups  %xmm0,0xcc(%rsp)
    +0x1193: movaps  %xmm0,0xc0(%rsp)
    +0x119b: movaps  %xmm0,0xb0(%rsp)
    +0x11a3: movaps  %xmm0,0xa0(%rsp)
    +0x11ab: movaps  %xmm0,0x90(%rsp)
    +0x11b3: movaps  %xmm0,0x80(%rsp)
    +0x11bb: movaps  %xmm0,0x70(%rsp)
    +0x11c0: movaps  %xmm0,0x60(%rsp)
    +0x11c5: movaps  %xmm0,0x50(%rsp)
    +0x11ca: movaps  %xmm0,0x40(%rsp)
    +0x11cf: movaps  %xmm0,0x30(%rsp)
    +0x11d4: movaps  %xmm0,0x20(%rsp)
    +0x11d9: movaps  %xmm0,0x10(%rsp)
    +0x11de: movups  (%r14),%xmm0
    +0x11e2: movups  0x10(%r14),%xmm1
    +0x11e7: movaps  %xmm0,0x10(%rsp)
    +0x11ec: movaps  %xmm1,0x20(%rsp)
    +0x11f1: movups  0x20(%r14),%xmm0
    +0x11f6: movups  0x30(%r14),%xmm1
    +0x11fb: movaps  %xmm0,0x30(%rsp)
    +0x1200: movaps  %xmm1,0x40(%rsp)
    +0x1205: movups  0x40(%r14),%xmm0
    +0x120a: movups  0x50(%r14),%xmm1
    +0x120f: xorps   0x50(%rsp),%xmm0
    +0x1214: xorps   0x60(%rsp),%xmm1
    +0x1219: movaps  %xmm0,0x50(%rsp)
    +0x121e: movaps  %xmm1,0x60(%rsp)
    +0x1223: movups  0x60(%r14),%xmm0
    +0x1228: movups  0x70(%r14),%xmm1
    +0x122d: xorps   0x70(%rsp),%xmm0
    +0x1232: xorps   0x80(%rsp),%xmm1
    +0x123a: movaps  %xmm0,0x70(%rsp)
    +0x123f: movaps  %xmm1,0x80(%rsp)
    +0x1247: mov     0x80(%r14),%rax
    +0x124e: xor     %rax,0x90(%rsp)
    +0x1256: lea     0x10(%rsp),%r13
    +0x125b: mov     %r13,%rdi
    +0x125e: call    <mldsa_keccakf1600_permute>
    +0x1263: movups  0x88(%r14),%xmm0
    +0x126b: movups  0x98(%r14),%xmm1
    +0x1273: xorps   0x10(%rsp),%xmm0
    +0x1278: xorps   0x20(%rsp),%xmm1
    +0x127d: movaps  %xmm0,0x10(%rsp)
    +0x1282: movaps  %xmm1,0x20(%rsp)
    +0x1287: movups  0xa8(%r14),%xmm0
    +0x128f: movups  0xb8(%r14),%xmm1
    +0x1297: xorps   0x30(%rsp),%xmm0
    +0x129c: xorps   0x40(%rsp),%xmm1
    +0x12a1: movaps  %xmm0,0x30(%rsp)
    +0x12a6: movaps  %xmm1,0x40(%rsp)
    +0x12ab: movups  0xc8(%r14),%xmm0
    +0x12b3: movups  0xd8(%r14),%xmm1
    +0x12bb: xorps   0x50(%rsp),%xmm0
    +0x12c0: xorps   0x60(%rsp),%xmm1
    +0x12c5: movaps  %xmm0,0x50(%rsp)
    +0x12ca: movaps  %xmm1,0x60(%rsp)
    +0x12cf: movups  0xe8(%r14),%xmm0
    +0x12d7: movups  0xf8(%r14),%xmm1
    +0x12df: xorps   0x70(%rsp),%xmm0
    +0x12e4: xorps   0x80(%rsp),%xmm1
    +0x12ec: movaps  %xmm0,0x70(%rsp)
    +0x12f1: movaps  %xmm1,0x80(%rsp)
    +0x12f9: mov     0x108(%r14),%rax
    +0x1300: xor     %rax,0x90(%rsp)
    +0x1308: mov     %r13,%rdi
    +0x130b: call    <mldsa_keccakf1600_permute>
    +0x1310: movups  0x110(%r14),%xmm0
    +0x1318: movups  0x120(%r14),%xmm1
    +0x1320: xorps   0x10(%rsp),%xmm0
    +0x1325: xorps   0x20(%rsp),%xmm1
    +0x132a: movaps  %xmm0,0x10(%rsp)
    +0x132f: movaps  %xmm1,0x20(%rsp)
    +0x1334: movups  0x130(%r14),%xmm0
    +0x133c: movups  0x140(%r14),%xmm1
    +0x1344: xorps   0x30(%rsp),%xmm0
    +0x1349: xorps   0x40(%rsp),%xmm1
    +0x134e: movaps  %xmm0,0x30(%rsp)
    +0x1353: movaps  %xmm1,0x40(%rsp)
    +0x1358: movups  0x150(%r14),%xmm0
    +0x1360: movups  0x160(%r14),%xmm1
    +0x1368: xorps   0x50(%rsp),%xmm0
    +0x136d: xorps   0x60(%rsp),%xmm1
    +0x1372: movaps  %xmm0,0x50(%rsp)
    +0x1377: movaps  %xmm1,0x60(%rsp)
    +0x137c: movups  0x170(%r14),%xmm0
    +0x1384: movups  0x180(%r14),%xmm1
    +0x138c: xorps   0x70(%rsp),%xmm0
    +0x1391: xorps   0x80(%rsp),%xmm1
    +0x1399: movaps  %xmm0,0x70(%rsp)
    +0x139e: movaps  %xmm1,0x80(%rsp)
    +0x13a6: mov     0x190(%r14),%rax
    +0x13ad: xor     %rax,0x90(%rsp)
    +0x13b5: mov     %r13,%rdi
    +0x13b8: call    <mldsa_keccakf1600_permute>
    +0x13bd: movups  0x198(%r14),%xmm0
    +0x13c5: movups  0x1a8(%r14),%xmm1
    +0x13cd: xorps   0x10(%rsp),%xmm0
    +0x13d2: xorps   0x20(%rsp),%xmm1
    +0x13d7: movaps  %xmm0,0x10(%rsp)
    +0x13dc: movaps  %xmm1,0x20(%rsp)
    +0x13e1: movups  0x1b8(%r14),%xmm0
    +0x13e9: movups  0x1c8(%r14),%xmm1
    +0x13f1: xorps   0x30(%rsp),%xmm0
    +0x13f6: xorps   0x40(%rsp),%xmm1
    +0x13fb: movaps  %xmm0,0x30(%rsp)
    +0x1400: movaps  %xmm1,0x40(%rsp)
    +0x1405: movups  0x1d8(%r14),%xmm0
    +0x140d: movups  0x1e8(%r14),%xmm1
    +0x1415: xorps   0x50(%rsp),%xmm0
    +0x141a: xorps   0x60(%rsp),%xmm1
    +0x141f: movaps  %xmm0,0x50(%rsp)
    +0x1424: movaps  %xmm1,0x60(%rsp)
    +0x1429: movups  0x1f8(%r14),%xmm0
    +0x1431: movups  0x208(%r14),%xmm1
    +0x1439: xorps   0x70(%rsp),%xmm0
    +0x143e: xorps   0x80(%rsp),%xmm1
    +0x1446: movaps  %xmm0,0x70(%rsp)
    +0x144b: movaps  %xmm1,0x80(%rsp)
    +0x1453: mov     0x218(%r14),%rax
    +0x145a: xor     %rax,0x90(%rsp)
    +0x1462: mov     %r13,%rdi
    +0x1465: call    <mldsa_keccakf1600_permute>
    +0x146a: movups  0x220(%r14),%xmm0
    +0x1472: movups  0x230(%r14),%xmm1
    +0x147a: xorps   0x10(%rsp),%xmm0
    +0x147f: xorps   0x20(%rsp),%xmm1
    +0x1484: movaps  %xmm0,0x10(%rsp)
    +0x1489: movaps  %xmm1,0x20(%rsp)
    +0x148e: movups  0x240(%r14),%xmm0
    +0x1496: movups  0x250(%r14),%xmm1
    +0x149e: xorps   0x30(%rsp),%xmm0
    +0x14a3: xorps   0x40(%rsp),%xmm1
    +0x14a8: movaps  %xmm0,0x30(%rsp)
    +0x14ad: movaps  %xmm1,0x40(%rsp)
    +0x14b2: movups  0x260(%r14),%xmm0
    +0x14ba: movups  0x270(%r14),%xmm1
    +0x14c2: xorps   0x50(%rsp),%xmm0
    +0x14c7: xorps   0x60(%rsp),%xmm1
    +0x14cc: movaps  %xmm0,0x50(%rsp)
    +0x14d1: movaps  %xmm1,0x60(%rsp)
    +0x14d6: movups  0x280(%r14),%xmm0
    +0x14de: movups  0x290(%r14),%xmm1
    +0x14e6: xorps   0x70(%rsp),%xmm0
    +0x14eb: xorps   0x80(%rsp),%xmm1
    +0x14f3: movaps  %xmm0,0x70(%rsp)
    +0x14f8: movaps  %xmm1,0x80(%rsp)
    +0x1500: mov     0x2a0(%r14),%rax
    +0x1507: xor     %rax,0x90(%rsp)
    +0x150f: mov     %r13,%rdi
    +0x1512: call    <mldsa_keccakf1600_permute>
    +0x1517: movups  0x2a8(%r14),%xmm0
    +0x151f: movups  0x2b8(%r14),%xmm1
    +0x1527: xorps   0x10(%rsp),%xmm0
    +0x152c: xorps   0x20(%rsp),%xmm1
    +0x1531: movaps  %xmm0,0x10(%rsp)
    +0x1536: movaps  %xmm1,0x20(%rsp)
    +0x153b: movups  0x2c8(%r14),%xmm0
    +0x1543: movups  0x2d8(%r14),%xmm1
    +0x154b: xorps   0x30(%rsp),%xmm0
    +0x1550: xorps   0x40(%rsp),%xmm1
    +0x1555: movaps  %xmm0,0x30(%rsp)
    +0x155a: movaps  %xmm1,0x40(%rsp)
    +0x155f: movups  0x2e8(%r14),%xmm0
    +0x1567: movups  0x2f8(%r14),%xmm1
    +0x156f: xorps   0x50(%rsp),%xmm0
    +0x1574: xorps   0x60(%rsp),%xmm1
    +0x1579: movaps  %xmm0,0x50(%rsp)
    +0x157e: movaps  %xmm1,0x60(%rsp)
    +0x1583: movups  0x308(%r14),%xmm0
    +0x158b: movups  0x318(%r14),%xmm1
    +0x1593: xorps   0x70(%rsp),%xmm0
    +0x1598: xorps   0x80(%rsp),%xmm1
    +0x15a0: movaps  %xmm0,0x70(%rsp)
    +0x15a5: movaps  %xmm1,0x80(%rsp)
    +0x15ad: mov     0x328(%r14),%rax
    +0x15b4: xor     %rax,0x90(%rsp)
    +0x15bc: mov     %r13,%rdi
    +0x15bf: call    <mldsa_keccakf1600_permute>
    +0x15c4: movups  0x330(%r14),%xmm0
    +0x15cc: movups  0x340(%r14),%xmm1
    +0x15d4: xorps   0x10(%rsp),%xmm0
    +0x15d9: xorps   0x20(%rsp),%xmm1
    +0x15de: movaps  %xmm0,0x10(%rsp)
    +0x15e3: movaps  %xmm1,0x20(%rsp)
    +0x15e8: movups  0x350(%r14),%xmm0
    +0x15f0: movups  0x360(%r14),%xmm1
    +0x15f8: xorps   0x30(%rsp),%xmm0
    +0x15fd: xorps   0x40(%rsp),%xmm1
    +0x1602: movaps  %xmm0,0x30(%rsp)
    +0x1607: movaps  %xmm1,0x40(%rsp)
    +0x160c: movups  0x370(%r14),%xmm0
    +0x1614: movups  0x380(%r14),%xmm1
    +0x161c: xorps   0x50(%rsp),%xmm0
    +0x1621: xorps   0x60(%rsp),%xmm1
    +0x1626: movaps  %xmm0,0x50(%rsp)
    +0x162b: movaps  %xmm1,0x60(%rsp)
    +0x1630: movups  0x390(%r14),%xmm0
    +0x1638: movups  0x3a0(%r14),%xmm1
    +0x1640: xorps   0x70(%rsp),%xmm0
    +0x1645: xorps   0x80(%rsp),%xmm1
    +0x164d: movaps  %xmm0,0x70(%rsp)
    +0x1652: movaps  %xmm1,0x80(%rsp)
    +0x165a: mov     0x3b0(%r14),%rax
    +0x1661: xor     %rax,0x90(%rsp)
    +0x1669: mov     %r13,%rdi
    +0x166c: call    <mldsa_keccakf1600_permute>
    +0x1671: movups  0x3b8(%r14),%xmm0
    +0x1679: movups  0x3c8(%r14),%xmm1
    +0x1681: xorps   0x10(%rsp),%xmm0
    +0x1686: xorps   0x20(%rsp),%xmm1
    +0x168b: movaps  %xmm0,0x10(%rsp)
    +0x1690: movaps  %xmm1,0x20(%rsp)
    +0x1695: movups  0x3d8(%r14),%xmm0
    +0x169d: movups  0x3e8(%r14),%xmm1
    +0x16a5: xorps   0x30(%rsp),%xmm0
    +0x16aa: xorps   0x40(%rsp),%xmm1
    +0x16af: movaps  %xmm0,0x30(%rsp)
    +0x16b4: movaps  %xmm1,0x40(%rsp)
    +0x16b9: movups  0x3f8(%r14),%xmm0
    +0x16c1: movups  0x408(%r14),%xmm1
    +0x16c9: xorps   0x50(%rsp),%xmm0
    +0x16ce: xorps   0x60(%rsp),%xmm1
    +0x16d3: movaps  %xmm0,0x50(%rsp)
    +0x16d8: movaps  %xmm1,0x60(%rsp)
    +0x16dd: movups  0x418(%r14),%xmm0
    +0x16e5: movups  0x428(%r14),%xmm1
    +0x16ed: xorps   0x70(%rsp),%xmm0
    +0x16f2: xorps   0x80(%rsp),%xmm1
    +0x16fa: movaps  %xmm0,0x70(%rsp)
    +0x16ff: movaps  %xmm1,0x80(%rsp)
    +0x1707: mov     0x438(%r14),%rax
    +0x170e: xor     %rax,0x90(%rsp)
    +0x1716: mov     %r13,%rdi
    +0x1719: call    <mldsa_keccakf1600_permute>
    +0x171e: movups  0x440(%r14),%xmm0
    +0x1726: movups  0x450(%r14),%xmm1
    +0x172e: xorps   0x10(%rsp),%xmm0
    +0x1733: xorps   0x20(%rsp),%xmm1
    +0x1738: movaps  %xmm0,0x10(%rsp)
    +0x173d: movaps  %xmm1,0x20(%rsp)
    +0x1742: movups  0x460(%r14),%xmm0
    +0x174a: movups  0x470(%r14),%xmm1
    +0x1752: xorps   0x30(%rsp),%xmm0
    +0x1757: xorps   0x40(%rsp),%xmm1
    +0x175c: movaps  %xmm0,0x30(%rsp)
    +0x1761: movaps  %xmm1,0x40(%rsp)
    +0x1766: movups  0x480(%r14),%xmm0
    +0x176e: movups  0x490(%r14),%xmm1
    +0x1776: xorps   0x50(%rsp),%xmm0
    +0x177b: xorps   0x60(%rsp),%xmm1
    +0x1780: movaps  %xmm0,0x50(%rsp)
    +0x1785: movaps  %xmm1,0x60(%rsp)
    +0x178a: movups  0x4a0(%r14),%xmm0
    +0x1792: movups  0x4b0(%r14),%xmm1
    +0x179a: xorps   0x70(%rsp),%xmm0
    +0x179f: xorps   0x80(%rsp),%xmm1
    +0x17a7: movaps  %xmm0,0x70(%rsp)
    +0x17ac: movaps  %xmm1,0x80(%rsp)
    +0x17b4: mov     0x4c0(%r14),%rax
    +0x17bb: xor     %rax,0x90(%rsp)
    +0x17c3: mov     %r13,%rdi
    +0x17c6: call    <mldsa_keccakf1600_permute>
    +0x17cb: movups  0x4c8(%r14),%xmm0
    +0x17d3: movups  0x4d8(%r14),%xmm1
    +0x17db: xorps   0x10(%rsp),%xmm0
    +0x17e0: xorps   0x20(%rsp),%xmm1
    +0x17e5: movaps  %xmm0,0x10(%rsp)
    +0x17ea: movaps  %xmm1,0x20(%rsp)
    +0x17ef: movups  0x4e8(%r14),%xmm0
    +0x17f7: movups  0x4f8(%r14),%xmm1
    +0x17ff: xorps   0x30(%rsp),%xmm0
    +0x1804: xorps   0x40(%rsp),%xmm1
    +0x1809: movaps  %xmm0,0x30(%rsp)
    +0x180e: movaps  %xmm1,0x40(%rsp)
    +0x1813: movups  0x508(%r14),%xmm0
    +0x181b: movups  0x518(%r14),%xmm1
    +0x1823: xorps   0x50(%rsp),%xmm0
    +0x1828: xorps   0x60(%rsp),%xmm1
    +0x182d: movaps  %xmm0,0x50(%rsp)
    +0x1832: movaps  %xmm1,0x60(%rsp)
    +0x1837: movups  0x528(%r14),%xmm0
    +0x183f: movups  0x538(%r14),%xmm1
    +0x1847: xorps   0x70(%rsp),%xmm0
    +0x184c: xorps   0x80(%rsp),%xmm1
    +0x1854: movaps  %xmm0,0x70(%rsp)
    +0x1859: movaps  %xmm1,0x80(%rsp)
    +0x1861: mov     0x548(%r14),%rax
    +0x1868: xor     %rax,0x90(%rsp)
    +0x1870: mov     %r13,%rdi
    +0x1873: call    <mldsa_keccakf1600_permute>
    +0x1878: movups  0x550(%r14),%xmm0
    +0x1880: movups  0x560(%r14),%xmm1
    +0x1888: xorps   0x10(%rsp),%xmm0
    +0x188d: xorps   0x20(%rsp),%xmm1
    +0x1892: movaps  %xmm0,0x10(%rsp)
    +0x1897: movaps  %xmm1,0x20(%rsp)
    +0x189c: movups  0x570(%r14),%xmm0
    +0x18a4: movups  0x580(%r14),%xmm1
    +0x18ac: xorps   0x30(%rsp),%xmm0
    +0x18b1: xorps   0x40(%rsp),%xmm1
    +0x18b6: movaps  %xmm0,0x30(%rsp)
    +0x18bb: movaps  %xmm1,0x40(%rsp)
    +0x18c0: movups  0x590(%r14),%xmm0
    +0x18c8: movups  0x5a0(%r14),%xmm1
    +0x18d0: xorps   0x50(%rsp),%xmm0
    +0x18d5: xorps   0x60(%rsp),%xmm1
    +0x18da: movaps  %xmm0,0x50(%rsp)
    +0x18df: movaps  %xmm1,0x60(%rsp)
    +0x18e4: movups  0x5b0(%r14),%xmm0
    +0x18ec: movups  0x5c0(%r14),%xmm1
    +0x18f4: xorps   0x70(%rsp),%xmm0
    +0x18f9: xorps   0x80(%rsp),%xmm1
    +0x1901: movaps  %xmm0,0x70(%rsp)
    +0x1906: movaps  %xmm1,0x80(%rsp)
    +0x190e: mov     0x5d0(%r14),%rax
    +0x1915: xor     %rax,0x90(%rsp)
    +0x191d: mov     %r13,%rdi
    +0x1920: call    <mldsa_keccakf1600_permute>
    +0x1925: movups  0x5d8(%r14),%xmm0
    +0x192d: movups  0x5e8(%r14),%xmm1
    +0x1935: xorps   0x10(%rsp),%xmm0
    +0x193a: xorps   0x20(%rsp),%xmm1
    +0x193f: movaps  %xmm0,0x10(%rsp)
    +0x1944: movaps  %xmm1,0x20(%rsp)
    +0x1949: movups  0x5f8(%r14),%xmm0
    +0x1951: movups  0x608(%r14),%xmm1
    +0x1959: xorps   0x30(%rsp),%xmm0
    +0x195e: xorps   0x40(%rsp),%xmm1
    +0x1963: movaps  %xmm0,0x30(%rsp)
    +0x1968: movaps  %xmm1,0x40(%rsp)
    +0x196d: movups  0x618(%r14),%xmm0
    +0x1975: movups  0x628(%r14),%xmm1
    +0x197d: xorps   0x50(%rsp),%xmm0
    +0x1982: xorps   0x60(%rsp),%xmm1
    +0x1987: movaps  %xmm0,0x50(%rsp)
    +0x198c: movaps  %xmm1,0x60(%rsp)
    +0x1991: movups  0x638(%r14),%xmm0
    +0x1999: movups  0x648(%r14),%xmm1
    +0x19a1: xorps   0x70(%rsp),%xmm0
    +0x19a6: xorps   0x80(%rsp),%xmm1
    +0x19ae: movaps  %xmm0,0x70(%rsp)
    +0x19b3: movaps  %xmm1,0x80(%rsp)
    +0x19bb: mov     0x658(%r14),%rax
    +0x19c2: xor     %rax,0x90(%rsp)
    +0x19ca: mov     %r13,%rdi
    +0x19cd: call    <mldsa_keccakf1600_permute>
    +0x19d2: movups  0x660(%r14),%xmm0
    +0x19da: movups  0x670(%r14),%xmm1
    +0x19e2: xorps   0x10(%rsp),%xmm0
    +0x19e7: xorps   0x20(%rsp),%xmm1
    +0x19ec: movaps  %xmm0,0x10(%rsp)
    +0x19f1: movaps  %xmm1,0x20(%rsp)
    +0x19f6: movups  0x680(%r14),%xmm0
    +0x19fe: movups  0x690(%r14),%xmm1
    +0x1a06: xorps   0x30(%rsp),%xmm0
    +0x1a0b: xorps   0x40(%rsp),%xmm1
    +0x1a10: movaps  %xmm0,0x30(%rsp)
    +0x1a15: movaps  %xmm1,0x40(%rsp)
    +0x1a1a: movups  0x6a0(%r14),%xmm0
    +0x1a22: movups  0x6b0(%r14),%xmm1
    +0x1a2a: xorps   0x50(%rsp),%xmm0
    +0x1a2f: xorps   0x60(%rsp),%xmm1
    +0x1a34: movaps  %xmm0,0x50(%rsp)
    +0x1a39: movaps  %xmm1,0x60(%rsp)
    +0x1a3e: movups  0x6c0(%r14),%xmm0
    +0x1a46: movups  0x6d0(%r14),%xmm1
    +0x1a4e: xorps   0x70(%rsp),%xmm0
    +0x1a53: xorps   0x80(%rsp),%xmm1
    +0x1a5b: movaps  %xmm0,0x70(%rsp)
    +0x1a60: movaps  %xmm1,0x80(%rsp)
    +0x1a68: mov     0x6e0(%r14),%rax
    +0x1a6f: xor     %rax,0x90(%rsp)
    +0x1a77: mov     %r13,%rdi
    +0x1a7a: call    <mldsa_keccakf1600_permute>
    +0x1a7f: movups  0x6e8(%r14),%xmm0
    +0x1a87: movups  0x6f8(%r14),%xmm1
    +0x1a8f: xorps   0x10(%rsp),%xmm0
    +0x1a94: xorps   0x20(%rsp),%xmm1
    +0x1a99: movaps  %xmm0,0x10(%rsp)
    +0x1a9e: movaps  %xmm1,0x20(%rsp)
    +0x1aa3: movups  0x708(%r14),%xmm0
    +0x1aab: movups  0x718(%r14),%xmm1
    +0x1ab3: xorps   0x30(%rsp),%xmm0
    +0x1ab8: xorps   0x40(%rsp),%xmm1
    +0x1abd: movaps  %xmm0,0x30(%rsp)
    +0x1ac2: movaps  %xmm1,0x40(%rsp)
    +0x1ac7: movups  0x728(%r14),%xmm0
    +0x1acf: movups  0x738(%r14),%xmm1
    +0x1ad7: xorps   0x50(%rsp),%xmm0
    +0x1adc: xorps   0x60(%rsp),%xmm1
    +0x1ae1: movaps  %xmm0,0x50(%rsp)
    +0x1ae6: movaps  %xmm1,0x60(%rsp)
    +0x1aeb: movups  0x748(%r14),%xmm0
    +0x1af3: movups  0x758(%r14),%xmm1
    +0x1afb: xorps   0x70(%rsp),%xmm0
    +0x1b00: xorps   0x80(%rsp),%xmm1
    +0x1b08: movaps  %xmm0,0x70(%rsp)
    +0x1b0d: movaps  %xmm1,0x80(%rsp)
    +0x1b15: mov     0x768(%r14),%rax
    +0x1b1c: xor     %rax,0x90(%rsp)
    +0x1b24: mov     %r13,%rdi
    +0x1b27: call    <mldsa_keccakf1600_permute>
    +0x1b2c: movups  0x770(%r14),%xmm0
    +0x1b34: xorps   0x10(%rsp),%xmm0
    +0x1b39: movaps  %xmm0,0x10(%rsp)
    +0x1b3e: movups  0x780(%r14),%xmm0
    +0x1b46: xorps   0x20(%rsp),%xmm0
    +0x1b4b: movaps  %xmm0,0x20(%rsp)
    +0x1b50: movups  0x790(%r14),%xmm0
    +0x1b58: xorps   0x30(%rsp),%xmm0
    +0x1b5d: movaps  %xmm0,0x30(%rsp)
    +0x1b62: xorb    $0x1f,0x40(%rsp)
    +0x1b67: xorb    $0x80,0x97(%rsp)
    +0x1b6f: movl    $0x88,0xd8(%rsp)
    +0x1b7a: mov     %r13,%rdi
    +0x1b7d: call    <mldsa_keccakf1600_permute>
    +0x1b82: movaps  0x10(%rsp),%xmm0
    +0x1b87: movaps  0x20(%rsp),%xmm1
    +0x1b8c: movaps  0x30(%rsp),%xmm2
    +0x1b91: movaps  0x40(%rsp),%xmm3
    +0x1b96: movaps  %xmm3,0x150(%rsp)
    +0x1b9e: movaps  %xmm2,0x140(%rsp)
    +0x1ba6: movaps  %xmm1,0x130(%rsp)
    +0x1bae: movaps  %xmm0,0x120(%rsp)
    +0x1bb6: xorps   %xmm0,%xmm0
    +0x1bb9: movaps  %xmm0,0x50(%rsp)
    +0x1bbe: movaps  %xmm0,0x60(%rsp)
    +0x1bc3: movaps  %xmm0,0x70(%rsp)
    +0x1bc8: movaps  %xmm0,0x80(%rsp)
    +0x1bd0: movaps  %xmm0,0x90(%rsp)
    +0x1bd8: movaps  %xmm0,0xa0(%rsp)
    +0x1be0: movaps  %xmm0,0xb0(%rsp)
    +0x1be8: movaps  %xmm0,0xc0(%rsp)
    +0x1bf0: movaps  %xmm0,0xd0(%rsp)
    +0x1bf8: movaps  %xmm0,0x10(%rsp)
    +0x1bfd: movaps  %xmm0,0x20(%rsp)
    +0x1c02: movaps  %xmm0,0x30(%rsp)
    +0x1c07: movaps  %xmm0,0x40(%rsp)
    +0x1c0c: movaps  0x160(%rsp),%xmm0
    +0x1c14: movaps  0x170(%rsp),%xmm1
    +0x1c1c: movups  %xmm1,0x10(%rbx)
    +0x1c20: movups  %xmm0,(%rbx)
    +0x1c23: movaps  0x1c0(%rsp),%xmm0
    +0x1c2b: movaps  0x1d0(%rsp),%xmm1
    +0x1c33: movups  %xmm1,0x30(%rbx)
    +0x1c37: movups  %xmm0,0x20(%rbx)
    +0x1c3b: movaps  0x120(%rsp),%xmm0
    +0x1c43: movaps  0x130(%rsp),%xmm1
    +0x1c4b: movaps  0x140(%rsp),%xmm2
    +0x1c53: movaps  0x150(%rsp),%xmm3
    +0x1c5b: movups  %xmm0,0x40(%rbx)
    +0x1c5f: movups  %xmm1,0x50(%rbx)
    +0x1c63: movups  %xmm2,0x60(%rbx)
    +0x1c67: movups  %xmm3,0x70(%rbx)
    +0x1c6b: mov     $0x1400,%edx
    +0x1c70: mov     %r15,%rdi
    +0x1c73: xor     %esi,%esi
    +0x1c75: call    <memset>
    +0x1c7a: xorps   %xmm0,%xmm0
    +0x1c7d: movaps  %xmm0,0x150(%rsp)
    +0x1c85: movaps  %xmm0,0x140(%rsp)
    +0x1c8d: movaps  %xmm0,0x130(%rsp)
    +0x1c95: movaps  %xmm0,0x120(%rsp)
    +0x1c9d: lea     0x120(%rsp),%rax
    +0x1ca5: movaps  %xmm0,0xf0(%rsp)
    +0x1cad: movaps  %xmm0,0xe0(%rsp)
    +0x1cb5: movw    $0x0,0x100(%rsp)
    +0x1cbf: lea     0xe0(%rsp),%rax
    +0x1cc7: movaps  %xmm0,0x1d0(%rsp)
    +0x1ccf: movaps  %xmm0,0x1c0(%rsp)
    +0x1cd7: movaps  %xmm0,0x1b0(%rsp)
    +0x1cdf: movaps  %xmm0,0x1a0(%rsp)
    +0x1ce7: movaps  %xmm0,0x190(%rsp)
    +0x1cef: movaps  %xmm0,0x180(%rsp)
    +0x1cf7: movaps  %xmm0,0x170(%rsp)
    +0x1cff: movaps  %xmm0,0x160(%rsp)
    +0x1d07: xor     %eax,%eax
    +0x1d09: lea     -0x28(%rbp),%rsp
    +0x1d0d: pop     %rbx
    +0x1d0e: pop     %r12
    +0x1d10: pop     %r13
    +0x1d12: pop     %r14
    +0x1d14: pop     %r15
    +0x1d16: pop     %rbp
    +0x1d17: xor     %ecx,%ecx
    +0x1d19: xor     %edi,%edi
    +0x1d1b: xor     %edx,%edx
    +0x1d1d: xor     %esi,%esi
    +0x1d1f: xor     %r8d,%r8d
    +0x1d22: xor     %r9d,%r9d
    +0x1d25: ret     
 ***)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa65_keypair_internal";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. From the seed SEED (32 bytes at seed), the public key at pk  *)
(* (1952 bytes) becomes mld_keypair_pk_65 SEED and the secret key at sk      *)
(* (4032 bytes) mld_keypair_sk_65 SEED, and the result is 0. The stack is    *)
(* the 10620 bytes below the return address: the six saved registers, up to  *)
(* 31 bytes of realignment, the frame of 5632 bytes and the 4909 bytes of    *)
(* the call of mld_compute_pack_t0_t165, the deepest callee.                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !pk sk seed SEED pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 6 5 (mld_keypair_rho 6 5 SEED) /\
        mld_keypair_terminates_65 SEED /\
        PAIRWISE nonoverlapping
         [(pk,1952); (sk,4032);
          (word_sub stackpointer (word 10620),10620)] /\
        ALLPAIRS nonoverlapping
         [(pk,1952); (sk,4032);
          (word_sub stackpointer (word 10620),10620)]
         [(seed,32); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pk,1952); (sk,4032)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_keypair_internal) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pk; sk; seed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,32)) s = SEED)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word 0 /\
                  (!j. j < 1952
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           mld_keypair_pk_65 SEED j) /\
                  (!j. j < 4032
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           mld_keypair_sk_65 SEED j))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                memory :> bytes(word_sub stackpointer (word 10620),10620)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, whether each nibble read by  *)
(* the sampling of each polynomial is accepted (mld_keypair_declass_65) and  *)
(* the stack, with all accesses within the arguments, the stack, the return  *)
(* address and the constants of the function and of the callees, and the     *)
(* writes within the keys and the stack.                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e pk sk seed SEED pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 6 5 (mld_keypair_rho 6 5 SEED) /\
        mld_keypair_terminates_65 SEED /\
        PAIRWISE nonoverlapping
         [(pk,1952); (sk,4032);
          (word_sub stackpointer (word 10620),10620)] /\
        ALLPAIRS nonoverlapping
         [(pk,1952); (sk,4032);
          (word_sub stackpointer (word 10620),10620)]
         [(seed,32); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pk,1952); (sk,4032)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_keypair_internal) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pk; sk; seed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,32)) s = SEED /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word 0 /\
                  (!j. j < 1952
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           mld_keypair_pk_65 SEED j) /\
                  (!j. j < 4032
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           mld_keypair_sk_65 SEED j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events pk sk seed (mld_keypair_rho 6 5 SEED)
                           (mld_keypair_declass_65 SEED) mf mc pc
                           (word_sub stackpointer (word 10620))
                           returnaddress /\
                     memaccess_inbounds e2
                      [seed,32; pk,1952; sk,4032;
                       word_sub stackpointer (word 10620),10620;
                       stackpointer,8; word(pc + got_memset),8;
                       word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_ntt_consts),256;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word(pc + mld_compute_pack_t0_t165_consts),768;
                       word(pc + mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32;
                       word(pc + mldsa65_keypair_internal_consts),96]
                      [pk,1952; sk,4032;
                       word_sub stackpointer (word 10620),10620]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                memory :> bytes(word_sub stackpointer (word 10620),10620)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e pk sk seed SEED pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 6 5 (mld_keypair_rho 6 5 SEED) /\
        mld_keypair_terminates_65 SEED /\
        PAIRWISE nonoverlapping
         [(pk,1952); (sk,4032);
          (word_sub stackpointer (word 10620),10620)] /\
        ALLPAIRS nonoverlapping
         [(pk,1952); (sk,4032);
          (word_sub stackpointer (word 10620),10620)]
         [(seed,32); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pk,1952); (sk,4032)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_keypair_internal) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pk; sk; seed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,32)) s = SEED /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events pk sk seed (mld_keypair_rho 6 5 SEED)
                           (mld_keypair_declass_65 SEED) mf mc pc
                           (word_sub stackpointer (word 10620))
                           returnaddress /\
                     memaccess_inbounds e2
                      [seed,32; pk,1952; sk,4032;
                       word_sub stackpointer (word 10620),10620;
                       stackpointer,8; word(pc + got_memset),8;
                       word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_ntt_consts),256;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word(pc + mld_compute_pack_t0_t165_consts),768;
                       word(pc + mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32;
                       word(pc + mldsa65_keypair_internal_consts),96]
                      [pk,1952; sk,4032;
                       word_sub stackpointer (word 10620),10620]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                memory :> bytes(word_sub stackpointer (word 10620),10620)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
