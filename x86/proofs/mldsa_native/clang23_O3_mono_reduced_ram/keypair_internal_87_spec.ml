(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the statement. This is the code for                       *)
(* mldsa87_keypair_internal (mld_sign_keypair_internal in sign.c) from       *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3    *)
(* and MLD_CONFIG_REDUCE_RAM (the monolithic build, see                      *)
(* mldsa_native/README.md). Clang inlines most of it: the SHAKE256 of the    *)
(* seed that gives rho, rho' and the key (one permutation with               *)
(* mldsa_keccakf1600_permute), the packing of each polynomial of s2 and s1   *)
(* into the secret key (mld_polyeta_pack), the copies of rho, the key and tr *)
(* into the keys, and the SHAKE256 of the public key into tr (20             *)
(* permutations). It calls mldsa87_poly_uniform_eta_4x four times, for the   *)
(* last four polynomials of s2, the first four, the last three of s1 and one *)
(* with the irrelevant nonce 255, and the first four of s1, mldsa_poly_ntt   *)
(* for each polynomial of s1 and mld_compute_pack_t0_t187, which computes t  *)
(* and packs t1 into the public key and t0 into the secret key, and clears   *)
(* its buffers with SSE stores and memset. It aligns its frame to 32 bytes   *)
(* (see utils/mldsa_native_realign.ml). It is verified in the whole image    *)
(* (see libmldsa.ml) against mld_keypair_pk_87 and mld_keypair_sk_87 of      *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and for   *)
(* the inlined regions (keypair_internal_87_lemmas.ml), assuming that the    *)
(* sampling of the matrix and of each polynomial terminates, and shown to be *)
(* constant time and memory safe, with the events depending only on the      *)
(* addresses and the values that the C code declassifies (rho and            *)
(* mld_keypair_declass_87).                                                  *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa87_keypair_internal:
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
      +0x20: sub     $0xe20,%rsp
      +0x27: mov     %rsi,%rbx
      +0x2a: movups  (%rdx),%xmm0
      +0x2d: movups  0x10(%rdx),%xmm1
      +0x31: movaps  %xmm1,0xf0(%rsp)
      +0x39: movaps  %xmm0,0xe0(%rsp)
      +0x41: movw    $0x708,0x100(%rsp)
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
     +0x178: movaps  0x1e0(%rsp),%xmm0
     +0x180: movaps  0x1f0(%rsp),%xmm1
     +0x188: movaps  0x200(%rsp),%xmm2
     +0x190: movaps  0x210(%rsp),%xmm3
     +0x198: movaps  %xmm3,0x190(%rsp)
     +0x1a0: movaps  %xmm2,0x180(%rsp)
     +0x1a8: movaps  %xmm1,0x170(%rsp)
     +0x1b0: movaps  %xmm0,0x160(%rsp)
     +0x1b8: lea     0x180(%rsp),%r15
     +0x1c0: xorps   %xmm0,%xmm0
     +0x1c3: movaps  %xmm0,0x260(%rsp)
     +0x1cb: movaps  %xmm0,0x270(%rsp)
     +0x1d3: movaps  %xmm0,0x280(%rsp)
     +0x1db: movaps  %xmm0,0x290(%rsp)
     +0x1e3: movaps  %xmm0,0x2a0(%rsp)
     +0x1eb: movaps  %xmm0,0x1e0(%rsp)
     +0x1f3: movaps  %xmm0,0x1f0(%rsp)
     +0x1fb: movaps  %xmm0,0x200(%rsp)
     +0x203: movaps  %xmm0,0x210(%rsp)
     +0x20b: movaps  %xmm0,0x220(%rsp)
     +0x213: movaps  %xmm0,0x230(%rsp)
     +0x21b: movaps  %xmm0,0x240(%rsp)
     +0x223: movaps  %xmm0,0x250(%rsp)
     +0x22b: lea     0x5e0(%rsp),%rsi
     +0x233: lea     0x9e0(%rsp),%rdx
     +0x23b: lea     0xde0(%rsp),%rcx
     +0x243: sub     $0x8,%rsp
     +0x247: lea     0x1e8(%rsp),%rdi
     +0x24f: mov     %r15,%r8
     +0x252: mov     $0xb,%r9d
     +0x258: push    $0xe
     +0x25a: push    $0xd
     +0x25c: push    $0xc
     +0x25e: call    <mldsa87_poly_uniform_eta_4x>
     +0x263: add     $0x20,%rsp
     +0x267: lea     0x4a2(%rbx),%rax
     +0x26e: mov     $0x1c,%ecx
     +0x273: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x280: mov     $0x2,%r8b
     +0x283: sub     0x1c4(%rsp,%rcx,1),%r8b
     +0x28b: mov     $0x2,%r9b
     +0x28e: sub     0x1cc(%rsp,%rcx,1),%r9b
     +0x296: movzbl  0x1c8(%rsp,%rcx,1),%r10d
     +0x29f: movzbl  0x1d0(%rsp,%rcx,1),%r11d
     +0x2a8: movzbl  0x1d4(%rsp,%rcx,1),%r12d
     +0x2b1: mov     $0x2,%sil
     +0x2b4: sub     0x1d8(%rsp,%rcx,1),%sil
     +0x2bc: movzbl  0x1dc(%rsp,%rcx,1),%edi
     +0x2c4: movzbl  0x1e0(%rsp,%rcx,1),%edx
     +0x2cc: shl     $0x3,%r10b
     +0x2d0: mov     $0x10,%r13b
     +0x2d3: sub     %r10b,%r13b
     +0x2d6: or      %r8b,%r13b
     +0x2d9: mov     %r9d,%r8d
     +0x2dc: shl     $0x6,%r8b
     +0x2e0: or      %r13b,%r8b
     +0x2e3: mov     %r8b,-0x2(%rax)
     +0x2e7: shr     $0x2,%r9b
     +0x2eb: add     %r11b,%r11b
     +0x2ee: mov     $0x4,%r8b
     +0x2f1: sub     %r11b,%r8b
     +0x2f4: or      %r9b,%r8b
     +0x2f7: shl     $0x4,%r12b
     +0x2fb: mov     $0x20,%r9b
     +0x2fe: sub     %r12b,%r9b
     +0x301: mov     %esi,%r10d
     +0x304: shl     $0x7,%r10b
     +0x308: or      %r9b,%r10b
     +0x30b: or      %r8b,%r10b
     +0x30e: mov     %r10b,-0x1(%rax)
     +0x312: shr     $1,%sil
     +0x315: shl     $0x2,%dil
     +0x319: mov     $0x8,%r8b
     +0x31c: sub     %dil,%r8b
     +0x31f: or      %sil,%r8b
     +0x322: shl     $0x5,%dl
     +0x325: mov     $0x40,%sil
     +0x328: sub     %dl,%sil
     +0x32b: or      %r8b,%sil
     +0x32e: mov     %sil,(%rax)
     +0x331: add     $0x20,%rcx
     +0x335: add     $0x3,%rax
     +0x339: cmp     $0x41c,%rcx
     +0x340: jne     <mldsa87_keypair_internal+0x280>
     +0x346: movq    $0x0,0x10(%rsp)
     +0x34f: lea     0x10(%rsp),%rax
     +0x354: mov     $0x502,%eax
     +0x359: lea     0x5fc(%rsp),%rcx
     +0x361: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x370: mov     $0x2,%r8b
     +0x373: sub     -0x1c(%rcx),%r8b
     +0x377: mov     $0x2,%r9b
     +0x37a: sub     -0x14(%rcx),%r9b
     +0x37e: movzbl  -0x18(%rcx),%r10d
     +0x383: movzbl  -0x10(%rcx),%r11d
     +0x388: movzbl  -0xc(%rcx),%r12d
     +0x38d: mov     $0x2,%sil
     +0x390: sub     -0x8(%rcx),%sil
     +0x394: movzbl  -0x4(%rcx),%edi
     +0x398: movzbl  (%rcx),%edx
     +0x39b: shl     $0x3,%r10b
     +0x39f: mov     $0x10,%r13b
     +0x3a2: sub     %r10b,%r13b
     +0x3a5: or      %r8b,%r13b
     +0x3a8: mov     %r9d,%r8d
     +0x3ab: shl     $0x6,%r8b
     +0x3af: or      %r13b,%r8b
     +0x3b2: mov     %r8b,-0x2(%rbx,%rax,1)
     +0x3b7: shr     $0x2,%r9b
     +0x3bb: add     %r11b,%r11b
     +0x3be: mov     $0x4,%r8b
     +0x3c1: sub     %r11b,%r8b
     +0x3c4: or      %r9b,%r8b
     +0x3c7: shl     $0x4,%r12b
     +0x3cb: mov     $0x20,%r9b
     +0x3ce: sub     %r12b,%r9b
     +0x3d1: mov     %esi,%r10d
     +0x3d4: shl     $0x7,%r10b
     +0x3d8: or      %r9b,%r10b
     +0x3db: or      %r8b,%r10b
     +0x3de: mov     %r10b,-0x1(%rbx,%rax,1)
     +0x3e3: shr     $1,%sil
     +0x3e6: shl     $0x2,%dil
     +0x3ea: mov     $0x8,%r8b
     +0x3ed: sub     %dil,%r8b
     +0x3f0: or      %sil,%r8b
     +0x3f3: shl     $0x5,%dl
     +0x3f6: mov     $0x40,%sil
     +0x3f9: sub     %dl,%sil
     +0x3fc: or      %r8b,%sil
     +0x3ff: mov     %sil,(%rbx,%rax,1)
     +0x403: add     $0x3,%rax
     +0x407: add     $0x20,%rcx
     +0x40b: cmp     $0x562,%rax
     +0x411: jne     <mldsa87_keypair_internal+0x370>
     +0x417: movq    $0x0,0x10(%rsp)
     +0x420: lea     0x10(%rsp),%rax
     +0x425: mov     $0x562,%eax
     +0x42a: lea     0x9fc(%rsp),%rcx
     +0x432: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x440: mov     $0x2,%r8b
     +0x443: sub     -0x1c(%rcx),%r8b
     +0x447: mov     $0x2,%r9b
     +0x44a: sub     -0x14(%rcx),%r9b
     +0x44e: movzbl  -0x18(%rcx),%r10d
     +0x453: movzbl  -0x10(%rcx),%r11d
     +0x458: movzbl  -0xc(%rcx),%r12d
     +0x45d: mov     $0x2,%sil
     +0x460: sub     -0x8(%rcx),%sil
     +0x464: movzbl  -0x4(%rcx),%edi
     +0x468: movzbl  (%rcx),%edx
     +0x46b: shl     $0x3,%r10b
     +0x46f: mov     $0x10,%r13b
     +0x472: sub     %r10b,%r13b
     +0x475: or      %r8b,%r13b
     +0x478: mov     %r9d,%r8d
     +0x47b: shl     $0x6,%r8b
     +0x47f: or      %r13b,%r8b
     +0x482: mov     %r8b,-0x2(%rbx,%rax,1)
     +0x487: shr     $0x2,%r9b
     +0x48b: add     %r11b,%r11b
     +0x48e: mov     $0x4,%r8b
     +0x491: sub     %r11b,%r8b
     +0x494: or      %r9b,%r8b
     +0x497: shl     $0x4,%r12b
     +0x49b: mov     $0x20,%r9b
     +0x49e: sub     %r12b,%r9b
     +0x4a1: mov     %esi,%r10d
     +0x4a4: shl     $0x7,%r10b
     +0x4a8: or      %r9b,%r10b
     +0x4ab: or      %r8b,%r10b
     +0x4ae: mov     %r10b,-0x1(%rbx,%rax,1)
     +0x4b3: shr     $1,%sil
     +0x4b6: shl     $0x2,%dil
     +0x4ba: mov     $0x8,%r8b
     +0x4bd: sub     %dil,%r8b
     +0x4c0: or      %sil,%r8b
     +0x4c3: shl     $0x5,%dl
     +0x4c6: mov     $0x40,%sil
     +0x4c9: sub     %dl,%sil
     +0x4cc: or      %r8b,%sil
     +0x4cf: mov     %sil,(%rbx,%rax,1)
     +0x4d3: add     $0x3,%rax
     +0x4d7: add     $0x20,%rcx
     +0x4db: cmp     $0x5c2,%rax
     +0x4e1: jne     <mldsa87_keypair_internal+0x440>
     +0x4e7: movq    $0x0,0x10(%rsp)
     +0x4f0: lea     0x10(%rsp),%rax
     +0x4f5: mov     $0x5c2,%eax
     +0x4fa: lea     0xdfc(%rsp),%rcx
     +0x502: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x510: mov     $0x2,%r8b
     +0x513: sub     -0x1c(%rcx),%r8b
     +0x517: mov     $0x2,%r9b
     +0x51a: sub     -0x14(%rcx),%r9b
     +0x51e: movzbl  -0x18(%rcx),%r10d
     +0x523: movzbl  -0x10(%rcx),%r11d
     +0x528: movzbl  -0xc(%rcx),%r12d
     +0x52d: mov     $0x2,%sil
     +0x530: sub     -0x8(%rcx),%sil
     +0x534: movzbl  -0x4(%rcx),%edi
     +0x538: movzbl  (%rcx),%edx
     +0x53b: shl     $0x3,%r10b
     +0x53f: mov     $0x10,%r13b
     +0x542: sub     %r10b,%r13b
     +0x545: or      %r8b,%r13b
     +0x548: mov     %r9d,%r8d
     +0x54b: shl     $0x6,%r8b
     +0x54f: or      %r13b,%r8b
     +0x552: mov     %r8b,-0x2(%rbx,%rax,1)
     +0x557: shr     $0x2,%r9b
     +0x55b: add     %r11b,%r11b
     +0x55e: mov     $0x4,%r8b
     +0x561: sub     %r11b,%r8b
     +0x564: or      %r9b,%r8b
     +0x567: shl     $0x4,%r12b
     +0x56b: mov     $0x20,%r9b
     +0x56e: sub     %r12b,%r9b
     +0x571: mov     %esi,%r10d
     +0x574: shl     $0x7,%r10b
     +0x578: or      %r9b,%r10b
     +0x57b: or      %r8b,%r10b
     +0x57e: mov     %r10b,-0x1(%rbx,%rax,1)
     +0x583: shr     $1,%sil
     +0x586: shl     $0x2,%dil
     +0x58a: mov     $0x8,%r8b
     +0x58d: sub     %dil,%r8b
     +0x590: or      %sil,%r8b
     +0x593: shl     $0x5,%dl
     +0x596: mov     $0x40,%sil
     +0x599: sub     %dl,%sil
     +0x59c: or      %r8b,%sil
     +0x59f: mov     %sil,(%rbx,%rax,1)
     +0x5a3: add     $0x3,%rax
     +0x5a7: add     $0x20,%rcx
     +0x5ab: cmp     $0x622,%rax
     +0x5b1: jne     <mldsa87_keypair_internal+0x510>
     +0x5b7: movq    $0x0,0x10(%rsp)
     +0x5c0: lea     0x10(%rsp),%rax
     +0x5c5: sub     $0x8,%rsp
     +0x5c9: lea     0x1e8(%rsp),%rdi
     +0x5d1: lea     0x5e8(%rsp),%rsi
     +0x5d9: lea     0x9e8(%rsp),%rdx
     +0x5e1: lea     0xde8(%rsp),%rcx
     +0x5e9: mov     %r15,%r8
     +0x5ec: mov     $0x7,%r9d
     +0x5f2: push    $0xa
     +0x5f4: push    $0x9
     +0x5f6: push    $0x8
     +0x5f8: call    <mldsa87_poly_uniform_eta_4x>
     +0x5fd: add     $0x20,%rsp
     +0x601: mov     $0x322,%eax
     +0x606: lea     0x1fc(%rsp),%rcx
     +0x60e: xchg    %ax,%ax
     +0x610: mov     $0x2,%r8b
     +0x613: sub     -0x1c(%rcx),%r8b
     +0x617: mov     $0x2,%r9b
     +0x61a: sub     -0x14(%rcx),%r9b
     +0x61e: movzbl  -0x18(%rcx),%r10d
     +0x623: movzbl  -0x10(%rcx),%r11d
     +0x628: movzbl  -0xc(%rcx),%r12d
     +0x62d: mov     $0x2,%sil
     +0x630: sub     -0x8(%rcx),%sil
     +0x634: movzbl  -0x4(%rcx),%edi
     +0x638: movzbl  (%rcx),%edx
     +0x63b: shl     $0x3,%r10b
     +0x63f: mov     $0x10,%r13b
     +0x642: sub     %r10b,%r13b
     +0x645: or      %r8b,%r13b
     +0x648: mov     %r9d,%r8d
     +0x64b: shl     $0x6,%r8b
     +0x64f: or      %r13b,%r8b
     +0x652: mov     %r8b,-0x2(%rbx,%rax,1)
     +0x657: shr     $0x2,%r9b
     +0x65b: add     %r11b,%r11b
     +0x65e: mov     $0x4,%r8b
     +0x661: sub     %r11b,%r8b
     +0x664: or      %r9b,%r8b
     +0x667: shl     $0x4,%r12b
     +0x66b: mov     $0x20,%r9b
     +0x66e: sub     %r12b,%r9b
     +0x671: mov     %esi,%r10d
     +0x674: shl     $0x7,%r10b
     +0x678: or      %r9b,%r10b
     +0x67b: or      %r8b,%r10b
     +0x67e: mov     %r10b,-0x1(%rbx,%rax,1)
     +0x683: shr     $1,%sil
     +0x686: shl     $0x2,%dil
     +0x68a: mov     $0x8,%r8b
     +0x68d: sub     %dil,%r8b
     +0x690: or      %sil,%r8b
     +0x693: shl     $0x5,%dl
     +0x696: mov     $0x40,%sil
     +0x699: sub     %dl,%sil
     +0x69c: or      %r8b,%sil
     +0x69f: mov     %sil,(%rbx,%rax,1)
     +0x6a3: add     $0x3,%rax
     +0x6a7: add     $0x20,%rcx
     +0x6ab: cmp     $0x382,%rax
     +0x6b1: jne     <mldsa87_keypair_internal+0x610>
     +0x6b7: movq    $0x0,0x10(%rsp)
     +0x6c0: lea     0x10(%rsp),%rax
     +0x6c5: mov     $0x382,%eax
     +0x6ca: lea     0x5fc(%rsp),%rcx
     +0x6d2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x6e0: mov     $0x2,%r8b
     +0x6e3: sub     -0x1c(%rcx),%r8b
     +0x6e7: mov     $0x2,%r9b
     +0x6ea: sub     -0x14(%rcx),%r9b
     +0x6ee: movzbl  -0x18(%rcx),%r10d
     +0x6f3: movzbl  -0x10(%rcx),%r11d
     +0x6f8: movzbl  -0xc(%rcx),%r12d
     +0x6fd: mov     $0x2,%sil
     +0x700: sub     -0x8(%rcx),%sil
     +0x704: movzbl  -0x4(%rcx),%edi
     +0x708: movzbl  (%rcx),%edx
     +0x70b: shl     $0x3,%r10b
     +0x70f: mov     $0x10,%r13b
     +0x712: sub     %r10b,%r13b
     +0x715: or      %r8b,%r13b
     +0x718: mov     %r9d,%r8d
     +0x71b: shl     $0x6,%r8b
     +0x71f: or      %r13b,%r8b
     +0x722: mov     %r8b,-0x2(%rbx,%rax,1)
     +0x727: shr     $0x2,%r9b
     +0x72b: add     %r11b,%r11b
     +0x72e: mov     $0x4,%r8b
     +0x731: sub     %r11b,%r8b
     +0x734: or      %r9b,%r8b
     +0x737: shl     $0x4,%r12b
     +0x73b: mov     $0x20,%r9b
     +0x73e: sub     %r12b,%r9b
     +0x741: mov     %esi,%r10d
     +0x744: shl     $0x7,%r10b
     +0x748: or      %r9b,%r10b
     +0x74b: or      %r8b,%r10b
     +0x74e: mov     %r10b,-0x1(%rbx,%rax,1)
     +0x753: shr     $1,%sil
     +0x756: shl     $0x2,%dil
     +0x75a: mov     $0x8,%r8b
     +0x75d: sub     %dil,%r8b
     +0x760: or      %sil,%r8b
     +0x763: shl     $0x5,%dl
     +0x766: mov     $0x40,%sil
     +0x769: sub     %dl,%sil
     +0x76c: or      %r8b,%sil
     +0x76f: mov     %sil,(%rbx,%rax,1)
     +0x773: add     $0x3,%rax
     +0x777: add     $0x20,%rcx
     +0x77b: cmp     $0x3e2,%rax
     +0x781: jne     <mldsa87_keypair_internal+0x6e0>
     +0x787: movq    $0x0,0x10(%rsp)
     +0x790: lea     0x10(%rsp),%rax
     +0x795: mov     $0x3e2,%eax
     +0x79a: lea     0x9fc(%rsp),%rcx
     +0x7a2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x7b0: mov     $0x2,%r8b
     +0x7b3: sub     -0x1c(%rcx),%r8b
     +0x7b7: mov     $0x2,%r9b
     +0x7ba: sub     -0x14(%rcx),%r9b
     +0x7be: movzbl  -0x18(%rcx),%r10d
     +0x7c3: movzbl  -0x10(%rcx),%r11d
     +0x7c8: movzbl  -0xc(%rcx),%r12d
     +0x7cd: mov     $0x2,%sil
     +0x7d0: sub     -0x8(%rcx),%sil
     +0x7d4: movzbl  -0x4(%rcx),%edi
     +0x7d8: movzbl  (%rcx),%edx
     +0x7db: shl     $0x3,%r10b
     +0x7df: mov     $0x10,%r13b
     +0x7e2: sub     %r10b,%r13b
     +0x7e5: or      %r8b,%r13b
     +0x7e8: mov     %r9d,%r8d
     +0x7eb: shl     $0x6,%r8b
     +0x7ef: or      %r13b,%r8b
     +0x7f2: mov     %r8b,-0x2(%rbx,%rax,1)
     +0x7f7: shr     $0x2,%r9b
     +0x7fb: add     %r11b,%r11b
     +0x7fe: mov     $0x4,%r8b
     +0x801: sub     %r11b,%r8b
     +0x804: or      %r9b,%r8b
     +0x807: shl     $0x4,%r12b
     +0x80b: mov     $0x20,%r9b
     +0x80e: sub     %r12b,%r9b
     +0x811: mov     %esi,%r10d
     +0x814: shl     $0x7,%r10b
     +0x818: or      %r9b,%r10b
     +0x81b: or      %r8b,%r10b
     +0x81e: mov     %r10b,-0x1(%rbx,%rax,1)
     +0x823: shr     $1,%sil
     +0x826: shl     $0x2,%dil
     +0x82a: mov     $0x8,%r8b
     +0x82d: sub     %dil,%r8b
     +0x830: or      %sil,%r8b
     +0x833: shl     $0x5,%dl
     +0x836: mov     $0x40,%sil
     +0x839: sub     %dl,%sil
     +0x83c: or      %r8b,%sil
     +0x83f: mov     %sil,(%rbx,%rax,1)
     +0x843: add     $0x3,%rax
     +0x847: add     $0x20,%rcx
     +0x84b: cmp     $0x442,%rax
     +0x851: jne     <mldsa87_keypair_internal+0x7b0>
     +0x857: movq    $0x0,0x10(%rsp)
     +0x860: lea     0x10(%rsp),%rax
     +0x865: mov     $0x442,%eax
     +0x86a: lea     0xdfc(%rsp),%rcx
     +0x872: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x880: mov     $0x2,%r8b
     +0x883: sub     -0x1c(%rcx),%r8b
     +0x887: mov     $0x2,%r9b
     +0x88a: sub     -0x14(%rcx),%r9b
     +0x88e: movzbl  -0x18(%rcx),%r10d
     +0x893: movzbl  -0x10(%rcx),%r11d
     +0x898: movzbl  -0xc(%rcx),%r12d
     +0x89d: mov     $0x2,%sil
     +0x8a0: sub     -0x8(%rcx),%sil
     +0x8a4: movzbl  -0x4(%rcx),%edi
     +0x8a8: movzbl  (%rcx),%edx
     +0x8ab: shl     $0x3,%r10b
     +0x8af: mov     $0x10,%r13b
     +0x8b2: sub     %r10b,%r13b
     +0x8b5: or      %r8b,%r13b
     +0x8b8: mov     %r9d,%r8d
     +0x8bb: shl     $0x6,%r8b
     +0x8bf: or      %r13b,%r8b
     +0x8c2: mov     %r8b,-0x2(%rbx,%rax,1)
     +0x8c7: shr     $0x2,%r9b
     +0x8cb: add     %r11b,%r11b
     +0x8ce: mov     $0x4,%r8b
     +0x8d1: sub     %r11b,%r8b
     +0x8d4: or      %r9b,%r8b
     +0x8d7: shl     $0x4,%r12b
     +0x8db: mov     $0x20,%r9b
     +0x8de: sub     %r12b,%r9b
     +0x8e1: mov     %esi,%r10d
     +0x8e4: shl     $0x7,%r10b
     +0x8e8: or      %r9b,%r10b
     +0x8eb: or      %r8b,%r10b
     +0x8ee: mov     %r10b,-0x1(%rbx,%rax,1)
     +0x8f3: shr     $1,%sil
     +0x8f6: shl     $0x2,%dil
     +0x8fa: mov     $0x8,%r8b
     +0x8fd: sub     %dil,%r8b
     +0x900: or      %sil,%r8b
     +0x903: shl     $0x5,%dl
     +0x906: mov     $0x40,%sil
     +0x909: sub     %dl,%sil
     +0x90c: or      %r8b,%sil
     +0x90f: mov     %sil,(%rbx,%rax,1)
     +0x913: add     $0x3,%rax
     +0x917: add     $0x20,%rcx
     +0x91b: cmp     $0x4a2,%rax
     +0x921: jne     <mldsa87_keypair_internal+0x880>
     +0x927: movq    $0x0,0x10(%rsp)
     +0x930: lea     0x10(%rsp),%rax
     +0x935: lea     0x11e0(%rsp),%rdi
     +0x93d: lea     0x15e0(%rsp),%rsi
     +0x945: lea     0x19e0(%rsp),%rdx
     +0x94d: sub     $0x8,%rsp
     +0x951: lea     0x1e8(%rsp),%rcx
     +0x959: mov     %r15,%r8
     +0x95c: mov     $0x4,%r9d
     +0x962: push    $0xff
     +0x967: push    $0x6
     +0x969: push    $0x5
     +0x96b: call    <mldsa87_poly_uniform_eta_4x>
     +0x970: add     $0x20,%rsp
     +0x974: mov     $0x202,%eax
     +0x979: lea     0x11fc(%rsp),%rcx
     +0x981: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x990: mov     $0x2,%r8b
     +0x993: sub     -0x1c(%rcx),%r8b
     +0x997: mov     $0x2,%r9b
     +0x99a: sub     -0x14(%rcx),%r9b
     +0x99e: movzbl  -0x18(%rcx),%r10d
     +0x9a3: movzbl  -0x10(%rcx),%r11d
     +0x9a8: movzbl  -0xc(%rcx),%r13d
     +0x9ad: mov     $0x2,%sil
     +0x9b0: sub     -0x8(%rcx),%sil
     +0x9b4: movzbl  -0x4(%rcx),%edi
     +0x9b8: movzbl  (%rcx),%edx
     +0x9bb: shl     $0x3,%r10b
     +0x9bf: mov     $0x10,%r12b
     +0x9c2: sub     %r10b,%r12b
     +0x9c5: or      %r8b,%r12b
     +0x9c8: mov     %r9d,%r8d
     +0x9cb: shl     $0x6,%r8b
     +0x9cf: or      %r12b,%r8b
     +0x9d2: mov     %r8b,-0x2(%rbx,%rax,1)
     +0x9d7: shr     $0x2,%r9b
     +0x9db: add     %r11b,%r11b
     +0x9de: mov     $0x4,%r8b
     +0x9e1: sub     %r11b,%r8b
     +0x9e4: or      %r9b,%r8b
     +0x9e7: shl     $0x4,%r13b
     +0x9eb: mov     $0x20,%r9b
     +0x9ee: sub     %r13b,%r9b
     +0x9f1: mov     %esi,%r10d
     +0x9f4: shl     $0x7,%r10b
     +0x9f8: or      %r9b,%r10b
     +0x9fb: or      %r8b,%r10b
     +0x9fe: mov     %r10b,-0x1(%rbx,%rax,1)
     +0xa03: shr     $1,%sil
     +0xa06: shl     $0x2,%dil
     +0xa0a: mov     $0x8,%r8b
     +0xa0d: sub     %dil,%r8b
     +0xa10: or      %sil,%r8b
     +0xa13: shl     $0x5,%dl
     +0xa16: mov     $0x40,%sil
     +0xa19: sub     %dl,%sil
     +0xa1c: or      %r8b,%sil
     +0xa1f: mov     %sil,(%rbx,%rax,1)
     +0xa23: add     $0x3,%rax
     +0xa27: add     $0x20,%rcx
     +0xa2b: cmp     $0x262,%rax
     +0xa31: jne     <mldsa87_keypair_internal+0x990>
     +0xa37: movq    $0x0,0x10(%rsp)
     +0xa40: lea     0x10(%rsp),%rax
     +0xa45: mov     $0x262,%eax
     +0xa4a: lea     0x15fc(%rsp),%rcx
     +0xa52: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0xa60: mov     $0x2,%r8b
     +0xa63: sub     -0x1c(%rcx),%r8b
     +0xa67: mov     $0x2,%r9b
     +0xa6a: sub     -0x14(%rcx),%r9b
     +0xa6e: movzbl  -0x18(%rcx),%r10d
     +0xa73: movzbl  -0x10(%rcx),%r11d
     +0xa78: movzbl  -0xc(%rcx),%r12d
     +0xa7d: mov     $0x2,%sil
     +0xa80: sub     -0x8(%rcx),%sil
     +0xa84: movzbl  -0x4(%rcx),%edi
     +0xa88: movzbl  (%rcx),%edx
     +0xa8b: shl     $0x3,%r10b
     +0xa8f: mov     $0x10,%r13b
     +0xa92: sub     %r10b,%r13b
     +0xa95: or      %r8b,%r13b
     +0xa98: mov     %r9d,%r8d
     +0xa9b: shl     $0x6,%r8b
     +0xa9f: or      %r13b,%r8b
     +0xaa2: mov     %r8b,-0x2(%rbx,%rax,1)
     +0xaa7: shr     $0x2,%r9b
     +0xaab: add     %r11b,%r11b
     +0xaae: mov     $0x4,%r8b
     +0xab1: sub     %r11b,%r8b
     +0xab4: or      %r9b,%r8b
     +0xab7: shl     $0x4,%r12b
     +0xabb: mov     $0x20,%r9b
     +0xabe: sub     %r12b,%r9b
     +0xac1: mov     %esi,%r10d
     +0xac4: shl     $0x7,%r10b
     +0xac8: or      %r9b,%r10b
     +0xacb: or      %r8b,%r10b
     +0xace: mov     %r10b,-0x1(%rbx,%rax,1)
     +0xad3: shr     $1,%sil
     +0xad6: shl     $0x2,%dil
     +0xada: mov     $0x8,%r8b
     +0xadd: sub     %dil,%r8b
     +0xae0: or      %sil,%r8b
     +0xae3: shl     $0x5,%dl
     +0xae6: mov     $0x40,%sil
     +0xae9: sub     %dl,%sil
     +0xaec: or      %r8b,%sil
     +0xaef: mov     %sil,(%rbx,%rax,1)
     +0xaf3: add     $0x3,%rax
     +0xaf7: add     $0x20,%rcx
     +0xafb: cmp     $0x2c2,%rax
     +0xb01: jne     <mldsa87_keypair_internal+0xa60>
     +0xb07: movq    $0x0,0x10(%rsp)
     +0xb10: lea     0x10(%rsp),%rax
     +0xb15: mov     $0x2c2,%eax
     +0xb1a: lea     0x19fc(%rsp),%rcx
     +0xb22: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0xb30: mov     $0x2,%r8b
     +0xb33: sub     -0x1c(%rcx),%r8b
     +0xb37: mov     $0x2,%r9b
     +0xb3a: sub     -0x14(%rcx),%r9b
     +0xb3e: movzbl  -0x18(%rcx),%r10d
     +0xb43: movzbl  -0x10(%rcx),%r11d
     +0xb48: movzbl  -0xc(%rcx),%r12d
     +0xb4d: mov     $0x2,%sil
     +0xb50: sub     -0x8(%rcx),%sil
     +0xb54: movzbl  -0x4(%rcx),%edi
     +0xb58: movzbl  (%rcx),%edx
     +0xb5b: shl     $0x3,%r10b
     +0xb5f: mov     $0x10,%r13b
     +0xb62: sub     %r10b,%r13b
     +0xb65: or      %r8b,%r13b
     +0xb68: mov     %r9d,%r8d
     +0xb6b: shl     $0x6,%r8b
     +0xb6f: or      %r13b,%r8b
     +0xb72: mov     %r8b,-0x2(%rbx,%rax,1)
     +0xb77: shr     $0x2,%r9b
     +0xb7b: add     %r11b,%r11b
     +0xb7e: mov     $0x4,%r8b
     +0xb81: sub     %r11b,%r8b
     +0xb84: or      %r9b,%r8b
     +0xb87: shl     $0x4,%r12b
     +0xb8b: mov     $0x20,%r9b
     +0xb8e: sub     %r12b,%r9b
     +0xb91: mov     %esi,%r10d
     +0xb94: shl     $0x7,%r10b
     +0xb98: or      %r9b,%r10b
     +0xb9b: or      %r8b,%r10b
     +0xb9e: mov     %r10b,-0x1(%rbx,%rax,1)
     +0xba3: shr     $1,%sil
     +0xba6: shl     $0x2,%dil
     +0xbaa: mov     $0x8,%r8b
     +0xbad: sub     %dil,%r8b
     +0xbb0: or      %sil,%r8b
     +0xbb3: shl     $0x5,%dl
     +0xbb6: mov     $0x40,%sil
     +0xbb9: sub     %dl,%sil
     +0xbbc: or      %r8b,%sil
     +0xbbf: mov     %sil,(%rbx,%rax,1)
     +0xbc3: add     $0x3,%rax
     +0xbc7: add     $0x20,%rcx
     +0xbcb: cmp     $0x322,%rax
     +0xbd1: jne     <mldsa87_keypair_internal+0xb30>
     +0xbd7: movq    $0x0,0x10(%rsp)
     +0xbe0: lea     0x10(%rsp),%rax
     +0xbe5: sub     $0x8,%rsp
     +0xbe9: lea     0x1e8(%rsp),%rdi
     +0xbf1: lea     0x5e8(%rsp),%rsi
     +0xbf9: lea     0x9e8(%rsp),%rdx
     +0xc01: lea     0xde8(%rsp),%rcx
     +0xc09: mov     %r15,%r8
     +0xc0c: xor     %r9d,%r9d
     +0xc0f: push    $0x3
     +0xc11: push    $0x2
     +0xc13: push    $0x1
     +0xc15: call    <mldsa87_poly_uniform_eta_4x>
     +0xc1a: add     $0x20,%rsp
     +0xc1e: mov     $0x82,%eax
     +0xc23: lea     0x1fc(%rsp),%rcx
     +0xc2b: nopl    0x0(%rax,%rax,1)
     +0xc30: mov     $0x2,%r8b
     +0xc33: sub     -0x1c(%rcx),%r8b
     +0xc37: mov     $0x2,%r9b
     +0xc3a: sub     -0x14(%rcx),%r9b
     +0xc3e: movzbl  -0x18(%rcx),%r10d
     +0xc43: movzbl  -0x10(%rcx),%r11d
     +0xc48: movzbl  -0xc(%rcx),%r15d
     +0xc4d: mov     $0x2,%sil
     +0xc50: sub     -0x8(%rcx),%sil
     +0xc54: movzbl  -0x4(%rcx),%edi
     +0xc58: movzbl  (%rcx),%edx
     +0xc5b: shl     $0x3,%r10b
     +0xc5f: mov     $0x10,%r12b
     +0xc62: sub     %r10b,%r12b
     +0xc65: or      %r8b,%r12b
     +0xc68: mov     %r9d,%r8d
     +0xc6b: shl     $0x6,%r8b
     +0xc6f: or      %r12b,%r8b
     +0xc72: mov     %r8b,-0x2(%rbx,%rax,1)
     +0xc77: shr     $0x2,%r9b
     +0xc7b: add     %r11b,%r11b
     +0xc7e: mov     $0x4,%r8b
     +0xc81: sub     %r11b,%r8b
     +0xc84: or      %r9b,%r8b
     +0xc87: shl     $0x4,%r15b
     +0xc8b: mov     $0x20,%r9b
     +0xc8e: sub     %r15b,%r9b
     +0xc91: mov     %esi,%r10d
     +0xc94: shl     $0x7,%r10b
     +0xc98: or      %r9b,%r10b
     +0xc9b: or      %r8b,%r10b
     +0xc9e: mov     %r10b,-0x1(%rbx,%rax,1)
     +0xca3: shr     $1,%sil
     +0xca6: shl     $0x2,%dil
     +0xcaa: mov     $0x8,%r8b
     +0xcad: sub     %dil,%r8b
     +0xcb0: or      %sil,%r8b
     +0xcb3: shl     $0x5,%dl
     +0xcb6: mov     $0x40,%sil
     +0xcb9: sub     %dl,%sil
     +0xcbc: or      %r8b,%sil
     +0xcbf: mov     %sil,(%rbx,%rax,1)
     +0xcc3: add     $0x3,%rax
     +0xcc7: add     $0x20,%rcx
     +0xccb: cmp     $0xe2,%rax
     +0xcd1: jne     <mldsa87_keypair_internal+0xc30>
     +0xcd7: movq    $0x0,0x10(%rsp)
     +0xce0: lea     0x10(%rsp),%rax
     +0xce5: mov     $0xe2,%eax
     +0xcea: lea     0x5fc(%rsp),%rcx
     +0xcf2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0xd00: mov     $0x2,%r8b
     +0xd03: sub     -0x1c(%rcx),%r8b
     +0xd07: mov     $0x2,%r9b
     +0xd0a: sub     -0x14(%rcx),%r9b
     +0xd0e: movzbl  -0x18(%rcx),%r10d
     +0xd13: movzbl  -0x10(%rcx),%r11d
     +0xd18: movzbl  -0xc(%rcx),%r15d
     +0xd1d: mov     $0x2,%sil
     +0xd20: sub     -0x8(%rcx),%sil
     +0xd24: movzbl  -0x4(%rcx),%edi
     +0xd28: movzbl  (%rcx),%edx
     +0xd2b: shl     $0x3,%r10b
     +0xd2f: mov     $0x10,%r12b
     +0xd32: sub     %r10b,%r12b
     +0xd35: or      %r8b,%r12b
     +0xd38: mov     %r9d,%r8d
     +0xd3b: shl     $0x6,%r8b
     +0xd3f: or      %r12b,%r8b
     +0xd42: mov     %r8b,-0x2(%rbx,%rax,1)
     +0xd47: shr     $0x2,%r9b
     +0xd4b: add     %r11b,%r11b
     +0xd4e: mov     $0x4,%r8b
     +0xd51: sub     %r11b,%r8b
     +0xd54: or      %r9b,%r8b
     +0xd57: shl     $0x4,%r15b
     +0xd5b: mov     $0x20,%r9b
     +0xd5e: sub     %r15b,%r9b
     +0xd61: mov     %esi,%r10d
     +0xd64: shl     $0x7,%r10b
     +0xd68: or      %r9b,%r10b
     +0xd6b: or      %r8b,%r10b
     +0xd6e: mov     %r10b,-0x1(%rbx,%rax,1)
     +0xd73: shr     $1,%sil
     +0xd76: shl     $0x2,%dil
     +0xd7a: mov     $0x8,%r8b
     +0xd7d: sub     %dil,%r8b
     +0xd80: or      %sil,%r8b
     +0xd83: shl     $0x5,%dl
     +0xd86: mov     $0x40,%sil
     +0xd89: sub     %dl,%sil
     +0xd8c: or      %r8b,%sil
     +0xd8f: mov     %sil,(%rbx,%rax,1)
     +0xd93: add     $0x3,%rax
     +0xd97: add     $0x20,%rcx
     +0xd9b: cmp     $0x142,%rax
     +0xda1: jne     <mldsa87_keypair_internal+0xd00>
     +0xda7: movq    $0x0,0x10(%rsp)
     +0xdb0: lea     0x10(%rsp),%rax
     +0xdb5: mov     $0x142,%eax
     +0xdba: lea     0x9fc(%rsp),%rcx
     +0xdc2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0xdd0: mov     $0x2,%r8b
     +0xdd3: sub     -0x1c(%rcx),%r8b
     +0xdd7: mov     $0x2,%r9b
     +0xdda: sub     -0x14(%rcx),%r9b
     +0xdde: movzbl  -0x18(%rcx),%r10d
     +0xde3: movzbl  -0x10(%rcx),%r11d
     +0xde8: movzbl  -0xc(%rcx),%r15d
     +0xded: mov     $0x2,%sil
     +0xdf0: sub     -0x8(%rcx),%sil
     +0xdf4: movzbl  -0x4(%rcx),%edi
     +0xdf8: movzbl  (%rcx),%edx
     +0xdfb: shl     $0x3,%r10b
     +0xdff: mov     $0x10,%r12b
     +0xe02: sub     %r10b,%r12b
     +0xe05: or      %r8b,%r12b
     +0xe08: mov     %r9d,%r8d
     +0xe0b: shl     $0x6,%r8b
     +0xe0f: or      %r12b,%r8b
     +0xe12: mov     %r8b,-0x2(%rbx,%rax,1)
     +0xe17: shr     $0x2,%r9b
     +0xe1b: add     %r11b,%r11b
     +0xe1e: mov     $0x4,%r8b
     +0xe21: sub     %r11b,%r8b
     +0xe24: or      %r9b,%r8b
     +0xe27: shl     $0x4,%r15b
     +0xe2b: mov     $0x20,%r9b
     +0xe2e: sub     %r15b,%r9b
     +0xe31: mov     %esi,%r10d
     +0xe34: shl     $0x7,%r10b
     +0xe38: or      %r9b,%r10b
     +0xe3b: or      %r8b,%r10b
     +0xe3e: mov     %r10b,-0x1(%rbx,%rax,1)
     +0xe43: shr     $1,%sil
     +0xe46: shl     $0x2,%dil
     +0xe4a: mov     $0x8,%r8b
     +0xe4d: sub     %dil,%r8b
     +0xe50: or      %sil,%r8b
     +0xe53: shl     $0x5,%dl
     +0xe56: mov     $0x40,%sil
     +0xe59: sub     %dl,%sil
     +0xe5c: or      %r8b,%sil
     +0xe5f: mov     %sil,(%rbx,%rax,1)
     +0xe63: add     $0x3,%rax
     +0xe67: add     $0x20,%rcx
     +0xe6b: cmp     $0x1a2,%rax
     +0xe71: jne     <mldsa87_keypair_internal+0xdd0>
     +0xe77: movq    $0x0,0x10(%rsp)
     +0xe80: lea     0x10(%rsp),%rax
     +0xe85: mov     $0x1a2,%eax
     +0xe8a: lea     0xdfc(%rsp),%rcx
     +0xe92: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0xea0: mov     $0x2,%r8b
     +0xea3: sub     -0x1c(%rcx),%r8b
     +0xea7: mov     $0x2,%r9b
     +0xeaa: sub     -0x14(%rcx),%r9b
     +0xeae: movzbl  -0x18(%rcx),%r10d
     +0xeb3: movzbl  -0x10(%rcx),%r11d
     +0xeb8: movzbl  -0xc(%rcx),%r15d
     +0xebd: mov     $0x2,%sil
     +0xec0: sub     -0x8(%rcx),%sil
     +0xec4: movzbl  -0x4(%rcx),%edi
     +0xec8: movzbl  (%rcx),%edx
     +0xecb: shl     $0x3,%r10b
     +0xecf: mov     $0x10,%r12b
     +0xed2: sub     %r10b,%r12b
     +0xed5: or      %r8b,%r12b
     +0xed8: mov     %r9d,%r8d
     +0xedb: shl     $0x6,%r8b
     +0xedf: or      %r12b,%r8b
     +0xee2: mov     %r8b,-0x2(%rbx,%rax,1)
     +0xee7: shr     $0x2,%r9b
     +0xeeb: add     %r11b,%r11b
     +0xeee: mov     $0x4,%r8b
     +0xef1: sub     %r11b,%r8b
     +0xef4: or      %r9b,%r8b
     +0xef7: shl     $0x4,%r15b
     +0xefb: mov     $0x20,%r9b
     +0xefe: sub     %r15b,%r9b
     +0xf01: mov     %esi,%r10d
     +0xf04: shl     $0x7,%r10b
     +0xf08: or      %r9b,%r10b
     +0xf0b: or      %r8b,%r10b
     +0xf0e: mov     %r10b,-0x1(%rbx,%rax,1)
     +0xf13: shr     $1,%sil
     +0xf16: shl     $0x2,%dil
     +0xf1a: mov     $0x8,%r8b
     +0xf1d: sub     %dil,%r8b
     +0xf20: or      %sil,%r8b
     +0xf23: shl     $0x5,%dl
     +0xf26: mov     $0x40,%sil
     +0xf29: sub     %dl,%sil
     +0xf2c: or      %r8b,%sil
     +0xf2f: mov     %sil,(%rbx,%rax,1)
     +0xf33: add     $0x3,%rax
     +0xf37: add     $0x20,%rcx
     +0xf3b: cmp     $0x202,%rax
     +0xf41: jne     <mldsa87_keypair_internal+0xea0>
     +0xf47: movq    $0x0,0x10(%rsp)
     +0xf50: lea     0x10(%rsp),%rax
     +0xf55: lea     0x1e0(%rsp),%r15
     +0xf5d: mov     %r15,%rdi
     +0xf60: call    <mldsa_poly_ntt>
     +0xf65: lea     0x5e0(%rsp),%rdi
     +0xf6d: call    <mldsa_poly_ntt>
     +0xf72: lea     0x9e0(%rsp),%rdi
     +0xf7a: call    <mldsa_poly_ntt>
     +0xf7f: lea     0xde0(%rsp),%rdi
     +0xf87: call    <mldsa_poly_ntt>
     +0xf8c: lea     0x11e0(%rsp),%rdi
     +0xf94: call    <mldsa_poly_ntt>
     +0xf99: lea     0x15e0(%rsp),%rdi
     +0xfa1: call    <mldsa_poly_ntt>
     +0xfa6: lea     0x19e0(%rsp),%rdi
     +0xfae: call    <mldsa_poly_ntt>
     +0xfb3: movaps  0x160(%rsp),%xmm0
     +0xfbb: movaps  0x170(%rsp),%xmm1
     +0xfc3: movups  %xmm1,0x10(%r14)
     +0xfc8: movups  %xmm0,(%r14)
     +0xfcc: lea     0x20(%r14),%rdi
     +0xfd0: lea     0x620(%rbx),%rsi
     +0xfd7: lea     0x160(%rsp),%r12
     +0xfdf: mov     %r15,%rdx
     +0xfe2: lea     0x320(%rbx),%rcx
     +0xfe9: mov     %r12,%r8
     +0xfec: call    <mld_compute_pack_t0_t187>
     +0xff1: xorps   %xmm0,%xmm0
     +0xff4: movups  %xmm0,0xcc(%rsp)
     +0xffc: movaps  %xmm0,0xc0(%rsp)
    +0x1004: movaps  %xmm0,0xb0(%rsp)
    +0x100c: movaps  %xmm0,0xa0(%rsp)
    +0x1014: movaps  %xmm0,0x90(%rsp)
    +0x101c: movaps  %xmm0,0x80(%rsp)
    +0x1024: movaps  %xmm0,0x70(%rsp)
    +0x1029: movaps  %xmm0,0x60(%rsp)
    +0x102e: movaps  %xmm0,0x50(%rsp)
    +0x1033: movaps  %xmm0,0x40(%rsp)
    +0x1038: movaps  %xmm0,0x30(%rsp)
    +0x103d: movaps  %xmm0,0x20(%rsp)
    +0x1042: movaps  %xmm0,0x10(%rsp)
    +0x1047: movups  (%r14),%xmm0
    +0x104b: movups  0x10(%r14),%xmm1
    +0x1050: movaps  %xmm0,0x10(%rsp)
    +0x1055: movaps  %xmm1,0x20(%rsp)
    +0x105a: movups  0x20(%r14),%xmm0
    +0x105f: movups  0x30(%r14),%xmm1
    +0x1064: movaps  %xmm0,0x30(%rsp)
    +0x1069: movaps  %xmm1,0x40(%rsp)
    +0x106e: movups  0x40(%r14),%xmm0
    +0x1073: movups  0x50(%r14),%xmm1
    +0x1078: xorps   0x50(%rsp),%xmm0
    +0x107d: xorps   0x60(%rsp),%xmm1
    +0x1082: movaps  %xmm0,0x50(%rsp)
    +0x1087: movaps  %xmm1,0x60(%rsp)
    +0x108c: movups  0x60(%r14),%xmm0
    +0x1091: movups  0x70(%r14),%xmm1
    +0x1096: xorps   0x70(%rsp),%xmm0
    +0x109b: xorps   0x80(%rsp),%xmm1
    +0x10a3: movaps  %xmm0,0x70(%rsp)
    +0x10a8: movaps  %xmm1,0x80(%rsp)
    +0x10b0: mov     0x80(%r14),%rax
    +0x10b7: xor     %rax,0x90(%rsp)
    +0x10bf: lea     0x10(%rsp),%r13
    +0x10c4: mov     %r13,%rdi
    +0x10c7: call    <mldsa_keccakf1600_permute>
    +0x10cc: movups  0x88(%r14),%xmm0
    +0x10d4: movups  0x98(%r14),%xmm1
    +0x10dc: xorps   0x10(%rsp),%xmm0
    +0x10e1: xorps   0x20(%rsp),%xmm1
    +0x10e6: movaps  %xmm0,0x10(%rsp)
    +0x10eb: movaps  %xmm1,0x20(%rsp)
    +0x10f0: movups  0xa8(%r14),%xmm0
    +0x10f8: movups  0xb8(%r14),%xmm1
    +0x1100: xorps   0x30(%rsp),%xmm0
    +0x1105: xorps   0x40(%rsp),%xmm1
    +0x110a: movaps  %xmm0,0x30(%rsp)
    +0x110f: movaps  %xmm1,0x40(%rsp)
    +0x1114: movups  0xc8(%r14),%xmm0
    +0x111c: movups  0xd8(%r14),%xmm1
    +0x1124: xorps   0x50(%rsp),%xmm0
    +0x1129: xorps   0x60(%rsp),%xmm1
    +0x112e: movaps  %xmm0,0x50(%rsp)
    +0x1133: movaps  %xmm1,0x60(%rsp)
    +0x1138: movups  0xe8(%r14),%xmm0
    +0x1140: movups  0xf8(%r14),%xmm1
    +0x1148: xorps   0x70(%rsp),%xmm0
    +0x114d: xorps   0x80(%rsp),%xmm1
    +0x1155: movaps  %xmm0,0x70(%rsp)
    +0x115a: movaps  %xmm1,0x80(%rsp)
    +0x1162: mov     0x108(%r14),%rax
    +0x1169: xor     %rax,0x90(%rsp)
    +0x1171: mov     %r13,%rdi
    +0x1174: call    <mldsa_keccakf1600_permute>
    +0x1179: movups  0x110(%r14),%xmm0
    +0x1181: movups  0x120(%r14),%xmm1
    +0x1189: xorps   0x10(%rsp),%xmm0
    +0x118e: xorps   0x20(%rsp),%xmm1
    +0x1193: movaps  %xmm0,0x10(%rsp)
    +0x1198: movaps  %xmm1,0x20(%rsp)
    +0x119d: movups  0x130(%r14),%xmm0
    +0x11a5: movups  0x140(%r14),%xmm1
    +0x11ad: xorps   0x30(%rsp),%xmm0
    +0x11b2: xorps   0x40(%rsp),%xmm1
    +0x11b7: movaps  %xmm0,0x30(%rsp)
    +0x11bc: movaps  %xmm1,0x40(%rsp)
    +0x11c1: movups  0x150(%r14),%xmm0
    +0x11c9: movups  0x160(%r14),%xmm1
    +0x11d1: xorps   0x50(%rsp),%xmm0
    +0x11d6: xorps   0x60(%rsp),%xmm1
    +0x11db: movaps  %xmm0,0x50(%rsp)
    +0x11e0: movaps  %xmm1,0x60(%rsp)
    +0x11e5: movups  0x170(%r14),%xmm0
    +0x11ed: movups  0x180(%r14),%xmm1
    +0x11f5: xorps   0x70(%rsp),%xmm0
    +0x11fa: xorps   0x80(%rsp),%xmm1
    +0x1202: movaps  %xmm0,0x70(%rsp)
    +0x1207: movaps  %xmm1,0x80(%rsp)
    +0x120f: mov     0x190(%r14),%rax
    +0x1216: xor     %rax,0x90(%rsp)
    +0x121e: mov     %r13,%rdi
    +0x1221: call    <mldsa_keccakf1600_permute>
    +0x1226: movups  0x198(%r14),%xmm0
    +0x122e: movups  0x1a8(%r14),%xmm1
    +0x1236: xorps   0x10(%rsp),%xmm0
    +0x123b: xorps   0x20(%rsp),%xmm1
    +0x1240: movaps  %xmm0,0x10(%rsp)
    +0x1245: movaps  %xmm1,0x20(%rsp)
    +0x124a: movups  0x1b8(%r14),%xmm0
    +0x1252: movups  0x1c8(%r14),%xmm1
    +0x125a: xorps   0x30(%rsp),%xmm0
    +0x125f: xorps   0x40(%rsp),%xmm1
    +0x1264: movaps  %xmm0,0x30(%rsp)
    +0x1269: movaps  %xmm1,0x40(%rsp)
    +0x126e: movups  0x1d8(%r14),%xmm0
    +0x1276: movups  0x1e8(%r14),%xmm1
    +0x127e: xorps   0x50(%rsp),%xmm0
    +0x1283: xorps   0x60(%rsp),%xmm1
    +0x1288: movaps  %xmm0,0x50(%rsp)
    +0x128d: movaps  %xmm1,0x60(%rsp)
    +0x1292: movups  0x1f8(%r14),%xmm0
    +0x129a: movups  0x208(%r14),%xmm1
    +0x12a2: xorps   0x70(%rsp),%xmm0
    +0x12a7: xorps   0x80(%rsp),%xmm1
    +0x12af: movaps  %xmm0,0x70(%rsp)
    +0x12b4: movaps  %xmm1,0x80(%rsp)
    +0x12bc: mov     0x218(%r14),%rax
    +0x12c3: xor     %rax,0x90(%rsp)
    +0x12cb: mov     %r13,%rdi
    +0x12ce: call    <mldsa_keccakf1600_permute>
    +0x12d3: movups  0x220(%r14),%xmm0
    +0x12db: movups  0x230(%r14),%xmm1
    +0x12e3: xorps   0x10(%rsp),%xmm0
    +0x12e8: xorps   0x20(%rsp),%xmm1
    +0x12ed: movaps  %xmm0,0x10(%rsp)
    +0x12f2: movaps  %xmm1,0x20(%rsp)
    +0x12f7: movups  0x240(%r14),%xmm0
    +0x12ff: movups  0x250(%r14),%xmm1
    +0x1307: xorps   0x30(%rsp),%xmm0
    +0x130c: xorps   0x40(%rsp),%xmm1
    +0x1311: movaps  %xmm0,0x30(%rsp)
    +0x1316: movaps  %xmm1,0x40(%rsp)
    +0x131b: movups  0x260(%r14),%xmm0
    +0x1323: movups  0x270(%r14),%xmm1
    +0x132b: xorps   0x50(%rsp),%xmm0
    +0x1330: xorps   0x60(%rsp),%xmm1
    +0x1335: movaps  %xmm0,0x50(%rsp)
    +0x133a: movaps  %xmm1,0x60(%rsp)
    +0x133f: movups  0x280(%r14),%xmm0
    +0x1347: movups  0x290(%r14),%xmm1
    +0x134f: xorps   0x70(%rsp),%xmm0
    +0x1354: xorps   0x80(%rsp),%xmm1
    +0x135c: movaps  %xmm0,0x70(%rsp)
    +0x1361: movaps  %xmm1,0x80(%rsp)
    +0x1369: mov     0x2a0(%r14),%rax
    +0x1370: xor     %rax,0x90(%rsp)
    +0x1378: mov     %r13,%rdi
    +0x137b: call    <mldsa_keccakf1600_permute>
    +0x1380: movups  0x2a8(%r14),%xmm0
    +0x1388: movups  0x2b8(%r14),%xmm1
    +0x1390: xorps   0x10(%rsp),%xmm0
    +0x1395: xorps   0x20(%rsp),%xmm1
    +0x139a: movaps  %xmm0,0x10(%rsp)
    +0x139f: movaps  %xmm1,0x20(%rsp)
    +0x13a4: movups  0x2c8(%r14),%xmm0
    +0x13ac: movups  0x2d8(%r14),%xmm1
    +0x13b4: xorps   0x30(%rsp),%xmm0
    +0x13b9: xorps   0x40(%rsp),%xmm1
    +0x13be: movaps  %xmm0,0x30(%rsp)
    +0x13c3: movaps  %xmm1,0x40(%rsp)
    +0x13c8: movups  0x2e8(%r14),%xmm0
    +0x13d0: movups  0x2f8(%r14),%xmm1
    +0x13d8: xorps   0x50(%rsp),%xmm0
    +0x13dd: xorps   0x60(%rsp),%xmm1
    +0x13e2: movaps  %xmm0,0x50(%rsp)
    +0x13e7: movaps  %xmm1,0x60(%rsp)
    +0x13ec: movups  0x308(%r14),%xmm0
    +0x13f4: movups  0x318(%r14),%xmm1
    +0x13fc: xorps   0x70(%rsp),%xmm0
    +0x1401: xorps   0x80(%rsp),%xmm1
    +0x1409: movaps  %xmm0,0x70(%rsp)
    +0x140e: movaps  %xmm1,0x80(%rsp)
    +0x1416: mov     0x328(%r14),%rax
    +0x141d: xor     %rax,0x90(%rsp)
    +0x1425: mov     %r13,%rdi
    +0x1428: call    <mldsa_keccakf1600_permute>
    +0x142d: movups  0x330(%r14),%xmm0
    +0x1435: movups  0x340(%r14),%xmm1
    +0x143d: xorps   0x10(%rsp),%xmm0
    +0x1442: xorps   0x20(%rsp),%xmm1
    +0x1447: movaps  %xmm0,0x10(%rsp)
    +0x144c: movaps  %xmm1,0x20(%rsp)
    +0x1451: movups  0x350(%r14),%xmm0
    +0x1459: movups  0x360(%r14),%xmm1
    +0x1461: xorps   0x30(%rsp),%xmm0
    +0x1466: xorps   0x40(%rsp),%xmm1
    +0x146b: movaps  %xmm0,0x30(%rsp)
    +0x1470: movaps  %xmm1,0x40(%rsp)
    +0x1475: movups  0x370(%r14),%xmm0
    +0x147d: movups  0x380(%r14),%xmm1
    +0x1485: xorps   0x50(%rsp),%xmm0
    +0x148a: xorps   0x60(%rsp),%xmm1
    +0x148f: movaps  %xmm0,0x50(%rsp)
    +0x1494: movaps  %xmm1,0x60(%rsp)
    +0x1499: movups  0x390(%r14),%xmm0
    +0x14a1: movups  0x3a0(%r14),%xmm1
    +0x14a9: xorps   0x70(%rsp),%xmm0
    +0x14ae: xorps   0x80(%rsp),%xmm1
    +0x14b6: movaps  %xmm0,0x70(%rsp)
    +0x14bb: movaps  %xmm1,0x80(%rsp)
    +0x14c3: mov     0x3b0(%r14),%rax
    +0x14ca: xor     %rax,0x90(%rsp)
    +0x14d2: mov     %r13,%rdi
    +0x14d5: call    <mldsa_keccakf1600_permute>
    +0x14da: movups  0x3b8(%r14),%xmm0
    +0x14e2: movups  0x3c8(%r14),%xmm1
    +0x14ea: xorps   0x10(%rsp),%xmm0
    +0x14ef: xorps   0x20(%rsp),%xmm1
    +0x14f4: movaps  %xmm0,0x10(%rsp)
    +0x14f9: movaps  %xmm1,0x20(%rsp)
    +0x14fe: movups  0x3d8(%r14),%xmm0
    +0x1506: movups  0x3e8(%r14),%xmm1
    +0x150e: xorps   0x30(%rsp),%xmm0
    +0x1513: xorps   0x40(%rsp),%xmm1
    +0x1518: movaps  %xmm0,0x30(%rsp)
    +0x151d: movaps  %xmm1,0x40(%rsp)
    +0x1522: movups  0x3f8(%r14),%xmm0
    +0x152a: movups  0x408(%r14),%xmm1
    +0x1532: xorps   0x50(%rsp),%xmm0
    +0x1537: xorps   0x60(%rsp),%xmm1
    +0x153c: movaps  %xmm0,0x50(%rsp)
    +0x1541: movaps  %xmm1,0x60(%rsp)
    +0x1546: movups  0x418(%r14),%xmm0
    +0x154e: movups  0x428(%r14),%xmm1
    +0x1556: xorps   0x70(%rsp),%xmm0
    +0x155b: xorps   0x80(%rsp),%xmm1
    +0x1563: movaps  %xmm0,0x70(%rsp)
    +0x1568: movaps  %xmm1,0x80(%rsp)
    +0x1570: mov     0x438(%r14),%rax
    +0x1577: xor     %rax,0x90(%rsp)
    +0x157f: mov     %r13,%rdi
    +0x1582: call    <mldsa_keccakf1600_permute>
    +0x1587: movups  0x440(%r14),%xmm0
    +0x158f: movups  0x450(%r14),%xmm1
    +0x1597: xorps   0x10(%rsp),%xmm0
    +0x159c: xorps   0x20(%rsp),%xmm1
    +0x15a1: movaps  %xmm0,0x10(%rsp)
    +0x15a6: movaps  %xmm1,0x20(%rsp)
    +0x15ab: movups  0x460(%r14),%xmm0
    +0x15b3: movups  0x470(%r14),%xmm1
    +0x15bb: xorps   0x30(%rsp),%xmm0
    +0x15c0: xorps   0x40(%rsp),%xmm1
    +0x15c5: movaps  %xmm0,0x30(%rsp)
    +0x15ca: movaps  %xmm1,0x40(%rsp)
    +0x15cf: movups  0x480(%r14),%xmm0
    +0x15d7: movups  0x490(%r14),%xmm1
    +0x15df: xorps   0x50(%rsp),%xmm0
    +0x15e4: xorps   0x60(%rsp),%xmm1
    +0x15e9: movaps  %xmm0,0x50(%rsp)
    +0x15ee: movaps  %xmm1,0x60(%rsp)
    +0x15f3: movups  0x4a0(%r14),%xmm0
    +0x15fb: movups  0x4b0(%r14),%xmm1
    +0x1603: xorps   0x70(%rsp),%xmm0
    +0x1608: xorps   0x80(%rsp),%xmm1
    +0x1610: movaps  %xmm0,0x70(%rsp)
    +0x1615: movaps  %xmm1,0x80(%rsp)
    +0x161d: mov     0x4c0(%r14),%rax
    +0x1624: xor     %rax,0x90(%rsp)
    +0x162c: mov     %r13,%rdi
    +0x162f: call    <mldsa_keccakf1600_permute>
    +0x1634: movups  0x4c8(%r14),%xmm0
    +0x163c: movups  0x4d8(%r14),%xmm1
    +0x1644: xorps   0x10(%rsp),%xmm0
    +0x1649: xorps   0x20(%rsp),%xmm1
    +0x164e: movaps  %xmm0,0x10(%rsp)
    +0x1653: movaps  %xmm1,0x20(%rsp)
    +0x1658: movups  0x4e8(%r14),%xmm0
    +0x1660: movups  0x4f8(%r14),%xmm1
    +0x1668: xorps   0x30(%rsp),%xmm0
    +0x166d: xorps   0x40(%rsp),%xmm1
    +0x1672: movaps  %xmm0,0x30(%rsp)
    +0x1677: movaps  %xmm1,0x40(%rsp)
    +0x167c: movups  0x508(%r14),%xmm0
    +0x1684: movups  0x518(%r14),%xmm1
    +0x168c: xorps   0x50(%rsp),%xmm0
    +0x1691: xorps   0x60(%rsp),%xmm1
    +0x1696: movaps  %xmm0,0x50(%rsp)
    +0x169b: movaps  %xmm1,0x60(%rsp)
    +0x16a0: movups  0x528(%r14),%xmm0
    +0x16a8: movups  0x538(%r14),%xmm1
    +0x16b0: xorps   0x70(%rsp),%xmm0
    +0x16b5: xorps   0x80(%rsp),%xmm1
    +0x16bd: movaps  %xmm0,0x70(%rsp)
    +0x16c2: movaps  %xmm1,0x80(%rsp)
    +0x16ca: mov     0x548(%r14),%rax
    +0x16d1: xor     %rax,0x90(%rsp)
    +0x16d9: mov     %r13,%rdi
    +0x16dc: call    <mldsa_keccakf1600_permute>
    +0x16e1: movups  0x550(%r14),%xmm0
    +0x16e9: movups  0x560(%r14),%xmm1
    +0x16f1: xorps   0x10(%rsp),%xmm0
    +0x16f6: xorps   0x20(%rsp),%xmm1
    +0x16fb: movaps  %xmm0,0x10(%rsp)
    +0x1700: movaps  %xmm1,0x20(%rsp)
    +0x1705: movups  0x570(%r14),%xmm0
    +0x170d: movups  0x580(%r14),%xmm1
    +0x1715: xorps   0x30(%rsp),%xmm0
    +0x171a: xorps   0x40(%rsp),%xmm1
    +0x171f: movaps  %xmm0,0x30(%rsp)
    +0x1724: movaps  %xmm1,0x40(%rsp)
    +0x1729: movups  0x590(%r14),%xmm0
    +0x1731: movups  0x5a0(%r14),%xmm1
    +0x1739: xorps   0x50(%rsp),%xmm0
    +0x173e: xorps   0x60(%rsp),%xmm1
    +0x1743: movaps  %xmm0,0x50(%rsp)
    +0x1748: movaps  %xmm1,0x60(%rsp)
    +0x174d: movups  0x5b0(%r14),%xmm0
    +0x1755: movups  0x5c0(%r14),%xmm1
    +0x175d: xorps   0x70(%rsp),%xmm0
    +0x1762: xorps   0x80(%rsp),%xmm1
    +0x176a: movaps  %xmm0,0x70(%rsp)
    +0x176f: movaps  %xmm1,0x80(%rsp)
    +0x1777: mov     0x5d0(%r14),%rax
    +0x177e: xor     %rax,0x90(%rsp)
    +0x1786: mov     %r13,%rdi
    +0x1789: call    <mldsa_keccakf1600_permute>
    +0x178e: movups  0x5d8(%r14),%xmm0
    +0x1796: movups  0x5e8(%r14),%xmm1
    +0x179e: xorps   0x10(%rsp),%xmm0
    +0x17a3: xorps   0x20(%rsp),%xmm1
    +0x17a8: movaps  %xmm0,0x10(%rsp)
    +0x17ad: movaps  %xmm1,0x20(%rsp)
    +0x17b2: movups  0x5f8(%r14),%xmm0
    +0x17ba: movups  0x608(%r14),%xmm1
    +0x17c2: xorps   0x30(%rsp),%xmm0
    +0x17c7: xorps   0x40(%rsp),%xmm1
    +0x17cc: movaps  %xmm0,0x30(%rsp)
    +0x17d1: movaps  %xmm1,0x40(%rsp)
    +0x17d6: movups  0x618(%r14),%xmm0
    +0x17de: movups  0x628(%r14),%xmm1
    +0x17e6: xorps   0x50(%rsp),%xmm0
    +0x17eb: xorps   0x60(%rsp),%xmm1
    +0x17f0: movaps  %xmm0,0x50(%rsp)
    +0x17f5: movaps  %xmm1,0x60(%rsp)
    +0x17fa: movups  0x638(%r14),%xmm0
    +0x1802: movups  0x648(%r14),%xmm1
    +0x180a: xorps   0x70(%rsp),%xmm0
    +0x180f: xorps   0x80(%rsp),%xmm1
    +0x1817: movaps  %xmm0,0x70(%rsp)
    +0x181c: movaps  %xmm1,0x80(%rsp)
    +0x1824: mov     0x658(%r14),%rax
    +0x182b: xor     %rax,0x90(%rsp)
    +0x1833: mov     %r13,%rdi
    +0x1836: call    <mldsa_keccakf1600_permute>
    +0x183b: movups  0x660(%r14),%xmm0
    +0x1843: movups  0x670(%r14),%xmm1
    +0x184b: xorps   0x10(%rsp),%xmm0
    +0x1850: xorps   0x20(%rsp),%xmm1
    +0x1855: movaps  %xmm0,0x10(%rsp)
    +0x185a: movaps  %xmm1,0x20(%rsp)
    +0x185f: movups  0x680(%r14),%xmm0
    +0x1867: movups  0x690(%r14),%xmm1
    +0x186f: xorps   0x30(%rsp),%xmm0
    +0x1874: xorps   0x40(%rsp),%xmm1
    +0x1879: movaps  %xmm0,0x30(%rsp)
    +0x187e: movaps  %xmm1,0x40(%rsp)
    +0x1883: movups  0x6a0(%r14),%xmm0
    +0x188b: movups  0x6b0(%r14),%xmm1
    +0x1893: xorps   0x50(%rsp),%xmm0
    +0x1898: xorps   0x60(%rsp),%xmm1
    +0x189d: movaps  %xmm0,0x50(%rsp)
    +0x18a2: movaps  %xmm1,0x60(%rsp)
    +0x18a7: movups  0x6c0(%r14),%xmm0
    +0x18af: movups  0x6d0(%r14),%xmm1
    +0x18b7: xorps   0x70(%rsp),%xmm0
    +0x18bc: xorps   0x80(%rsp),%xmm1
    +0x18c4: movaps  %xmm0,0x70(%rsp)
    +0x18c9: movaps  %xmm1,0x80(%rsp)
    +0x18d1: mov     0x6e0(%r14),%rax
    +0x18d8: xor     %rax,0x90(%rsp)
    +0x18e0: mov     %r13,%rdi
    +0x18e3: call    <mldsa_keccakf1600_permute>
    +0x18e8: movups  0x6e8(%r14),%xmm0
    +0x18f0: movups  0x6f8(%r14),%xmm1
    +0x18f8: xorps   0x10(%rsp),%xmm0
    +0x18fd: xorps   0x20(%rsp),%xmm1
    +0x1902: movaps  %xmm0,0x10(%rsp)
    +0x1907: movaps  %xmm1,0x20(%rsp)
    +0x190c: movups  0x708(%r14),%xmm0
    +0x1914: movups  0x718(%r14),%xmm1
    +0x191c: xorps   0x30(%rsp),%xmm0
    +0x1921: xorps   0x40(%rsp),%xmm1
    +0x1926: movaps  %xmm0,0x30(%rsp)
    +0x192b: movaps  %xmm1,0x40(%rsp)
    +0x1930: movups  0x728(%r14),%xmm0
    +0x1938: movups  0x738(%r14),%xmm1
    +0x1940: xorps   0x50(%rsp),%xmm0
    +0x1945: xorps   0x60(%rsp),%xmm1
    +0x194a: movaps  %xmm0,0x50(%rsp)
    +0x194f: movaps  %xmm1,0x60(%rsp)
    +0x1954: movups  0x748(%r14),%xmm0
    +0x195c: movups  0x758(%r14),%xmm1
    +0x1964: xorps   0x70(%rsp),%xmm0
    +0x1969: xorps   0x80(%rsp),%xmm1
    +0x1971: movaps  %xmm0,0x70(%rsp)
    +0x1976: movaps  %xmm1,0x80(%rsp)
    +0x197e: mov     0x768(%r14),%rax
    +0x1985: xor     %rax,0x90(%rsp)
    +0x198d: mov     %r13,%rdi
    +0x1990: call    <mldsa_keccakf1600_permute>
    +0x1995: movups  0x770(%r14),%xmm0
    +0x199d: movups  0x780(%r14),%xmm1
    +0x19a5: xorps   0x10(%rsp),%xmm0
    +0x19aa: xorps   0x20(%rsp),%xmm1
    +0x19af: movaps  %xmm0,0x10(%rsp)
    +0x19b4: movaps  %xmm1,0x20(%rsp)
    +0x19b9: movups  0x790(%r14),%xmm0
    +0x19c1: movups  0x7a0(%r14),%xmm1
    +0x19c9: xorps   0x30(%rsp),%xmm0
    +0x19ce: xorps   0x40(%rsp),%xmm1
    +0x19d3: movaps  %xmm0,0x30(%rsp)
    +0x19d8: movaps  %xmm1,0x40(%rsp)
    +0x19dd: movups  0x7b0(%r14),%xmm0
    +0x19e5: movups  0x7c0(%r14),%xmm1
    +0x19ed: xorps   0x50(%rsp),%xmm0
    +0x19f2: xorps   0x60(%rsp),%xmm1
    +0x19f7: movaps  %xmm0,0x50(%rsp)
    +0x19fc: movaps  %xmm1,0x60(%rsp)
    +0x1a01: movups  0x7d0(%r14),%xmm0
    +0x1a09: movups  0x7e0(%r14),%xmm1
    +0x1a11: xorps   0x70(%rsp),%xmm0
    +0x1a16: xorps   0x80(%rsp),%xmm1
    +0x1a1e: movaps  %xmm0,0x70(%rsp)
    +0x1a23: movaps  %xmm1,0x80(%rsp)
    +0x1a2b: mov     0x7f0(%r14),%rax
    +0x1a32: xor     %rax,0x90(%rsp)
    +0x1a3a: mov     %r13,%rdi
    +0x1a3d: call    <mldsa_keccakf1600_permute>
    +0x1a42: movups  0x7f8(%r14),%xmm0
    +0x1a4a: movups  0x808(%r14),%xmm1
    +0x1a52: xorps   0x10(%rsp),%xmm0
    +0x1a57: xorps   0x20(%rsp),%xmm1
    +0x1a5c: movaps  %xmm0,0x10(%rsp)
    +0x1a61: movaps  %xmm1,0x20(%rsp)
    +0x1a66: movups  0x818(%r14),%xmm0
    +0x1a6e: movups  0x828(%r14),%xmm1
    +0x1a76: xorps   0x30(%rsp),%xmm0
    +0x1a7b: xorps   0x40(%rsp),%xmm1
    +0x1a80: movaps  %xmm0,0x30(%rsp)
    +0x1a85: movaps  %xmm1,0x40(%rsp)
    +0x1a8a: movups  0x838(%r14),%xmm0
    +0x1a92: movups  0x848(%r14),%xmm1
    +0x1a9a: xorps   0x50(%rsp),%xmm0
    +0x1a9f: xorps   0x60(%rsp),%xmm1
    +0x1aa4: movaps  %xmm0,0x50(%rsp)
    +0x1aa9: movaps  %xmm1,0x60(%rsp)
    +0x1aae: movups  0x858(%r14),%xmm0
    +0x1ab6: movups  0x868(%r14),%xmm1
    +0x1abe: xorps   0x70(%rsp),%xmm0
    +0x1ac3: xorps   0x80(%rsp),%xmm1
    +0x1acb: movaps  %xmm0,0x70(%rsp)
    +0x1ad0: movaps  %xmm1,0x80(%rsp)
    +0x1ad8: mov     0x878(%r14),%rax
    +0x1adf: xor     %rax,0x90(%rsp)
    +0x1ae7: mov     %r13,%rdi
    +0x1aea: call    <mldsa_keccakf1600_permute>
    +0x1aef: movups  0x880(%r14),%xmm0
    +0x1af7: movups  0x890(%r14),%xmm1
    +0x1aff: xorps   0x10(%rsp),%xmm0
    +0x1b04: xorps   0x20(%rsp),%xmm1
    +0x1b09: movaps  %xmm0,0x10(%rsp)
    +0x1b0e: movaps  %xmm1,0x20(%rsp)
    +0x1b13: movups  0x8a0(%r14),%xmm0
    +0x1b1b: movups  0x8b0(%r14),%xmm1
    +0x1b23: xorps   0x30(%rsp),%xmm0
    +0x1b28: xorps   0x40(%rsp),%xmm1
    +0x1b2d: movaps  %xmm0,0x30(%rsp)
    +0x1b32: movaps  %xmm1,0x40(%rsp)
    +0x1b37: movups  0x8c0(%r14),%xmm0
    +0x1b3f: movups  0x8d0(%r14),%xmm1
    +0x1b47: xorps   0x50(%rsp),%xmm0
    +0x1b4c: xorps   0x60(%rsp),%xmm1
    +0x1b51: movaps  %xmm0,0x50(%rsp)
    +0x1b56: movaps  %xmm1,0x60(%rsp)
    +0x1b5b: movups  0x8e0(%r14),%xmm0
    +0x1b63: movups  0x8f0(%r14),%xmm1
    +0x1b6b: xorps   0x70(%rsp),%xmm0
    +0x1b70: xorps   0x80(%rsp),%xmm1
    +0x1b78: movaps  %xmm0,0x70(%rsp)
    +0x1b7d: movaps  %xmm1,0x80(%rsp)
    +0x1b85: mov     0x900(%r14),%rax
    +0x1b8c: xor     %rax,0x90(%rsp)
    +0x1b94: mov     %r13,%rdi
    +0x1b97: call    <mldsa_keccakf1600_permute>
    +0x1b9c: movups  0x908(%r14),%xmm0
    +0x1ba4: movups  0x918(%r14),%xmm1
    +0x1bac: xorps   0x10(%rsp),%xmm0
    +0x1bb1: xorps   0x20(%rsp),%xmm1
    +0x1bb6: movaps  %xmm0,0x10(%rsp)
    +0x1bbb: movaps  %xmm1,0x20(%rsp)
    +0x1bc0: movups  0x928(%r14),%xmm0
    +0x1bc8: movups  0x938(%r14),%xmm1
    +0x1bd0: xorps   0x30(%rsp),%xmm0
    +0x1bd5: xorps   0x40(%rsp),%xmm1
    +0x1bda: movaps  %xmm0,0x30(%rsp)
    +0x1bdf: movaps  %xmm1,0x40(%rsp)
    +0x1be4: movups  0x948(%r14),%xmm0
    +0x1bec: movups  0x958(%r14),%xmm1
    +0x1bf4: xorps   0x50(%rsp),%xmm0
    +0x1bf9: xorps   0x60(%rsp),%xmm1
    +0x1bfe: movaps  %xmm0,0x50(%rsp)
    +0x1c03: movaps  %xmm1,0x60(%rsp)
    +0x1c08: movups  0x968(%r14),%xmm0
    +0x1c10: movups  0x978(%r14),%xmm1
    +0x1c18: xorps   0x70(%rsp),%xmm0
    +0x1c1d: xorps   0x80(%rsp),%xmm1
    +0x1c25: movaps  %xmm0,0x70(%rsp)
    +0x1c2a: movaps  %xmm1,0x80(%rsp)
    +0x1c32: mov     0x988(%r14),%rax
    +0x1c39: xor     %rax,0x90(%rsp)
    +0x1c41: mov     %r13,%rdi
    +0x1c44: call    <mldsa_keccakf1600_permute>
    +0x1c49: movups  0x990(%r14),%xmm0
    +0x1c51: movups  0x9a0(%r14),%xmm1
    +0x1c59: xorps   0x10(%rsp),%xmm0
    +0x1c5e: xorps   0x20(%rsp),%xmm1
    +0x1c63: movaps  %xmm0,0x10(%rsp)
    +0x1c68: movaps  %xmm1,0x20(%rsp)
    +0x1c6d: movups  0x9b0(%r14),%xmm0
    +0x1c75: movups  0x9c0(%r14),%xmm1
    +0x1c7d: xorps   0x30(%rsp),%xmm0
    +0x1c82: xorps   0x40(%rsp),%xmm1
    +0x1c87: movaps  %xmm0,0x30(%rsp)
    +0x1c8c: movaps  %xmm1,0x40(%rsp)
    +0x1c91: movups  0x9d0(%r14),%xmm0
    +0x1c99: movups  0x9e0(%r14),%xmm1
    +0x1ca1: xorps   0x50(%rsp),%xmm0
    +0x1ca6: xorps   0x60(%rsp),%xmm1
    +0x1cab: movaps  %xmm0,0x50(%rsp)
    +0x1cb0: movaps  %xmm1,0x60(%rsp)
    +0x1cb5: movups  0x9f0(%r14),%xmm0
    +0x1cbd: movups  0xa00(%r14),%xmm1
    +0x1cc5: xorps   0x70(%rsp),%xmm0
    +0x1cca: xorps   0x80(%rsp),%xmm1
    +0x1cd2: movaps  %xmm0,0x70(%rsp)
    +0x1cd7: movaps  %xmm1,0x80(%rsp)
    +0x1cdf: mov     0xa10(%r14),%rax
    +0x1ce6: xor     %rax,0x90(%rsp)
    +0x1cee: mov     %r13,%rdi
    +0x1cf1: call    <mldsa_keccakf1600_permute>
    +0x1cf6: mov     0xa18(%r14),%rax
    +0x1cfd: xor     %rax,0x10(%rsp)
    +0x1d02: xorb    $0x1f,0x18(%rsp)
    +0x1d07: xorb    $0x80,0x97(%rsp)
    +0x1d0f: movl    $0x88,0xd8(%rsp)
    +0x1d1a: mov     %r13,%rdi
    +0x1d1d: call    <mldsa_keccakf1600_permute>
    +0x1d22: movaps  0x10(%rsp),%xmm0
    +0x1d27: movaps  0x20(%rsp),%xmm1
    +0x1d2c: movaps  0x30(%rsp),%xmm2
    +0x1d31: movaps  0x40(%rsp),%xmm3
    +0x1d36: movaps  %xmm3,0x150(%rsp)
    +0x1d3e: movaps  %xmm2,0x140(%rsp)
    +0x1d46: movaps  %xmm1,0x130(%rsp)
    +0x1d4e: movaps  %xmm0,0x120(%rsp)
    +0x1d56: xorps   %xmm0,%xmm0
    +0x1d59: movaps  %xmm0,0x50(%rsp)
    +0x1d5e: movaps  %xmm0,0x60(%rsp)
    +0x1d63: movaps  %xmm0,0x70(%rsp)
    +0x1d68: movaps  %xmm0,0x80(%rsp)
    +0x1d70: movaps  %xmm0,0x90(%rsp)
    +0x1d78: movaps  %xmm0,0xa0(%rsp)
    +0x1d80: movaps  %xmm0,0xb0(%rsp)
    +0x1d88: movaps  %xmm0,0xc0(%rsp)
    +0x1d90: movaps  %xmm0,0xd0(%rsp)
    +0x1d98: movaps  %xmm0,0x10(%rsp)
    +0x1d9d: movaps  %xmm0,0x20(%rsp)
    +0x1da2: movaps  %xmm0,0x30(%rsp)
    +0x1da7: movaps  %xmm0,0x40(%rsp)
    +0x1dac: movaps  0x160(%rsp),%xmm0
    +0x1db4: movaps  0x170(%rsp),%xmm1
    +0x1dbc: movups  %xmm1,0x10(%rbx)
    +0x1dc0: movups  %xmm0,(%rbx)
    +0x1dc3: movaps  0x1c0(%rsp),%xmm0
    +0x1dcb: movaps  0x1d0(%rsp),%xmm1
    +0x1dd3: movups  %xmm1,0x30(%rbx)
    +0x1dd7: movups  %xmm0,0x20(%rbx)
    +0x1ddb: movaps  0x120(%rsp),%xmm0
    +0x1de3: movaps  0x130(%rsp),%xmm1
    +0x1deb: movaps  0x140(%rsp),%xmm2
    +0x1df3: movaps  0x150(%rsp),%xmm3
    +0x1dfb: movups  %xmm0,0x40(%rbx)
    +0x1dff: movups  %xmm1,0x50(%rbx)
    +0x1e03: movups  %xmm2,0x60(%rbx)
    +0x1e07: movups  %xmm3,0x70(%rbx)
    +0x1e0b: mov     $0x1c00,%edx
    +0x1e10: mov     %r15,%rdi
    +0x1e13: xor     %esi,%esi
    +0x1e15: call    <memset>
    +0x1e1a: xorps   %xmm0,%xmm0
    +0x1e1d: movaps  %xmm0,0x150(%rsp)
    +0x1e25: movaps  %xmm0,0x140(%rsp)
    +0x1e2d: movaps  %xmm0,0x130(%rsp)
    +0x1e35: movaps  %xmm0,0x120(%rsp)
    +0x1e3d: lea     0x120(%rsp),%rax
    +0x1e45: movaps  %xmm0,0xf0(%rsp)
    +0x1e4d: movaps  %xmm0,0xe0(%rsp)
    +0x1e55: movw    $0x0,0x100(%rsp)
    +0x1e5f: lea     0xe0(%rsp),%rax
    +0x1e67: movaps  %xmm0,0x1d0(%rsp)
    +0x1e6f: movaps  %xmm0,0x1c0(%rsp)
    +0x1e77: movaps  %xmm0,0x1b0(%rsp)
    +0x1e7f: movaps  %xmm0,0x1a0(%rsp)
    +0x1e87: movaps  %xmm0,0x190(%rsp)
    +0x1e8f: movaps  %xmm0,0x180(%rsp)
    +0x1e97: movaps  %xmm0,0x170(%rsp)
    +0x1e9f: movaps  %xmm0,0x160(%rsp)
    +0x1ea7: xor     %eax,%eax
    +0x1ea9: lea     -0x28(%rbp),%rsp
    +0x1ead: pop     %rbx
    +0x1eae: pop     %r12
    +0x1eb0: pop     %r13
    +0x1eb2: pop     %r14
    +0x1eb4: pop     %r15
    +0x1eb6: pop     %rbp
    +0x1eb7: xor     %ecx,%ecx
    +0x1eb9: xor     %edi,%edi
    +0x1ebb: xor     %edx,%edx
    +0x1ebd: xor     %esi,%esi
    +0x1ebf: xor     %r8d,%r8d
    +0x1ec2: xor     %r9d,%r9d
    +0x1ec5: xor     %r10d,%r10d
    +0x1ec8: xor     %r11d,%r11d
    +0x1ecb: ret     
 ***)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa87_keypair_internal";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. From the seed SEED (32 bytes at seed), the public key at pk  *)
(* (2592 bytes) becomes mld_keypair_pk_87 SEED and the secret key at sk      *)
(* (4896 bytes) mld_keypair_sk_87 SEED, and the result is 0. The stack is    *)
(* the 12668 bytes below the return address: the six saved registers, up to  *)
(* 31 bytes of realignment, the frame of 7680 bytes and the 4909 bytes of    *)
(* the call of mld_compute_pack_t0_t187, the deepest callee.                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !pk sk seed SEED pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 8 7 (mld_keypair_rho 8 7 SEED) /\
        mld_keypair_terminates_87 SEED /\
        PAIRWISE nonoverlapping
         [(pk,2592); (sk,4896);
          (word_sub stackpointer (word 12668),12668)] /\
        ALLPAIRS nonoverlapping
         [(pk,2592); (sk,4896);
          (word_sub stackpointer (word 12668),12668)]
         [(seed,32); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pk,2592); (sk,4896)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_keypair_internal) /\
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
                  (!j. j < 2592
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           mld_keypair_pk_87 SEED j) /\
                  (!j. j < 4896
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           mld_keypair_sk_87 SEED j))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                memory :> bytes(word_sub stackpointer (word 12668),12668)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, whether each nibble read by  *)
(* the sampling of each polynomial is accepted (mld_keypair_declass_87) and  *)
(* the stack, with all accesses within the arguments, the stack, the return  *)
(* address and the constants of the function and of the callees, and the     *)
(* writes within the keys and the stack.                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e pk sk seed SEED pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 8 7 (mld_keypair_rho 8 7 SEED) /\
        mld_keypair_terminates_87 SEED /\
        PAIRWISE nonoverlapping
         [(pk,2592); (sk,4896);
          (word_sub stackpointer (word 12668),12668)] /\
        ALLPAIRS nonoverlapping
         [(pk,2592); (sk,4896);
          (word_sub stackpointer (word 12668),12668)]
         [(seed,32); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pk,2592); (sk,4896)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_keypair_internal) /\
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
                  (!j. j < 2592
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           mld_keypair_pk_87 SEED j) /\
                  (!j. j < 4896
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           mld_keypair_sk_87 SEED j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events pk sk seed (mld_keypair_rho 8 7 SEED)
                           (mld_keypair_declass_87 SEED) mf mc pc
                           (word_sub stackpointer (word 12668))
                           returnaddress /\
                     memaccess_inbounds e2
                      [seed,32; pk,2592; sk,4896;
                       word_sub stackpointer (word 12668),12668;
                       stackpointer,8; word(pc + got_memset),8;
                       word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_ntt_consts),256;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word(pc + mld_compute_pack_t0_t187_consts),64;
                       word(pc + mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32]
                      [pk,2592; sk,4896;
                       word_sub stackpointer (word 12668),12668]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                memory :> bytes(word_sub stackpointer (word 12668),12668)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e pk sk seed SEED pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 8 7 (mld_keypair_rho 8 7 SEED) /\
        mld_keypair_terminates_87 SEED /\
        PAIRWISE nonoverlapping
         [(pk,2592); (sk,4896);
          (word_sub stackpointer (word 12668),12668)] /\
        ALLPAIRS nonoverlapping
         [(pk,2592); (sk,4896);
          (word_sub stackpointer (word 12668),12668)]
         [(seed,32); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pk,2592); (sk,4896)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_keypair_internal) /\
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
                     e2 = f_events pk sk seed (mld_keypair_rho 8 7 SEED)
                           (mld_keypair_declass_87 SEED) mf mc pc
                           (word_sub stackpointer (word 12668))
                           returnaddress /\
                     memaccess_inbounds e2
                      [seed,32; pk,2592; sk,4896;
                       word_sub stackpointer (word 12668),12668;
                       stackpointer,8; word(pc + got_memset),8;
                       word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_ntt_consts),256;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word(pc + mld_compute_pack_t0_t187_consts),64;
                       word(pc + mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32]
                      [pk,2592; sk,4896;
                       word_sub stackpointer (word 12668),12668]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                memory :> bytes(word_sub stackpointer (word 12668),12668)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
