(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the statement. This is the code for                       *)
(* mldsa44_keypair_internal (mld_sign_keypair_internal in sign.c) from       *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3    *)
(* and MLD_CONFIG_REDUCE_RAM (the monolithic build, see                      *)
(* mldsa_native/README.md). Clang inlines most of it: the SHAKE256 of the    *)
(* seed that gives rho, rho' and the key (one permutation with               *)
(* mldsa_keccakf1600_permute), the packing of each polynomial of s2 and s1   *)
(* into the secret key (mld_polyeta_pack), the copies of rho, the key and tr *)
(* into the keys, and the SHAKE256 of the public key into tr (ten            *)
(* permutations). It calls mldsa44_poly_uniform_eta_4x for s2 and then s1,   *)
(* mldsa_poly_ntt for each polynomial of s1 and mld_compute_pack_t0_t144,    *)
(* which computes t and packs t1 into the public key and t0 into the secret  *)
(* key, and clears its buffers with SSE stores and memset. It aligns its     *)
(* frame to 32 bytes (see utils/mldsa_native_realign.ml). It is verified in  *)
(* the whole image (see libmldsa.ml) against mld_keypair_pk_44 and           *)
(* mld_keypair_sk_44 of common/mldsa_native_sign.ml, using the theorems for  *)
(* the callees and for the inlined regions (keypair_internal_44_lemmas.ml),  *)
(* assuming that the sampling of the matrix and of each polynomial           *)
(* terminates, and shown to be constant time and memory safe, with the       *)
(* events depending only on the addresses and the values that the C code     *)
(* declassifies (rho and mld_keypair_declass_44).                            *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_keypair_internal:
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
      +0x20: sub     $0x220,%rsp
      +0x27: mov     %rsi,%rbx
      +0x2a: movups  (%rdx),%xmm0
      +0x2d: movups  0x10(%rdx),%xmm1
      +0x31: movaps  %xmm1,0xf0(%rsp)
      +0x39: movaps  %xmm0,0xe0(%rsp)
      +0x41: movw    $0x404,0x100(%rsp)
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
     +0x128: lea     0x1e0(%rsp),%r15
     +0x130: mov     %r15,%rdi
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
     +0x1b8: lea     0x180(%rsp),%r12
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
     +0x24f: mov     %r12,%r8
     +0x252: mov     $0x4,%r9d
     +0x258: push    $0x7
     +0x25a: push    $0x6
     +0x25c: push    $0x5
     +0x25e: call    <mldsa44_poly_uniform_eta_4x>
     +0x263: add     $0x20,%rsp
     +0x267: mov     $0x202,%eax
     +0x26c: lea     0x1fc(%rsp),%rcx
     +0x274: data16  data16 cs nopw 0x0(%rax,%rax,1)
     +0x280: mov     $0x2,%r8b
     +0x283: sub     -0x1c(%rcx),%r8b
     +0x287: mov     $0x2,%r9b
     +0x28a: sub     -0x14(%rcx),%r9b
     +0x28e: movzbl  -0x18(%rcx),%r10d
     +0x293: movzbl  -0x10(%rcx),%r11d
     +0x298: movzbl  -0xc(%rcx),%r13d
     +0x29d: mov     $0x2,%sil
     +0x2a0: sub     -0x8(%rcx),%sil
     +0x2a4: movzbl  -0x4(%rcx),%edi
     +0x2a8: movzbl  (%rcx),%edx
     +0x2ab: shl     $0x3,%r10b
     +0x2af: mov     $0x10,%r15b
     +0x2b2: sub     %r10b,%r15b
     +0x2b5: or      %r8b,%r15b
     +0x2b8: mov     %r9d,%r8d
     +0x2bb: shl     $0x6,%r8b
     +0x2bf: or      %r15b,%r8b
     +0x2c2: mov     %r8b,-0x2(%rbx,%rax,1)
     +0x2c7: shr     $0x2,%r9b
     +0x2cb: add     %r11b,%r11b
     +0x2ce: mov     $0x4,%r8b
     +0x2d1: sub     %r11b,%r8b
     +0x2d4: or      %r9b,%r8b
     +0x2d7: shl     $0x4,%r13b
     +0x2db: mov     $0x20,%r9b
     +0x2de: sub     %r13b,%r9b
     +0x2e1: mov     %esi,%r10d
     +0x2e4: shl     $0x7,%r10b
     +0x2e8: or      %r9b,%r10b
     +0x2eb: or      %r8b,%r10b
     +0x2ee: mov     %r10b,-0x1(%rbx,%rax,1)
     +0x2f3: shr     $1,%sil
     +0x2f6: shl     $0x2,%dil
     +0x2fa: mov     $0x8,%r8b
     +0x2fd: sub     %dil,%r8b
     +0x300: or      %sil,%r8b
     +0x303: shl     $0x5,%dl
     +0x306: mov     $0x40,%sil
     +0x309: sub     %dl,%sil
     +0x30c: or      %r8b,%sil
     +0x30f: mov     %sil,(%rbx,%rax,1)
     +0x313: add     $0x3,%rax
     +0x317: add     $0x20,%rcx
     +0x31b: cmp     $0x262,%rax
     +0x321: jne     <mldsa44_keypair_internal+0x280>
     +0x327: movq    $0x0,0x10(%rsp)
     +0x330: lea     0x10(%rsp),%rax
     +0x335: mov     $0x262,%eax
     +0x33a: lea     0x5fc(%rsp),%rcx
     +0x342: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x350: mov     $0x2,%r8b
     +0x353: sub     -0x1c(%rcx),%r8b
     +0x357: mov     $0x2,%r9b
     +0x35a: sub     -0x14(%rcx),%r9b
     +0x35e: movzbl  -0x18(%rcx),%r10d
     +0x363: movzbl  -0x10(%rcx),%r11d
     +0x368: movzbl  -0xc(%rcx),%r15d
     +0x36d: mov     $0x2,%sil
     +0x370: sub     -0x8(%rcx),%sil
     +0x374: movzbl  -0x4(%rcx),%edi
     +0x378: movzbl  (%rcx),%edx
     +0x37b: shl     $0x3,%r10b
     +0x37f: mov     $0x10,%r13b
     +0x382: sub     %r10b,%r13b
     +0x385: or      %r8b,%r13b
     +0x388: mov     %r9d,%r8d
     +0x38b: shl     $0x6,%r8b
     +0x38f: or      %r13b,%r8b
     +0x392: mov     %r8b,-0x2(%rbx,%rax,1)
     +0x397: shr     $0x2,%r9b
     +0x39b: add     %r11b,%r11b
     +0x39e: mov     $0x4,%r8b
     +0x3a1: sub     %r11b,%r8b
     +0x3a4: or      %r9b,%r8b
     +0x3a7: shl     $0x4,%r15b
     +0x3ab: mov     $0x20,%r9b
     +0x3ae: sub     %r15b,%r9b
     +0x3b1: mov     %esi,%r10d
     +0x3b4: shl     $0x7,%r10b
     +0x3b8: or      %r9b,%r10b
     +0x3bb: or      %r8b,%r10b
     +0x3be: mov     %r10b,-0x1(%rbx,%rax,1)
     +0x3c3: shr     $1,%sil
     +0x3c6: shl     $0x2,%dil
     +0x3ca: mov     $0x8,%r8b
     +0x3cd: sub     %dil,%r8b
     +0x3d0: or      %sil,%r8b
     +0x3d3: shl     $0x5,%dl
     +0x3d6: mov     $0x40,%sil
     +0x3d9: sub     %dl,%sil
     +0x3dc: or      %r8b,%sil
     +0x3df: mov     %sil,(%rbx,%rax,1)
     +0x3e3: add     $0x3,%rax
     +0x3e7: add     $0x20,%rcx
     +0x3eb: cmp     $0x2c2,%rax
     +0x3f1: jne     <mldsa44_keypair_internal+0x350>
     +0x3f7: movq    $0x0,0x10(%rsp)
     +0x400: lea     0x10(%rsp),%rax
     +0x405: mov     $0x2c2,%eax
     +0x40a: lea     0x9fc(%rsp),%rcx
     +0x412: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x420: mov     $0x2,%r8b
     +0x423: sub     -0x1c(%rcx),%r8b
     +0x427: mov     $0x2,%r9b
     +0x42a: sub     -0x14(%rcx),%r9b
     +0x42e: movzbl  -0x18(%rcx),%r10d
     +0x433: movzbl  -0x10(%rcx),%r11d
     +0x438: movzbl  -0xc(%rcx),%r15d
     +0x43d: mov     $0x2,%sil
     +0x440: sub     -0x8(%rcx),%sil
     +0x444: movzbl  -0x4(%rcx),%edi
     +0x448: movzbl  (%rcx),%edx
     +0x44b: shl     $0x3,%r10b
     +0x44f: mov     $0x10,%r13b
     +0x452: sub     %r10b,%r13b
     +0x455: or      %r8b,%r13b
     +0x458: mov     %r9d,%r8d
     +0x45b: shl     $0x6,%r8b
     +0x45f: or      %r13b,%r8b
     +0x462: mov     %r8b,-0x2(%rbx,%rax,1)
     +0x467: shr     $0x2,%r9b
     +0x46b: add     %r11b,%r11b
     +0x46e: mov     $0x4,%r8b
     +0x471: sub     %r11b,%r8b
     +0x474: or      %r9b,%r8b
     +0x477: shl     $0x4,%r15b
     +0x47b: mov     $0x20,%r9b
     +0x47e: sub     %r15b,%r9b
     +0x481: mov     %esi,%r10d
     +0x484: shl     $0x7,%r10b
     +0x488: or      %r9b,%r10b
     +0x48b: or      %r8b,%r10b
     +0x48e: mov     %r10b,-0x1(%rbx,%rax,1)
     +0x493: shr     $1,%sil
     +0x496: shl     $0x2,%dil
     +0x49a: mov     $0x8,%r8b
     +0x49d: sub     %dil,%r8b
     +0x4a0: or      %sil,%r8b
     +0x4a3: shl     $0x5,%dl
     +0x4a6: mov     $0x40,%sil
     +0x4a9: sub     %dl,%sil
     +0x4ac: or      %r8b,%sil
     +0x4af: mov     %sil,(%rbx,%rax,1)
     +0x4b3: add     $0x3,%rax
     +0x4b7: add     $0x20,%rcx
     +0x4bb: cmp     $0x322,%rax
     +0x4c1: jne     <mldsa44_keypair_internal+0x420>
     +0x4c7: movq    $0x0,0x10(%rsp)
     +0x4d0: lea     0x10(%rsp),%rax
     +0x4d5: mov     $0x322,%eax
     +0x4da: lea     0xdfc(%rsp),%rcx
     +0x4e2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x4f0: mov     $0x2,%r8b
     +0x4f3: sub     -0x1c(%rcx),%r8b
     +0x4f7: mov     $0x2,%r9b
     +0x4fa: sub     -0x14(%rcx),%r9b
     +0x4fe: movzbl  -0x18(%rcx),%r10d
     +0x503: movzbl  -0x10(%rcx),%r11d
     +0x508: movzbl  -0xc(%rcx),%r15d
     +0x50d: mov     $0x2,%sil
     +0x510: sub     -0x8(%rcx),%sil
     +0x514: movzbl  -0x4(%rcx),%edi
     +0x518: movzbl  (%rcx),%edx
     +0x51b: shl     $0x3,%r10b
     +0x51f: mov     $0x10,%r13b
     +0x522: sub     %r10b,%r13b
     +0x525: or      %r8b,%r13b
     +0x528: mov     %r9d,%r8d
     +0x52b: shl     $0x6,%r8b
     +0x52f: or      %r13b,%r8b
     +0x532: mov     %r8b,-0x2(%rbx,%rax,1)
     +0x537: shr     $0x2,%r9b
     +0x53b: add     %r11b,%r11b
     +0x53e: mov     $0x4,%r8b
     +0x541: sub     %r11b,%r8b
     +0x544: or      %r9b,%r8b
     +0x547: shl     $0x4,%r15b
     +0x54b: mov     $0x20,%r9b
     +0x54e: sub     %r15b,%r9b
     +0x551: mov     %esi,%r10d
     +0x554: shl     $0x7,%r10b
     +0x558: or      %r9b,%r10b
     +0x55b: or      %r8b,%r10b
     +0x55e: mov     %r10b,-0x1(%rbx,%rax,1)
     +0x563: shr     $1,%sil
     +0x566: shl     $0x2,%dil
     +0x56a: mov     $0x8,%r8b
     +0x56d: sub     %dil,%r8b
     +0x570: or      %sil,%r8b
     +0x573: shl     $0x5,%dl
     +0x576: mov     $0x40,%sil
     +0x579: sub     %dl,%sil
     +0x57c: or      %r8b,%sil
     +0x57f: mov     %sil,(%rbx,%rax,1)
     +0x583: add     $0x3,%rax
     +0x587: add     $0x20,%rcx
     +0x58b: cmp     $0x382,%rax
     +0x591: jne     <mldsa44_keypair_internal+0x4f0>
     +0x597: movq    $0x0,0x10(%rsp)
     +0x5a0: lea     0x10(%rsp),%rax
     +0x5a5: sub     $0x8,%rsp
     +0x5a9: lea     0x1e8(%rsp),%rdi
     +0x5b1: lea     0x5e8(%rsp),%rsi
     +0x5b9: lea     0x9e8(%rsp),%rdx
     +0x5c1: lea     0xde8(%rsp),%r13
     +0x5c9: mov     %r13,%rcx
     +0x5cc: mov     %r12,%r8
     +0x5cf: xor     %r9d,%r9d
     +0x5d2: push    $0x3
     +0x5d4: push    $0x2
     +0x5d6: push    $0x1
     +0x5d8: call    <mldsa44_poly_uniform_eta_4x>
     +0x5dd: add     $0x20,%rsp
     +0x5e1: mov     $0x82,%eax
     +0x5e6: lea     0x1fc(%rsp),%rcx
     +0x5ee: xchg    %ax,%ax
     +0x5f0: mov     $0x2,%r8b
     +0x5f3: sub     -0x1c(%rcx),%r8b
     +0x5f7: mov     $0x2,%r9b
     +0x5fa: sub     -0x14(%rcx),%r9b
     +0x5fe: movzbl  -0x18(%rcx),%r10d
     +0x603: movzbl  -0x10(%rcx),%r11d
     +0x608: movzbl  -0xc(%rcx),%r15d
     +0x60d: mov     $0x2,%sil
     +0x610: sub     -0x8(%rcx),%sil
     +0x614: movzbl  -0x4(%rcx),%edi
     +0x618: movzbl  (%rcx),%edx
     +0x61b: shl     $0x3,%r10b
     +0x61f: mov     $0x10,%r12b
     +0x622: sub     %r10b,%r12b
     +0x625: or      %r8b,%r12b
     +0x628: mov     %r9d,%r8d
     +0x62b: shl     $0x6,%r8b
     +0x62f: or      %r12b,%r8b
     +0x632: mov     %r8b,-0x2(%rbx,%rax,1)
     +0x637: shr     $0x2,%r9b
     +0x63b: add     %r11b,%r11b
     +0x63e: mov     $0x4,%r8b
     +0x641: sub     %r11b,%r8b
     +0x644: or      %r9b,%r8b
     +0x647: shl     $0x4,%r15b
     +0x64b: mov     $0x20,%r9b
     +0x64e: sub     %r15b,%r9b
     +0x651: mov     %esi,%r10d
     +0x654: shl     $0x7,%r10b
     +0x658: or      %r9b,%r10b
     +0x65b: or      %r8b,%r10b
     +0x65e: mov     %r10b,-0x1(%rbx,%rax,1)
     +0x663: shr     $1,%sil
     +0x666: shl     $0x2,%dil
     +0x66a: mov     $0x8,%r8b
     +0x66d: sub     %dil,%r8b
     +0x670: or      %sil,%r8b
     +0x673: shl     $0x5,%dl
     +0x676: mov     $0x40,%sil
     +0x679: sub     %dl,%sil
     +0x67c: or      %r8b,%sil
     +0x67f: mov     %sil,(%rbx,%rax,1)
     +0x683: add     $0x3,%rax
     +0x687: add     $0x20,%rcx
     +0x68b: cmp     $0xe2,%rax
     +0x691: jne     <mldsa44_keypair_internal+0x5f0>
     +0x697: movq    $0x0,0x10(%rsp)
     +0x6a0: lea     0x10(%rsp),%rax
     +0x6a5: mov     $0xe2,%eax
     +0x6aa: lea     0x5fc(%rsp),%rcx
     +0x6b2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x6c0: mov     $0x2,%r8b
     +0x6c3: sub     -0x1c(%rcx),%r8b
     +0x6c7: mov     $0x2,%r9b
     +0x6ca: sub     -0x14(%rcx),%r9b
     +0x6ce: movzbl  -0x18(%rcx),%r10d
     +0x6d3: movzbl  -0x10(%rcx),%r11d
     +0x6d8: movzbl  -0xc(%rcx),%r15d
     +0x6dd: mov     $0x2,%sil
     +0x6e0: sub     -0x8(%rcx),%sil
     +0x6e4: movzbl  -0x4(%rcx),%edi
     +0x6e8: movzbl  (%rcx),%edx
     +0x6eb: shl     $0x3,%r10b
     +0x6ef: mov     $0x10,%r12b
     +0x6f2: sub     %r10b,%r12b
     +0x6f5: or      %r8b,%r12b
     +0x6f8: mov     %r9d,%r8d
     +0x6fb: shl     $0x6,%r8b
     +0x6ff: or      %r12b,%r8b
     +0x702: mov     %r8b,-0x2(%rbx,%rax,1)
     +0x707: shr     $0x2,%r9b
     +0x70b: add     %r11b,%r11b
     +0x70e: mov     $0x4,%r8b
     +0x711: sub     %r11b,%r8b
     +0x714: or      %r9b,%r8b
     +0x717: shl     $0x4,%r15b
     +0x71b: mov     $0x20,%r9b
     +0x71e: sub     %r15b,%r9b
     +0x721: mov     %esi,%r10d
     +0x724: shl     $0x7,%r10b
     +0x728: or      %r9b,%r10b
     +0x72b: or      %r8b,%r10b
     +0x72e: mov     %r10b,-0x1(%rbx,%rax,1)
     +0x733: shr     $1,%sil
     +0x736: shl     $0x2,%dil
     +0x73a: mov     $0x8,%r8b
     +0x73d: sub     %dil,%r8b
     +0x740: or      %sil,%r8b
     +0x743: shl     $0x5,%dl
     +0x746: mov     $0x40,%sil
     +0x749: sub     %dl,%sil
     +0x74c: or      %r8b,%sil
     +0x74f: mov     %sil,(%rbx,%rax,1)
     +0x753: add     $0x3,%rax
     +0x757: add     $0x20,%rcx
     +0x75b: cmp     $0x142,%rax
     +0x761: jne     <mldsa44_keypair_internal+0x6c0>
     +0x767: movq    $0x0,0x10(%rsp)
     +0x770: lea     0x10(%rsp),%rax
     +0x775: mov     $0x142,%eax
     +0x77a: lea     0x9fc(%rsp),%rcx
     +0x782: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x790: mov     $0x2,%r8b
     +0x793: sub     -0x1c(%rcx),%r8b
     +0x797: mov     $0x2,%r9b
     +0x79a: sub     -0x14(%rcx),%r9b
     +0x79e: movzbl  -0x18(%rcx),%r10d
     +0x7a3: movzbl  -0x10(%rcx),%r11d
     +0x7a8: movzbl  -0xc(%rcx),%r15d
     +0x7ad: mov     $0x2,%sil
     +0x7b0: sub     -0x8(%rcx),%sil
     +0x7b4: movzbl  -0x4(%rcx),%edi
     +0x7b8: movzbl  (%rcx),%edx
     +0x7bb: shl     $0x3,%r10b
     +0x7bf: mov     $0x10,%r12b
     +0x7c2: sub     %r10b,%r12b
     +0x7c5: or      %r8b,%r12b
     +0x7c8: mov     %r9d,%r8d
     +0x7cb: shl     $0x6,%r8b
     +0x7cf: or      %r12b,%r8b
     +0x7d2: mov     %r8b,-0x2(%rbx,%rax,1)
     +0x7d7: shr     $0x2,%r9b
     +0x7db: add     %r11b,%r11b
     +0x7de: mov     $0x4,%r8b
     +0x7e1: sub     %r11b,%r8b
     +0x7e4: or      %r9b,%r8b
     +0x7e7: shl     $0x4,%r15b
     +0x7eb: mov     $0x20,%r9b
     +0x7ee: sub     %r15b,%r9b
     +0x7f1: mov     %esi,%r10d
     +0x7f4: shl     $0x7,%r10b
     +0x7f8: or      %r9b,%r10b
     +0x7fb: or      %r8b,%r10b
     +0x7fe: mov     %r10b,-0x1(%rbx,%rax,1)
     +0x803: shr     $1,%sil
     +0x806: shl     $0x2,%dil
     +0x80a: mov     $0x8,%r8b
     +0x80d: sub     %dil,%r8b
     +0x810: or      %sil,%r8b
     +0x813: shl     $0x5,%dl
     +0x816: mov     $0x40,%sil
     +0x819: sub     %dl,%sil
     +0x81c: or      %r8b,%sil
     +0x81f: mov     %sil,(%rbx,%rax,1)
     +0x823: add     $0x3,%rax
     +0x827: add     $0x20,%rcx
     +0x82b: cmp     $0x1a2,%rax
     +0x831: jne     <mldsa44_keypair_internal+0x790>
     +0x837: movq    $0x0,0x10(%rsp)
     +0x840: lea     0x10(%rsp),%rax
     +0x845: mov     $0x1a2,%eax
     +0x84a: lea     0xdfc(%rsp),%rcx
     +0x852: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x860: mov     $0x2,%r8b
     +0x863: sub     -0x1c(%rcx),%r8b
     +0x867: mov     $0x2,%r9b
     +0x86a: sub     -0x14(%rcx),%r9b
     +0x86e: movzbl  -0x18(%rcx),%r10d
     +0x873: movzbl  -0x10(%rcx),%r11d
     +0x878: movzbl  -0xc(%rcx),%r15d
     +0x87d: mov     $0x2,%sil
     +0x880: sub     -0x8(%rcx),%sil
     +0x884: movzbl  -0x4(%rcx),%edi
     +0x888: movzbl  (%rcx),%edx
     +0x88b: shl     $0x3,%r10b
     +0x88f: mov     $0x10,%r12b
     +0x892: sub     %r10b,%r12b
     +0x895: or      %r8b,%r12b
     +0x898: mov     %r9d,%r8d
     +0x89b: shl     $0x6,%r8b
     +0x89f: or      %r12b,%r8b
     +0x8a2: mov     %r8b,-0x2(%rbx,%rax,1)
     +0x8a7: shr     $0x2,%r9b
     +0x8ab: add     %r11b,%r11b
     +0x8ae: mov     $0x4,%r8b
     +0x8b1: sub     %r11b,%r8b
     +0x8b4: or      %r9b,%r8b
     +0x8b7: shl     $0x4,%r15b
     +0x8bb: mov     $0x20,%r9b
     +0x8be: sub     %r15b,%r9b
     +0x8c1: mov     %esi,%r10d
     +0x8c4: shl     $0x7,%r10b
     +0x8c8: or      %r9b,%r10b
     +0x8cb: or      %r8b,%r10b
     +0x8ce: mov     %r10b,-0x1(%rbx,%rax,1)
     +0x8d3: shr     $1,%sil
     +0x8d6: shl     $0x2,%dil
     +0x8da: mov     $0x8,%r8b
     +0x8dd: sub     %dil,%r8b
     +0x8e0: or      %sil,%r8b
     +0x8e3: shl     $0x5,%dl
     +0x8e6: mov     $0x40,%sil
     +0x8e9: sub     %dl,%sil
     +0x8ec: or      %r8b,%sil
     +0x8ef: mov     %sil,(%rbx,%rax,1)
     +0x8f3: add     $0x3,%rax
     +0x8f7: add     $0x20,%rcx
     +0x8fb: cmp     $0x202,%rax
     +0x901: jne     <mldsa44_keypair_internal+0x860>
     +0x907: movq    $0x0,0x10(%rsp)
     +0x910: lea     0x10(%rsp),%rax
     +0x915: lea     0x1e0(%rsp),%r12
     +0x91d: mov     %r12,%rdi
     +0x920: call    <mldsa_poly_ntt>
     +0x925: lea     0x5e0(%rsp),%rdi
     +0x92d: call    <mldsa_poly_ntt>
     +0x932: lea     0x9e0(%rsp),%rdi
     +0x93a: call    <mldsa_poly_ntt>
     +0x93f: mov     %r13,%rdi
     +0x942: call    <mldsa_poly_ntt>
     +0x947: movaps  0x160(%rsp),%xmm0
     +0x94f: movaps  0x170(%rsp),%xmm1
     +0x957: movups  %xmm1,0x10(%r14)
     +0x95c: movups  %xmm0,(%r14)
     +0x960: lea     0x20(%r14),%rdi
     +0x964: lea     0x380(%rbx),%rsi
     +0x96b: lea     0x160(%rsp),%r15
     +0x973: mov     %r12,%rdx
     +0x976: lea     0x200(%rbx),%rcx
     +0x97d: mov     %r15,%r8
     +0x980: call    <mld_compute_pack_t0_t144>
     +0x985: xorps   %xmm0,%xmm0
     +0x988: movups  %xmm0,0xcc(%rsp)
     +0x990: movaps  %xmm0,0xc0(%rsp)
     +0x998: movaps  %xmm0,0xb0(%rsp)
     +0x9a0: movaps  %xmm0,0xa0(%rsp)
     +0x9a8: movaps  %xmm0,0x90(%rsp)
     +0x9b0: movaps  %xmm0,0x80(%rsp)
     +0x9b8: movaps  %xmm0,0x70(%rsp)
     +0x9bd: movaps  %xmm0,0x60(%rsp)
     +0x9c2: movaps  %xmm0,0x50(%rsp)
     +0x9c7: movaps  %xmm0,0x40(%rsp)
     +0x9cc: movaps  %xmm0,0x30(%rsp)
     +0x9d1: movaps  %xmm0,0x20(%rsp)
     +0x9d6: movaps  %xmm0,0x10(%rsp)
     +0x9db: movups  (%r14),%xmm0
     +0x9df: movups  0x10(%r14),%xmm1
     +0x9e4: movaps  %xmm0,0x10(%rsp)
     +0x9e9: movaps  %xmm1,0x20(%rsp)
     +0x9ee: movups  0x20(%r14),%xmm0
     +0x9f3: movups  0x30(%r14),%xmm1
     +0x9f8: movaps  %xmm0,0x30(%rsp)
     +0x9fd: movaps  %xmm1,0x40(%rsp)
     +0xa02: movups  0x40(%r14),%xmm0
     +0xa07: movups  0x50(%r14),%xmm1
     +0xa0c: xorps   0x50(%rsp),%xmm0
     +0xa11: xorps   0x60(%rsp),%xmm1
     +0xa16: movaps  %xmm0,0x50(%rsp)
     +0xa1b: movaps  %xmm1,0x60(%rsp)
     +0xa20: movups  0x60(%r14),%xmm0
     +0xa25: movups  0x70(%r14),%xmm1
     +0xa2a: xorps   0x70(%rsp),%xmm0
     +0xa2f: xorps   0x80(%rsp),%xmm1
     +0xa37: movaps  %xmm0,0x70(%rsp)
     +0xa3c: movaps  %xmm1,0x80(%rsp)
     +0xa44: mov     0x80(%r14),%rax
     +0xa4b: xor     %rax,0x90(%rsp)
     +0xa53: lea     0x10(%rsp),%r13
     +0xa58: mov     %r13,%rdi
     +0xa5b: call    <mldsa_keccakf1600_permute>
     +0xa60: movups  0x88(%r14),%xmm0
     +0xa68: movups  0x98(%r14),%xmm1
     +0xa70: xorps   0x10(%rsp),%xmm0
     +0xa75: xorps   0x20(%rsp),%xmm1
     +0xa7a: movaps  %xmm0,0x10(%rsp)
     +0xa7f: movaps  %xmm1,0x20(%rsp)
     +0xa84: movups  0xa8(%r14),%xmm0
     +0xa8c: movups  0xb8(%r14),%xmm1
     +0xa94: xorps   0x30(%rsp),%xmm0
     +0xa99: xorps   0x40(%rsp),%xmm1
     +0xa9e: movaps  %xmm0,0x30(%rsp)
     +0xaa3: movaps  %xmm1,0x40(%rsp)
     +0xaa8: movups  0xc8(%r14),%xmm0
     +0xab0: movups  0xd8(%r14),%xmm1
     +0xab8: xorps   0x50(%rsp),%xmm0
     +0xabd: xorps   0x60(%rsp),%xmm1
     +0xac2: movaps  %xmm0,0x50(%rsp)
     +0xac7: movaps  %xmm1,0x60(%rsp)
     +0xacc: movups  0xe8(%r14),%xmm0
     +0xad4: movups  0xf8(%r14),%xmm1
     +0xadc: xorps   0x70(%rsp),%xmm0
     +0xae1: xorps   0x80(%rsp),%xmm1
     +0xae9: movaps  %xmm0,0x70(%rsp)
     +0xaee: movaps  %xmm1,0x80(%rsp)
     +0xaf6: mov     0x108(%r14),%rax
     +0xafd: xor     %rax,0x90(%rsp)
     +0xb05: mov     %r13,%rdi
     +0xb08: call    <mldsa_keccakf1600_permute>
     +0xb0d: movups  0x110(%r14),%xmm0
     +0xb15: movups  0x120(%r14),%xmm1
     +0xb1d: xorps   0x10(%rsp),%xmm0
     +0xb22: xorps   0x20(%rsp),%xmm1
     +0xb27: movaps  %xmm0,0x10(%rsp)
     +0xb2c: movaps  %xmm1,0x20(%rsp)
     +0xb31: movups  0x130(%r14),%xmm0
     +0xb39: movups  0x140(%r14),%xmm1
     +0xb41: xorps   0x30(%rsp),%xmm0
     +0xb46: xorps   0x40(%rsp),%xmm1
     +0xb4b: movaps  %xmm0,0x30(%rsp)
     +0xb50: movaps  %xmm1,0x40(%rsp)
     +0xb55: movups  0x150(%r14),%xmm0
     +0xb5d: movups  0x160(%r14),%xmm1
     +0xb65: xorps   0x50(%rsp),%xmm0
     +0xb6a: xorps   0x60(%rsp),%xmm1
     +0xb6f: movaps  %xmm0,0x50(%rsp)
     +0xb74: movaps  %xmm1,0x60(%rsp)
     +0xb79: movups  0x170(%r14),%xmm0
     +0xb81: movups  0x180(%r14),%xmm1
     +0xb89: xorps   0x70(%rsp),%xmm0
     +0xb8e: xorps   0x80(%rsp),%xmm1
     +0xb96: movaps  %xmm0,0x70(%rsp)
     +0xb9b: movaps  %xmm1,0x80(%rsp)
     +0xba3: mov     0x190(%r14),%rax
     +0xbaa: xor     %rax,0x90(%rsp)
     +0xbb2: mov     %r13,%rdi
     +0xbb5: call    <mldsa_keccakf1600_permute>
     +0xbba: movups  0x198(%r14),%xmm0
     +0xbc2: movups  0x1a8(%r14),%xmm1
     +0xbca: xorps   0x10(%rsp),%xmm0
     +0xbcf: xorps   0x20(%rsp),%xmm1
     +0xbd4: movaps  %xmm0,0x10(%rsp)
     +0xbd9: movaps  %xmm1,0x20(%rsp)
     +0xbde: movups  0x1b8(%r14),%xmm0
     +0xbe6: movups  0x1c8(%r14),%xmm1
     +0xbee: xorps   0x30(%rsp),%xmm0
     +0xbf3: xorps   0x40(%rsp),%xmm1
     +0xbf8: movaps  %xmm0,0x30(%rsp)
     +0xbfd: movaps  %xmm1,0x40(%rsp)
     +0xc02: movups  0x1d8(%r14),%xmm0
     +0xc0a: movups  0x1e8(%r14),%xmm1
     +0xc12: xorps   0x50(%rsp),%xmm0
     +0xc17: xorps   0x60(%rsp),%xmm1
     +0xc1c: movaps  %xmm0,0x50(%rsp)
     +0xc21: movaps  %xmm1,0x60(%rsp)
     +0xc26: movups  0x1f8(%r14),%xmm0
     +0xc2e: movups  0x208(%r14),%xmm1
     +0xc36: xorps   0x70(%rsp),%xmm0
     +0xc3b: xorps   0x80(%rsp),%xmm1
     +0xc43: movaps  %xmm0,0x70(%rsp)
     +0xc48: movaps  %xmm1,0x80(%rsp)
     +0xc50: mov     0x218(%r14),%rax
     +0xc57: xor     %rax,0x90(%rsp)
     +0xc5f: mov     %r13,%rdi
     +0xc62: call    <mldsa_keccakf1600_permute>
     +0xc67: movups  0x220(%r14),%xmm0
     +0xc6f: movups  0x230(%r14),%xmm1
     +0xc77: xorps   0x10(%rsp),%xmm0
     +0xc7c: xorps   0x20(%rsp),%xmm1
     +0xc81: movaps  %xmm0,0x10(%rsp)
     +0xc86: movaps  %xmm1,0x20(%rsp)
     +0xc8b: movups  0x240(%r14),%xmm0
     +0xc93: movups  0x250(%r14),%xmm1
     +0xc9b: xorps   0x30(%rsp),%xmm0
     +0xca0: xorps   0x40(%rsp),%xmm1
     +0xca5: movaps  %xmm0,0x30(%rsp)
     +0xcaa: movaps  %xmm1,0x40(%rsp)
     +0xcaf: movups  0x260(%r14),%xmm0
     +0xcb7: movups  0x270(%r14),%xmm1
     +0xcbf: xorps   0x50(%rsp),%xmm0
     +0xcc4: xorps   0x60(%rsp),%xmm1
     +0xcc9: movaps  %xmm0,0x50(%rsp)
     +0xcce: movaps  %xmm1,0x60(%rsp)
     +0xcd3: movups  0x280(%r14),%xmm0
     +0xcdb: movups  0x290(%r14),%xmm1
     +0xce3: xorps   0x70(%rsp),%xmm0
     +0xce8: xorps   0x80(%rsp),%xmm1
     +0xcf0: movaps  %xmm0,0x70(%rsp)
     +0xcf5: movaps  %xmm1,0x80(%rsp)
     +0xcfd: mov     0x2a0(%r14),%rax
     +0xd04: xor     %rax,0x90(%rsp)
     +0xd0c: mov     %r13,%rdi
     +0xd0f: call    <mldsa_keccakf1600_permute>
     +0xd14: movups  0x2a8(%r14),%xmm0
     +0xd1c: movups  0x2b8(%r14),%xmm1
     +0xd24: xorps   0x10(%rsp),%xmm0
     +0xd29: xorps   0x20(%rsp),%xmm1
     +0xd2e: movaps  %xmm0,0x10(%rsp)
     +0xd33: movaps  %xmm1,0x20(%rsp)
     +0xd38: movups  0x2c8(%r14),%xmm0
     +0xd40: movups  0x2d8(%r14),%xmm1
     +0xd48: xorps   0x30(%rsp),%xmm0
     +0xd4d: xorps   0x40(%rsp),%xmm1
     +0xd52: movaps  %xmm0,0x30(%rsp)
     +0xd57: movaps  %xmm1,0x40(%rsp)
     +0xd5c: movups  0x2e8(%r14),%xmm0
     +0xd64: movups  0x2f8(%r14),%xmm1
     +0xd6c: xorps   0x50(%rsp),%xmm0
     +0xd71: xorps   0x60(%rsp),%xmm1
     +0xd76: movaps  %xmm0,0x50(%rsp)
     +0xd7b: movaps  %xmm1,0x60(%rsp)
     +0xd80: movups  0x308(%r14),%xmm0
     +0xd88: movups  0x318(%r14),%xmm1
     +0xd90: xorps   0x70(%rsp),%xmm0
     +0xd95: xorps   0x80(%rsp),%xmm1
     +0xd9d: movaps  %xmm0,0x70(%rsp)
     +0xda2: movaps  %xmm1,0x80(%rsp)
     +0xdaa: mov     0x328(%r14),%rax
     +0xdb1: xor     %rax,0x90(%rsp)
     +0xdb9: mov     %r13,%rdi
     +0xdbc: call    <mldsa_keccakf1600_permute>
     +0xdc1: movups  0x330(%r14),%xmm0
     +0xdc9: movups  0x340(%r14),%xmm1
     +0xdd1: xorps   0x10(%rsp),%xmm0
     +0xdd6: xorps   0x20(%rsp),%xmm1
     +0xddb: movaps  %xmm0,0x10(%rsp)
     +0xde0: movaps  %xmm1,0x20(%rsp)
     +0xde5: movups  0x350(%r14),%xmm0
     +0xded: movups  0x360(%r14),%xmm1
     +0xdf5: xorps   0x30(%rsp),%xmm0
     +0xdfa: xorps   0x40(%rsp),%xmm1
     +0xdff: movaps  %xmm0,0x30(%rsp)
     +0xe04: movaps  %xmm1,0x40(%rsp)
     +0xe09: movups  0x370(%r14),%xmm0
     +0xe11: movups  0x380(%r14),%xmm1
     +0xe19: xorps   0x50(%rsp),%xmm0
     +0xe1e: xorps   0x60(%rsp),%xmm1
     +0xe23: movaps  %xmm0,0x50(%rsp)
     +0xe28: movaps  %xmm1,0x60(%rsp)
     +0xe2d: movups  0x390(%r14),%xmm0
     +0xe35: movups  0x3a0(%r14),%xmm1
     +0xe3d: xorps   0x70(%rsp),%xmm0
     +0xe42: xorps   0x80(%rsp),%xmm1
     +0xe4a: movaps  %xmm0,0x70(%rsp)
     +0xe4f: movaps  %xmm1,0x80(%rsp)
     +0xe57: mov     0x3b0(%r14),%rax
     +0xe5e: xor     %rax,0x90(%rsp)
     +0xe66: mov     %r13,%rdi
     +0xe69: call    <mldsa_keccakf1600_permute>
     +0xe6e: movups  0x3b8(%r14),%xmm0
     +0xe76: movups  0x3c8(%r14),%xmm1
     +0xe7e: xorps   0x10(%rsp),%xmm0
     +0xe83: xorps   0x20(%rsp),%xmm1
     +0xe88: movaps  %xmm0,0x10(%rsp)
     +0xe8d: movaps  %xmm1,0x20(%rsp)
     +0xe92: movups  0x3d8(%r14),%xmm0
     +0xe9a: movups  0x3e8(%r14),%xmm1
     +0xea2: xorps   0x30(%rsp),%xmm0
     +0xea7: xorps   0x40(%rsp),%xmm1
     +0xeac: movaps  %xmm0,0x30(%rsp)
     +0xeb1: movaps  %xmm1,0x40(%rsp)
     +0xeb6: movups  0x3f8(%r14),%xmm0
     +0xebe: movups  0x408(%r14),%xmm1
     +0xec6: xorps   0x50(%rsp),%xmm0
     +0xecb: xorps   0x60(%rsp),%xmm1
     +0xed0: movaps  %xmm0,0x50(%rsp)
     +0xed5: movaps  %xmm1,0x60(%rsp)
     +0xeda: movups  0x418(%r14),%xmm0
     +0xee2: movups  0x428(%r14),%xmm1
     +0xeea: xorps   0x70(%rsp),%xmm0
     +0xeef: xorps   0x80(%rsp),%xmm1
     +0xef7: movaps  %xmm0,0x70(%rsp)
     +0xefc: movaps  %xmm1,0x80(%rsp)
     +0xf04: mov     0x438(%r14),%rax
     +0xf0b: xor     %rax,0x90(%rsp)
     +0xf13: mov     %r13,%rdi
     +0xf16: call    <mldsa_keccakf1600_permute>
     +0xf1b: movups  0x440(%r14),%xmm0
     +0xf23: movups  0x450(%r14),%xmm1
     +0xf2b: xorps   0x10(%rsp),%xmm0
     +0xf30: xorps   0x20(%rsp),%xmm1
     +0xf35: movaps  %xmm0,0x10(%rsp)
     +0xf3a: movaps  %xmm1,0x20(%rsp)
     +0xf3f: movups  0x460(%r14),%xmm0
     +0xf47: movups  0x470(%r14),%xmm1
     +0xf4f: xorps   0x30(%rsp),%xmm0
     +0xf54: xorps   0x40(%rsp),%xmm1
     +0xf59: movaps  %xmm0,0x30(%rsp)
     +0xf5e: movaps  %xmm1,0x40(%rsp)
     +0xf63: movups  0x480(%r14),%xmm0
     +0xf6b: movups  0x490(%r14),%xmm1
     +0xf73: xorps   0x50(%rsp),%xmm0
     +0xf78: xorps   0x60(%rsp),%xmm1
     +0xf7d: movaps  %xmm0,0x50(%rsp)
     +0xf82: movaps  %xmm1,0x60(%rsp)
     +0xf87: movups  0x4a0(%r14),%xmm0
     +0xf8f: movups  0x4b0(%r14),%xmm1
     +0xf97: xorps   0x70(%rsp),%xmm0
     +0xf9c: xorps   0x80(%rsp),%xmm1
     +0xfa4: movaps  %xmm0,0x70(%rsp)
     +0xfa9: movaps  %xmm1,0x80(%rsp)
     +0xfb1: mov     0x4c0(%r14),%rax
     +0xfb8: xor     %rax,0x90(%rsp)
     +0xfc0: mov     %r13,%rdi
     +0xfc3: call    <mldsa_keccakf1600_permute>
     +0xfc8: mov     0x4c8(%r14),%rax
     +0xfcf: mov     0x4d0(%r14),%rcx
     +0xfd6: xor     %rax,0x10(%rsp)
     +0xfdb: xor     %rcx,0x18(%rsp)
     +0xfe0: mov     0x4d8(%r14),%rax
     +0xfe7: mov     0x4e0(%r14),%rcx
     +0xfee: xor     %rax,0x20(%rsp)
     +0xff3: xor     %rcx,0x28(%rsp)
     +0xff8: mov     0x4e8(%r14),%rax
     +0xfff: mov     0x4f0(%r14),%rcx
    +0x1006: xor     %rax,0x30(%rsp)
    +0x100b: xor     %rcx,0x38(%rsp)
    +0x1010: mov     0x4f8(%r14),%rax
    +0x1017: mov     0x500(%r14),%rcx
    +0x101e: xor     %rax,0x40(%rsp)
    +0x1023: xor     %rcx,0x48(%rsp)
    +0x1028: mov     0x508(%r14),%rax
    +0x102f: mov     0x510(%r14),%rcx
    +0x1036: xor     %rax,0x50(%rsp)
    +0x103b: xor     %rcx,0x58(%rsp)
    +0x1040: mov     0x518(%r14),%rax
    +0x1047: xor     %rax,0x60(%rsp)
    +0x104c: xorb    $0x1f,0x68(%rsp)
    +0x1051: xorb    $0x80,0x97(%rsp)
    +0x1059: movl    $0x88,0xd8(%rsp)
    +0x1064: mov     %r13,%rdi
    +0x1067: call    <mldsa_keccakf1600_permute>
    +0x106c: movaps  0x10(%rsp),%xmm0
    +0x1071: movaps  0x20(%rsp),%xmm1
    +0x1076: movaps  0x30(%rsp),%xmm2
    +0x107b: movaps  0x40(%rsp),%xmm3
    +0x1080: movaps  %xmm3,0x150(%rsp)
    +0x1088: movaps  %xmm2,0x140(%rsp)
    +0x1090: movaps  %xmm1,0x130(%rsp)
    +0x1098: movaps  %xmm0,0x120(%rsp)
    +0x10a0: xorps   %xmm0,%xmm0
    +0x10a3: movaps  %xmm0,0x50(%rsp)
    +0x10a8: movaps  %xmm0,0x60(%rsp)
    +0x10ad: movaps  %xmm0,0x70(%rsp)
    +0x10b2: movaps  %xmm0,0x80(%rsp)
    +0x10ba: movaps  %xmm0,0x90(%rsp)
    +0x10c2: movaps  %xmm0,0xa0(%rsp)
    +0x10ca: movaps  %xmm0,0xb0(%rsp)
    +0x10d2: movaps  %xmm0,0xc0(%rsp)
    +0x10da: movaps  %xmm0,0xd0(%rsp)
    +0x10e2: movaps  %xmm0,0x10(%rsp)
    +0x10e7: movaps  %xmm0,0x20(%rsp)
    +0x10ec: movaps  %xmm0,0x30(%rsp)
    +0x10f1: movaps  %xmm0,0x40(%rsp)
    +0x10f6: movaps  0x160(%rsp),%xmm0
    +0x10fe: movaps  0x170(%rsp),%xmm1
    +0x1106: movups  %xmm1,0x10(%rbx)
    +0x110a: movups  %xmm0,(%rbx)
    +0x110d: movaps  0x1c0(%rsp),%xmm0
    +0x1115: movaps  0x1d0(%rsp),%xmm1
    +0x111d: movups  %xmm1,0x30(%rbx)
    +0x1121: movups  %xmm0,0x20(%rbx)
    +0x1125: movaps  0x120(%rsp),%xmm0
    +0x112d: movaps  0x130(%rsp),%xmm1
    +0x1135: movaps  0x140(%rsp),%xmm2
    +0x113d: movaps  0x150(%rsp),%xmm3
    +0x1145: movups  %xmm0,0x40(%rbx)
    +0x1149: movups  %xmm1,0x50(%rbx)
    +0x114d: movups  %xmm2,0x60(%rbx)
    +0x1151: movups  %xmm3,0x70(%rbx)
    +0x1155: mov     $0x1000,%edx
    +0x115a: mov     %r12,%rdi
    +0x115d: xor     %esi,%esi
    +0x115f: call    <memset>
    +0x1164: xorps   %xmm0,%xmm0
    +0x1167: movaps  %xmm0,0x150(%rsp)
    +0x116f: movaps  %xmm0,0x140(%rsp)
    +0x1177: movaps  %xmm0,0x130(%rsp)
    +0x117f: movaps  %xmm0,0x120(%rsp)
    +0x1187: lea     0x120(%rsp),%rax
    +0x118f: movaps  %xmm0,0xf0(%rsp)
    +0x1197: movaps  %xmm0,0xe0(%rsp)
    +0x119f: movw    $0x0,0x100(%rsp)
    +0x11a9: lea     0xe0(%rsp),%rax
    +0x11b1: movaps  %xmm0,0x1d0(%rsp)
    +0x11b9: movaps  %xmm0,0x1c0(%rsp)
    +0x11c1: movaps  %xmm0,0x1b0(%rsp)
    +0x11c9: movaps  %xmm0,0x1a0(%rsp)
    +0x11d1: movaps  %xmm0,0x190(%rsp)
    +0x11d9: movaps  %xmm0,0x180(%rsp)
    +0x11e1: movaps  %xmm0,0x170(%rsp)
    +0x11e9: movaps  %xmm0,0x160(%rsp)
    +0x11f1: xor     %eax,%eax
    +0x11f3: lea     -0x28(%rbp),%rsp
    +0x11f7: pop     %rbx
    +0x11f8: pop     %r12
    +0x11fa: pop     %r13
    +0x11fc: pop     %r14
    +0x11fe: pop     %r15
    +0x1200: pop     %rbp
    +0x1201: xor     %ecx,%ecx
    +0x1203: xor     %edi,%edi
    +0x1205: xor     %edx,%edx
    +0x1207: xor     %esi,%esi
    +0x1209: xor     %r8d,%r8d
    +0x120c: xor     %r9d,%r9d
    +0x120f: xor     %r10d,%r10d
    +0x1212: xor     %r11d,%r11d
    +0x1215: ret     
 ***)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_keypair_internal";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. From the seed SEED (32 bytes at seed), the public key at pk  *)
(* (1312 bytes) becomes mld_keypair_pk_44 SEED and the secret key at sk      *)
(* (2560 bytes) mld_keypair_sk_44 SEED, and the result is 0. The stack is    *)
(* the 9596 bytes below the return address: the six saved registers, up to   *)
(* 31 bytes of realignment, the frame of 4608 bytes and the 4909 bytes of    *)
(* the call of mld_compute_pack_t0_t144, the deepest callee.                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !pk sk seed SEED pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 (mld_keypair_rho 4 4 SEED) /\
        mld_keypair_terminates_44 SEED /\
        PAIRWISE nonoverlapping
         [(pk,1312); (sk,2560);
          (word_sub stackpointer (word 9596),9596)] /\
        ALLPAIRS nonoverlapping
         [(pk,1312); (sk,2560);
          (word_sub stackpointer (word 9596),9596)]
         [(seed,32); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pk,1312); (sk,2560)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa44_keypair_internal) /\
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
                  (!j. j < 1312
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           mld_keypair_pk_44 SEED j) /\
                  (!j. j < 2560
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           mld_keypair_sk_44 SEED j))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,1312); memory :> bytes(sk,2560);
                memory :> bytes(word_sub stackpointer (word 9596),9596)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, whether each nibble read by  *)
(* the sampling of each polynomial is accepted (mld_keypair_declass_44) and  *)
(* the stack, with all accesses within the arguments, the stack, the return  *)
(* address and the constants of the function and of the callees, and the     *)
(* writes within the keys and the stack.                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e pk sk seed SEED pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 (mld_keypair_rho 4 4 SEED) /\
        mld_keypair_terminates_44 SEED /\
        PAIRWISE nonoverlapping
         [(pk,1312); (sk,2560);
          (word_sub stackpointer (word 9596),9596)] /\
        ALLPAIRS nonoverlapping
         [(pk,1312); (sk,2560);
          (word_sub stackpointer (word 9596),9596)]
         [(seed,32); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pk,1312); (sk,2560)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa44_keypair_internal) /\
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
                  (!j. j < 1312
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           mld_keypair_pk_44 SEED j) /\
                  (!j. j < 2560
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           mld_keypair_sk_44 SEED j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events pk sk seed (mld_keypair_rho 4 4 SEED)
                           (mld_keypair_declass_44 SEED) mf mc pc
                           (word_sub stackpointer (word 9596))
                           returnaddress /\
                     memaccess_inbounds e2
                      [seed,32; pk,1312; sk,2560;
                       word_sub stackpointer (word 9596),9596;
                       stackpointer,8; word(pc + got_memset),8;
                       word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_ntt_consts),256;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word(pc + mld_compute_pack_t0_t144_consts),64;
                       word(pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32]
                      [pk,1312; sk,2560;
                       word_sub stackpointer (word 9596),9596]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,1312); memory :> bytes(sk,2560);
                memory :> bytes(word_sub stackpointer (word 9596),9596)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e pk sk seed SEED pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 (mld_keypair_rho 4 4 SEED) /\
        mld_keypair_terminates_44 SEED /\
        PAIRWISE nonoverlapping
         [(pk,1312); (sk,2560);
          (word_sub stackpointer (word 9596),9596)] /\
        ALLPAIRS nonoverlapping
         [(pk,1312); (sk,2560);
          (word_sub stackpointer (word 9596),9596)]
         [(seed,32); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        ALL (nonoverlapping (stackpointer,8)) [(pk,1312); (sk,2560)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa44_keypair_internal) /\
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
                     e2 = f_events pk sk seed (mld_keypair_rho 4 4 SEED)
                           (mld_keypair_declass_44 SEED) mf mc pc
                           (word_sub stackpointer (word 9596))
                           returnaddress /\
                     memaccess_inbounds e2
                      [seed,32; pk,1312; sk,2560;
                       word_sub stackpointer (word 9596),9596;
                       stackpointer,8; word(pc + got_memset),8;
                       word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_ntt_consts),256;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word(pc + mld_compute_pack_t0_t144_consts),64;
                       word(pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32]
                      [pk,1312; sk,2560;
                       word_sub stackpointer (word 9596),9596]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,1312); memory :> bytes(sk,2560);
                memory :> bytes(word_sub stackpointer (word 9596),9596)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
