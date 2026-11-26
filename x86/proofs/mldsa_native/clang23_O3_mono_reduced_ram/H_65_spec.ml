(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 of up to three inputs: the statement. This is the code for       *)
(* mld_H65 (mld_H in sign.c, for ML-DSA-65) from mldsa-native's portable C   *)
(* implementation compiled by clang 23 with -O3 as a monolithic build with   *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). Clang inlined the     *)
(* SHAKE256 functions: the function zeroes a Keccak state on its stack,      *)
(* absorbs in1, and in2 and in3 unless their lengths are zero, with vector   *)
(* and scalar loops and calls of mldsa_keccakf1600_permute, finalizes,       *)
(* squeezes the output block by block with calls of                          *)
(* mldsa_keccakf1600_permute and memcpy, and zeroes the state. It is         *)
(* verified in the whole image (see libmldsa.ml) against mld_shake256_byte   *)
(* of common/mldsa_native_fips202.ml for the concatenation of the three      *)
(* inputs; the inputs and the output may overlap, and a pointer with a zero  *)
(* length may be anything (NULL), except that in1len must not be zero: the   *)
(* code for the first input skips the test for an empty input when the input *)
(* is shorter than a block (presumably because all callers pass a nonzero    *)
(* constant in1len), and for in1len = 0 it does not terminate. It is also    *)
(* shown to be constant time and memory safe.                                *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mld_H65:
       +0x0: push    %rbp
       +0x1: push    %r15
       +0x3: push    %r14
       +0x5: push    %r13
       +0x7: push    %r12
       +0x9: push    %rbx
       +0xa: sub     $0xe8,%rsp
      +0x11: mov     %r9,%r12
      +0x14: mov     %r8,%r13
      +0x17: mov     %rcx,%r15
      +0x1a: mov     %rdx,%rbp
      +0x1d: mov     %rsi,%rbx
      +0x20: mov     %rdi,0x8(%rsp)
      +0x25: xorps   %xmm0,%xmm0
      +0x28: movups  %xmm0,0xcc(%rsp)
      +0x30: movaps  %xmm0,0xc0(%rsp)
      +0x38: movaps  %xmm0,0xb0(%rsp)
      +0x40: movaps  %xmm0,0xa0(%rsp)
      +0x48: movaps  %xmm0,0x90(%rsp)
      +0x50: movaps  %xmm0,0x80(%rsp)
      +0x58: movaps  %xmm0,0x70(%rsp)
      +0x5d: movaps  %xmm0,0x60(%rsp)
      +0x62: movaps  %xmm0,0x50(%rsp)
      +0x67: movaps  %xmm0,0x40(%rsp)
      +0x6c: movaps  %xmm0,0x30(%rsp)
      +0x71: movaps  %xmm0,0x20(%rsp)
      +0x76: movaps  %xmm0,0x10(%rsp)
      +0x7b: cmp     $0x88,%rcx
      +0x82: jb      <mld_H65+0x141>
      +0x88: lea     0x10(%rsp),%r14
      +0x8d: nopl    (%rax)
      +0x90: movups  0x0(%rbp),%xmm0
      +0x94: movups  0x10(%rbp),%xmm1
      +0x98: xorps   0x10(%rsp),%xmm0
      +0x9d: xorps   0x20(%rsp),%xmm1
      +0xa2: movaps  %xmm0,0x10(%rsp)
      +0xa7: movaps  %xmm1,0x20(%rsp)
      +0xac: movups  0x20(%rbp),%xmm0
      +0xb0: movups  0x30(%rbp),%xmm1
      +0xb4: xorps   0x30(%rsp),%xmm0
      +0xb9: xorps   0x40(%rsp),%xmm1
      +0xbe: movaps  %xmm0,0x30(%rsp)
      +0xc3: movaps  %xmm1,0x40(%rsp)
      +0xc8: movups  0x40(%rbp),%xmm0
      +0xcc: movups  0x50(%rbp),%xmm1
      +0xd0: xorps   0x50(%rsp),%xmm0
      +0xd5: xorps   0x60(%rsp),%xmm1
      +0xda: movaps  %xmm0,0x50(%rsp)
      +0xdf: movaps  %xmm1,0x60(%rsp)
      +0xe4: movups  0x60(%rbp),%xmm0
      +0xe8: movups  0x70(%rbp),%xmm1
      +0xec: xorps   0x70(%rsp),%xmm0
      +0xf1: xorps   0x80(%rsp),%xmm1
      +0xf9: movaps  %xmm0,0x70(%rsp)
      +0xfe: movaps  %xmm1,0x80(%rsp)
     +0x106: mov     0x80(%rbp),%rax
     +0x10d: xor     %rax,0x90(%rsp)
     +0x115: add     $0xffffffffffffff78,%r15
     +0x11c: add     $0x88,%rbp
     +0x123: mov     %r14,%rdi
     +0x126: call    <mldsa_keccakf1600_permute>
     +0x12b: cmp     $0x87,%r15
     +0x132: ja      <mld_H65+0x90>
     +0x138: test    %r15,%r15
     +0x13b: je      <mld_H65+0x1dc>
     +0x141: cmp     $0x4,%r15
     +0x145: jb      <mld_H65+0x168>
     +0x147: lea     (%rsp,%r15,1),%rax
     +0x14b: add     $0x10,%rax
     +0x14f: lea     (%r15,%rbp,1),%rcx
     +0x153: lea     0x10(%rsp),%rdx
     +0x158: cmp     %rcx,%rdx
     +0x15b: setb    %cl
     +0x15e: cmp     %rax,%rbp
     +0x161: setb    %al
     +0x164: test    %al,%cl
     +0x166: je      <mld_H65+0x1d2>
     +0x168: xor     %eax,%eax
     +0x16a: mov     %r15,%rdx
     +0x16d: mov     %rax,%rcx
     +0x170: and     $0x3,%rdx
     +0x174: je      <mld_H65+0x192>
     +0x176: mov     %rax,%rcx
     +0x179: nopl    0x0(%rax)
     +0x180: movzbl  0x0(%rbp,%rcx,1),%esi
     +0x185: xor     %sil,0x10(%rsp,%rcx,1)
     +0x18a: inc     %rcx
     +0x18d: dec     %rdx
     +0x190: jne     <mld_H65+0x180>
     +0x192: sub     %r15,%rax
     +0x195: cmp     $0xfffffffffffffffc,%rax
     +0x199: ja      <mld_H65+0x25a>
     +0x19f: nop     
     +0x1a0: movzbl  0x0(%rbp,%rcx,1),%eax
     +0x1a5: xor     %al,0x10(%rsp,%rcx,1)
     +0x1a9: movzbl  0x1(%rbp,%rcx,1),%eax
     +0x1ae: xor     %al,0x11(%rsp,%rcx,1)
     +0x1b2: movzbl  0x2(%rbp,%rcx,1),%eax
     +0x1b7: xor     %al,0x12(%rsp,%rcx,1)
     +0x1bb: movzbl  0x3(%rbp,%rcx,1),%eax
     +0x1c0: xor     %al,0x13(%rsp,%rcx,1)
     +0x1c4: add     $0x4,%rcx
     +0x1c8: cmp     %rcx,%r15
     +0x1cb: jne     <mld_H65+0x1a0>
     +0x1cd: jmp     <mld_H65+0x25a>
     +0x1d2: cmp     $0x20,%r15
     +0x1d6: jae     <mld_H65+0x1e1>
     +0x1d8: xor     %eax,%eax
     +0x1da: jmp     <mld_H65+0x226>
     +0x1dc: xor     %r15d,%r15d
     +0x1df: jmp     <mld_H65+0x25a>
     +0x1e1: mov     %r15d,%eax
     +0x1e4: and     $0xe0,%eax
     +0x1e9: xor     %ecx,%ecx
     +0x1eb: nopl    0x0(%rax,%rax,1)
     +0x1f0: movups  0x0(%rbp,%rcx,1),%xmm0
     +0x1f5: movups  0x10(%rbp,%rcx,1),%xmm1
     +0x1fa: xorps   0x10(%rsp,%rcx,1),%xmm0
     +0x1ff: xorps   0x20(%rsp,%rcx,1),%xmm1
     +0x204: movaps  %xmm0,0x10(%rsp,%rcx,1)
     +0x209: movaps  %xmm1,0x20(%rsp,%rcx,1)
     +0x20e: add     $0x20,%rcx
     +0x212: cmp     %rcx,%rax
     +0x215: jne     <mld_H65+0x1f0>
     +0x217: cmp     %rax,%r15
     +0x21a: je      <mld_H65+0x25a>
     +0x21c: test    $0x1c,%r15b
     +0x220: je      <mld_H65+0x16a>
     +0x226: mov     %rax,%rcx
     +0x229: mov     %r15d,%eax
     +0x22c: and     $0xfc,%eax
     +0x231: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x240: mov     0x0(%rbp,%rcx,1),%edx
     +0x244: xor     %edx,0x10(%rsp,%rcx,1)
     +0x248: add     $0x4,%rcx
     +0x24c: cmp     %rcx,%rax
     +0x24f: jne     <mld_H65+0x240>
     +0x251: cmp     %rax,%r15
     +0x254: jne     <mld_H65+0x16a>
     +0x25a: mov     0x128(%rsp),%r14
     +0x262: mov     %r15d,0xd8(%rsp)
     +0x26a: test    %r12,%r12
     +0x26d: mov     0x8(%rsp),%rbp
     +0x272: je      <mld_H65+0x551>
     +0x278: mov     $0x88,%eax
     +0x27d: sub     %r15,%rax
     +0x280: cmp     %rax,%r12
     +0x283: jae     <mld_H65+0x292>
     +0x285: lea     (%rsp,%r15,1),%rbp
     +0x289: add     $0x10,%rbp
     +0x28d: jmp     <mld_H65+0x4b3>
     +0x292: lea     0x10(%rsp),%rbp
     +0x297: jmp     <mld_H65+0x2c6>
     +0x299: nopl    0x0(%rax)
     +0x2a0: sub     %rax,%r12
     +0x2a3: add     %rax,%r13
     +0x2a6: mov     %rbp,%rdi
     +0x2a9: call    <mldsa_keccakf1600_permute>
     +0x2ae: mov     $0x88,%eax
     +0x2b3: mov     $0x0,%r15d
     +0x2b9: cmp     $0x87,%r12
     +0x2c0: jbe     <mld_H65+0x4a7>
     +0x2c6: lea     (%rsp,%r15,1),%rcx
     +0x2ca: add     $0x10,%rcx
     +0x2ce: cmp     $0x4,%rax
     +0x2d2: jae     <mld_H65+0x2e0>
     +0x2d4: xor     %edx,%edx
     +0x2d6: jmp     <mld_H65+0x490>
     +0x2db: nopl    0x0(%rax,%rax,1)
     +0x2e0: cmp     $0x20,%rax
     +0x2e4: jae     <mld_H65+0x2f0>
     +0x2e6: xor     %edx,%edx
     +0x2e8: jmp     <mld_H65+0x45d>
     +0x2ed: nopl    (%rax)
     +0x2f0: mov     %eax,%edx
     +0x2f2: and     $0xe0,%edx
     +0x2f8: movups  0x0(%r13),%xmm0
     +0x2fd: movups  0x10(%r13),%xmm1
     +0x302: movups  (%rcx),%xmm2
     +0x305: xorps   %xmm0,%xmm2
     +0x308: movups  0x10(%rcx),%xmm0
     +0x30c: xorps   %xmm1,%xmm0
     +0x30f: movups  %xmm2,(%rcx)
     +0x312: movups  %xmm0,0x10(%rcx)
     +0x316: cmp     $0x20,%rdx
     +0x31a: je      <mld_H65+0x450>
     +0x320: movups  0x20(%r13),%xmm0
     +0x325: movups  0x30(%r13),%xmm1
     +0x32a: movups  0x20(%rcx),%xmm2
     +0x32e: xorps   %xmm0,%xmm2
     +0x331: movups  0x30(%rcx),%xmm0
     +0x335: xorps   %xmm1,%xmm0
     +0x338: movups  %xmm2,0x20(%rcx)
     +0x33c: movups  %xmm0,0x30(%rcx)
     +0x340: cmp     $0x40,%edx
     +0x343: je      <mld_H65+0x450>
     +0x349: movups  0x40(%r13),%xmm0
     +0x34e: movups  0x50(%r13),%xmm1
     +0x353: movups  0x40(%rcx),%xmm2
     +0x357: xorps   %xmm0,%xmm2
     +0x35a: movups  0x50(%rcx),%xmm0
     +0x35e: xorps   %xmm1,%xmm0
     +0x361: movups  %xmm2,0x40(%rcx)
     +0x365: movups  %xmm0,0x50(%rcx)
     +0x369: cmp     $0x60,%edx
     +0x36c: je      <mld_H65+0x450>
     +0x372: movups  0x60(%r13),%xmm0
     +0x377: movups  0x70(%r13),%xmm1
     +0x37c: movups  0x60(%rcx),%xmm2
     +0x380: xorps   %xmm0,%xmm2
     +0x383: movups  0x70(%rcx),%xmm0
     +0x387: xorps   %xmm1,%xmm0
     +0x38a: movups  %xmm2,0x60(%rcx)
     +0x38e: movups  %xmm0,0x70(%rcx)
     +0x392: cmp     $0x80,%edx
     +0x398: je      <mld_H65+0x450>
     +0x39e: movups  0x80(%r13),%xmm0
     +0x3a6: movups  0x90(%r13),%xmm1
     +0x3ae: movups  0x80(%rcx),%xmm2
     +0x3b5: xorps   %xmm0,%xmm2
     +0x3b8: movups  0x90(%rcx),%xmm0
     +0x3bf: xorps   %xmm1,%xmm0
     +0x3c2: movups  %xmm2,0x80(%rcx)
     +0x3c9: movups  %xmm0,0x90(%rcx)
     +0x3d0: cmp     $0xa0,%edx
     +0x3d6: je      <mld_H65+0x450>
     +0x3d8: movups  0xa0(%r13),%xmm0
     +0x3e0: movups  0xb0(%r13),%xmm1
     +0x3e8: movups  0xa0(%rcx),%xmm2
     +0x3ef: xorps   %xmm0,%xmm2
     +0x3f2: movups  0xb0(%rcx),%xmm0
     +0x3f9: xorps   %xmm1,%xmm0
     +0x3fc: movups  %xmm2,0xa0(%rcx)
     +0x403: movups  %xmm0,0xb0(%rcx)
     +0x40a: cmp     $0xc0,%edx
     +0x410: je      <mld_H65+0x450>
     +0x412: movups  0xc0(%r13),%xmm0
     +0x41a: movups  0xd0(%r13),%xmm1
     +0x422: movups  0xc0(%rcx),%xmm2
     +0x429: xorps   %xmm0,%xmm2
     +0x42c: movups  0xd0(%rcx),%xmm0
     +0x433: xorps   %xmm1,%xmm0
     +0x436: movups  %xmm2,0xc0(%rcx)
     +0x43d: movups  %xmm0,0xd0(%rcx)
     +0x444: data16  data16 cs nopw 0x0(%rax,%rax,1)
     +0x450: cmp     %rdx,%rax
     +0x453: je      <mld_H65+0x2a0>
     +0x459: test    $0x1c,%al
     +0x45b: je      <mld_H65+0x490>
     +0x45d: mov     %rdx,%rsi
     +0x460: mov     %eax,%edx
     +0x462: and     $0xfc,%edx
     +0x468: nopl    0x0(%rax,%rax,1)
     +0x470: mov     0x0(%r13,%rsi,1),%edi
     +0x475: xor     %edi,(%rcx,%rsi,1)
     +0x478: add     $0x4,%rsi
     +0x47c: cmp     %rsi,%rdx
     +0x47f: jne     <mld_H65+0x470>
     +0x481: jmp     <mld_H65+0x49d>
     +0x483: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x490: movzbl  0x0(%r13,%rdx,1),%esi
     +0x496: xor     %sil,(%rcx,%rdx,1)
     +0x49a: inc     %rdx
     +0x49d: cmp     %rdx,%rax
     +0x4a0: jne     <mld_H65+0x490>
     +0x4a2: jmp     <mld_H65+0x2a0>
     +0x4a7: xor     %r15d,%r15d
     +0x4aa: test    %r12,%r12
     +0x4ad: je      <mld_H65+0x544>
     +0x4b3: cmp     $0x4,%r12
     +0x4b7: jb      <mld_H65+0x4d5>
     +0x4b9: lea     (%r12,%rbp,1),%rax
     +0x4bd: lea     (%r12,%r13,1),%rcx
     +0x4c1: cmp     %rcx,%rbp
     +0x4c4: setb    %cl
     +0x4c7: cmp     %rax,%r13
     +0x4ca: setb    %al
     +0x4cd: test    %al,%cl
     +0x4cf: je      <mld_H65+0x896>
     +0x4d5: xor     %eax,%eax
     +0x4d7: mov     %r12,%rdx
     +0x4da: mov     %rax,%rcx
     +0x4dd: and     $0x3,%rdx
     +0x4e1: je      <mld_H65+0x503>
     +0x4e3: mov     %rax,%rcx
     +0x4e6: cs      nopw 0x0(%rax,%rax,1)
     +0x4f0: movzbl  0x0(%r13,%rcx,1),%esi
     +0x4f6: xor     %sil,0x0(%rbp,%rcx,1)
     +0x4fb: inc     %rcx
     +0x4fe: dec     %rdx
     +0x501: jne     <mld_H65+0x4f0>
     +0x503: sub     %r12,%rax
     +0x506: cmp     $0xfffffffffffffffc,%rax
     +0x50a: ja      <mld_H65+0x541>
     +0x50c: nopl    0x0(%rax)
     +0x510: movzbl  0x0(%r13,%rcx,1),%eax
     +0x516: xor     %al,0x0(%rbp,%rcx,1)
     +0x51a: movzbl  0x1(%r13,%rcx,1),%eax
     +0x520: xor     %al,0x1(%rbp,%rcx,1)
     +0x524: movzbl  0x2(%r13,%rcx,1),%eax
     +0x52a: xor     %al,0x2(%rbp,%rcx,1)
     +0x52e: movzbl  0x3(%r13,%rcx,1),%eax
     +0x534: xor     %al,0x3(%rbp,%rcx,1)
     +0x538: add     $0x4,%rcx
     +0x53c: cmp     %rcx,%r12
     +0x53f: jne     <mld_H65+0x510>
     +0x541: add     %r12d,%r15d
     +0x544: mov     %r15d,0xd8(%rsp)
     +0x54c: mov     0x8(%rsp),%rbp
     +0x551: test    %r14,%r14
     +0x554: je      <mld_H65+0x72f>
     +0x55a: mov     0x120(%rsp),%r13
     +0x562: mov     $0x88,%eax
     +0x567: sub     %r15d,%eax
     +0x56a: cmp     %rax,%r14
     +0x56d: jae     <mld_H65+0x57f>
     +0x56f: mov     %r15d,%eax
     +0x572: lea     (%rsp,%rax,1),%r12
     +0x576: add     $0x10,%r12
     +0x57a: jmp     <mld_H65+0x698>
     +0x57f: lea     0x20(%rsp),%rbp
     +0x584: lea     0x10(%rsp),%r12
     +0x589: jmp     <mld_H65+0x5b3>
     +0x58b: nopl    0x0(%rax,%rax,1)
     +0x590: sub     %rax,%r14
     +0x593: add     %rax,%r13
     +0x596: mov     %r12,%rdi
     +0x599: call    <mldsa_keccakf1600_permute>
     +0x59e: xor     %r15d,%r15d
     +0x5a1: mov     $0x88,%eax
     +0x5a6: cmp     $0x87,%r14
     +0x5ad: jbe     <mld_H65+0x687>
     +0x5b3: cmp     $0x88,%r15d
     +0x5ba: je      <mld_H65+0x590>
     +0x5bc: mov     %r15d,%esi
     +0x5bf: lea     (%rsp,%rsi,1),%rcx
     +0x5c3: add     $0x10,%rcx
     +0x5c7: cmp     $0x4,%rax
     +0x5cb: jae     <mld_H65+0x5e0>
     +0x5cd: xor     %edx,%edx
     +0x5cf: jmp     <mld_H65+0x670>
     +0x5d4: data16  data16 cs nopw 0x0(%rax,%rax,1)
     +0x5e0: cmp     $0x20,%rax
     +0x5e4: jae     <mld_H65+0x5ea>
     +0x5e6: xor     %edx,%edx
     +0x5e8: jmp     <mld_H65+0x63a>
     +0x5ea: mov     %eax,%edx
     +0x5ec: and     $0xffffffe0,%edx
     +0x5ef: add     %rbp,%rsi
     +0x5f2: xor     %edi,%edi
     +0x5f4: data16  data16 cs nopw 0x0(%rax,%rax,1)
     +0x600: movups  0x0(%r13,%rdi,1),%xmm0
     +0x606: movups  0x10(%r13,%rdi,1),%xmm1
     +0x60c: movups  -0x10(%rsi,%rdi,1),%xmm2
     +0x611: xorps   %xmm0,%xmm2
     +0x614: movups  (%rsi,%rdi,1),%xmm0
     +0x618: xorps   %xmm1,%xmm0
     +0x61b: movups  %xmm2,-0x10(%rsi,%rdi,1)
     +0x620: movups  %xmm0,(%rsi,%rdi,1)
     +0x624: add     $0x20,%rdi
     +0x628: cmp     %rdi,%rdx
     +0x62b: jne     <mld_H65+0x600>
     +0x62d: cmp     %rdx,%rax
     +0x630: je      <mld_H65+0x590>
     +0x636: test    $0x1c,%al
     +0x638: je      <mld_H65+0x670>
     +0x63a: mov     %rdx,%rsi
     +0x63d: mov     %eax,%edx
     +0x63f: and     $0xfffffffc,%edx
     +0x642: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x650: mov     0x0(%r13,%rsi,1),%edi
     +0x655: xor     %edi,(%rcx,%rsi,1)
     +0x658: add     $0x4,%rsi
     +0x65c: cmp     %rsi,%rdx
     +0x65f: jne     <mld_H65+0x650>
     +0x661: jmp     <mld_H65+0x67d>
     +0x663: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x670: movzbl  0x0(%r13,%rdx,1),%esi
     +0x676: xor     %sil,(%rcx,%rdx,1)
     +0x67a: inc     %rdx
     +0x67d: cmp     %rdx,%rax
     +0x680: jne     <mld_H65+0x670>
     +0x682: jmp     <mld_H65+0x590>
     +0x687: xor     %r15d,%r15d
     +0x68a: test    %r14,%r14
     +0x68d: mov     0x8(%rsp),%rbp
     +0x692: je      <mld_H65+0x727>
     +0x698: cmp     $0x4,%r14
     +0x69c: jb      <mld_H65+0x6b8>
     +0x69e: lea     (%r14,%r13,1),%rax
     +0x6a2: cmp     %rax,%r12
     +0x6a5: jae     <mld_H65+0x88c>
     +0x6ab: lea     (%r12,%r14,1),%rax
     +0x6af: cmp     %rax,%r13
     +0x6b2: jae     <mld_H65+0x88c>
     +0x6b8: xor     %eax,%eax
     +0x6ba: mov     %r14,%rdx
     +0x6bd: mov     %rax,%rcx
     +0x6c0: and     $0x3,%rdx
     +0x6c4: je      <mld_H65+0x6e2>
     +0x6c6: mov     %rax,%rcx
     +0x6c9: nopl    0x0(%rax)
     +0x6d0: movzbl  0x0(%r13,%rcx,1),%esi
     +0x6d6: xor     %sil,(%r12,%rcx,1)
     +0x6da: inc     %rcx
     +0x6dd: dec     %rdx
     +0x6e0: jne     <mld_H65+0x6d0>
     +0x6e2: sub     %r14,%rax
     +0x6e5: cmp     $0xfffffffffffffffc,%rax
     +0x6e9: ja      <mld_H65+0x724>
     +0x6eb: nopl    0x0(%rax,%rax,1)
     +0x6f0: movzbl  0x0(%r13,%rcx,1),%eax
     +0x6f6: xor     %al,(%r12,%rcx,1)
     +0x6fa: movzbl  0x1(%r13,%rcx,1),%eax
     +0x700: xor     %al,0x1(%r12,%rcx,1)
     +0x705: movzbl  0x2(%r13,%rcx,1),%eax
     +0x70b: xor     %al,0x2(%r12,%rcx,1)
     +0x710: movzbl  0x3(%r13,%rcx,1),%eax
     +0x716: xor     %al,0x3(%r12,%rcx,1)
     +0x71b: add     $0x4,%rcx
     +0x71f: cmp     %rcx,%r14
     +0x722: jne     <mld_H65+0x6f0>
     +0x724: add     %r14d,%r15d
     +0x727: mov     %r15d,0xd8(%rsp)
     +0x72f: mov     %r15d,%eax
     +0x732: xorb    $0x1f,0x10(%rsp,%rax,1)
     +0x737: xorb    $0x80,0x97(%rsp)
     +0x73f: movl    $0x88,0xd8(%rsp)
     +0x74a: mov     $0x88,%r13d
     +0x750: xor     %r12d,%r12d
     +0x753: lea     0x10(%rsp),%r15
     +0x758: jmp     <mld_H65+0x792>
     +0x75a: nopw    0x0(%rax,%rax,1)
     +0x760: mov     $0x88,%r14d
     +0x766: sub     %r13d,%r14d
     +0x769: cmp     %r14,%rbx
     +0x76c: cmovb   %rbx,%r14
     +0x770: mov     %r13d,%eax
     +0x773: lea     (%rsp,%rax,1),%rsi
     +0x777: add     $0x10,%rsi
     +0x77b: lea     (%r12,%rbp,1),%rdi
     +0x77f: mov     %r14,%rdx
     +0x782: call    <memcpy>
     +0x787: add     %r14d,%r13d
     +0x78a: add     %r14,%r12
     +0x78d: sub     %r14,%rbx
     +0x790: je      <mld_H65+0x7bc>
     +0x792: cmp     $0x88,%r13d
     +0x799: jne     <mld_H65+0x760>
     +0x79b: mov     %r15,%rdi
     +0x79e: call    <mldsa_keccakf1600_permute>
     +0x7a3: cmp     $0x88,%rbx
     +0x7aa: mov     $0x88,%r14d
     +0x7b0: cmovb   %rbx,%r14
     +0x7b4: xor     %r13d,%r13d
     +0x7b7: mov     %r15,%rsi
     +0x7ba: jmp     <mld_H65+0x77b>
     +0x7bc: xorps   %xmm0,%xmm0
     +0x7bf: movaps  %xmm0,0xd0(%rsp)
     +0x7c7: movaps  %xmm0,0xc0(%rsp)
     +0x7cf: movaps  %xmm0,0xb0(%rsp)
     +0x7d7: movaps  %xmm0,0xa0(%rsp)
     +0x7df: movaps  %xmm0,0x90(%rsp)
     +0x7e7: movaps  %xmm0,0x80(%rsp)
     +0x7ef: movaps  %xmm0,0x70(%rsp)
     +0x7f4: movaps  %xmm0,0x60(%rsp)
     +0x7f9: movaps  %xmm0,0x50(%rsp)
     +0x7fe: movaps  %xmm0,0x40(%rsp)
     +0x803: movaps  %xmm0,0x30(%rsp)
     +0x808: movaps  %xmm0,0x20(%rsp)
     +0x80d: movaps  %xmm0,0x10(%rsp)
     +0x812: lea     0x10(%rsp),%rax
     +0x817: movaps  %xmm0,0xd0(%rsp)
     +0x81f: movaps  %xmm0,0xc0(%rsp)
     +0x827: movaps  %xmm0,0xb0(%rsp)
     +0x82f: movaps  %xmm0,0xa0(%rsp)
     +0x837: movaps  %xmm0,0x90(%rsp)
     +0x83f: movaps  %xmm0,0x80(%rsp)
     +0x847: movaps  %xmm0,0x70(%rsp)
     +0x84c: movaps  %xmm0,0x60(%rsp)
     +0x851: movaps  %xmm0,0x50(%rsp)
     +0x856: movaps  %xmm0,0x40(%rsp)
     +0x85b: movaps  %xmm0,0x30(%rsp)
     +0x860: movaps  %xmm0,0x20(%rsp)
     +0x865: movaps  %xmm0,0x10(%rsp)
     +0x86a: add     $0xe8,%rsp
     +0x871: pop     %rbx
     +0x872: pop     %r12
     +0x874: pop     %r13
     +0x876: pop     %r14
     +0x878: pop     %r15
     +0x87a: pop     %rbp
     +0x87b: xor     %eax,%eax
     +0x87d: xor     %ecx,%ecx
     +0x87f: xor     %edi,%edi
     +0x881: xor     %edx,%edx
     +0x883: xor     %esi,%esi
     +0x885: xor     %r8d,%r8d
     +0x888: xor     %r9d,%r9d
     +0x88b: ret     
     +0x88c: cmp     $0x20,%r14
     +0x890: jae     <mld_H65+0x8a7>
     +0x892: xor     %eax,%eax
     +0x894: jmp     <mld_H65+0x8f4>
     +0x896: cmp     $0x20,%r12
     +0x89a: jae     <mld_H65+0x920>
     +0x8a0: xor     %eax,%eax
     +0x8a2: jmp     <mld_H65+0x972>
     +0x8a7: mov     %r14,%rax
     +0x8aa: and     $0xffffffffffffffe0,%rax
     +0x8ae: xor     %ecx,%ecx
     +0x8b0: movups  0x0(%r13,%rcx,1),%xmm0
     +0x8b6: movups  0x10(%r13,%rcx,1),%xmm1
     +0x8bc: movups  (%r12,%rcx,1),%xmm2
     +0x8c1: xorps   %xmm0,%xmm2
     +0x8c4: movups  0x10(%r12,%rcx,1),%xmm0
     +0x8ca: xorps   %xmm1,%xmm0
     +0x8cd: movups  %xmm2,(%r12,%rcx,1)
     +0x8d2: movups  %xmm0,0x10(%r12,%rcx,1)
     +0x8d8: add     $0x20,%rcx
     +0x8dc: cmp     %rcx,%rax
     +0x8df: jne     <mld_H65+0x8b0>
     +0x8e1: cmp     %rax,%r14
     +0x8e4: je      <mld_H65+0x724>
     +0x8ea: test    $0x1c,%r14b
     +0x8ee: je      <mld_H65+0x6ba>
     +0x8f4: mov     %rax,%rcx
     +0x8f7: mov     %r14,%rax
     +0x8fa: and     $0xfffffffffffffffc,%rax
     +0x8fe: xchg    %ax,%ax
     +0x900: mov     0x0(%r13,%rcx,1),%edx
     +0x905: xor     %edx,(%r12,%rcx,1)
     +0x909: add     $0x4,%rcx
     +0x90d: cmp     %rcx,%rax
     +0x910: jne     <mld_H65+0x900>
     +0x912: cmp     %rax,%r14
     +0x915: je      <mld_H65+0x724>
     +0x91b: jmp     <mld_H65+0x6ba>
     +0x920: mov     %r12,%rax
     +0x923: and     $0xffffffffffffffe0,%rax
     +0x927: xor     %ecx,%ecx
     +0x929: nopl    0x0(%rax)
     +0x930: movups  0x0(%r13,%rcx,1),%xmm0
     +0x936: movups  0x10(%r13,%rcx,1),%xmm1
     +0x93c: movups  0x0(%rbp,%rcx,1),%xmm2
     +0x941: xorps   %xmm0,%xmm2
     +0x944: movups  0x10(%rbp,%rcx,1),%xmm0
     +0x949: xorps   %xmm1,%xmm0
     +0x94c: movups  %xmm2,0x0(%rbp,%rcx,1)
     +0x951: movups  %xmm0,0x10(%rbp,%rcx,1)
     +0x956: add     $0x20,%rcx
     +0x95a: cmp     %rcx,%rax
     +0x95d: jne     <mld_H65+0x930>
     +0x95f: cmp     %rax,%r12
     +0x962: je      <mld_H65+0x541>
     +0x968: test    $0x1c,%r12b
     +0x96c: je      <mld_H65+0x4d7>
     +0x972: mov     %rax,%rcx
     +0x975: mov     %r12,%rax
     +0x978: and     $0xfffffffffffffffc,%rax
     +0x97c: nopl    0x0(%rax)
     +0x980: mov     0x0(%r13,%rcx,1),%edx
     +0x985: xor     %edx,0x0(%rbp,%rcx,1)
     +0x989: add     $0x4,%rcx
     +0x98d: cmp     %rcx,%rax
     +0x990: jne     <mld_H65+0x980>
     +0x992: cmp     %rax,%r12
     +0x995: je      <mld_H65+0x541>
     +0x99b: jmp     <mld_H65+0x4d7>
 ***)

let MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mld_H65";
    layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The output is SHAKE256 of in1 || in2 || in3, the bytes M1,   *)
(* M2 and M3 as numbers. The last two arguments, in3 and in3len, are on the  *)
(* stack above the return address. The function saves six registers below    *)
(* the return address and reserves 232 bytes for the state and its position  *)
(* (at stackpointer - 264) and the saved output pointer, below which the     *)
(* calls of mldsa_keccakf1600_permute and memcpy use 296 bytes with their    *)
(* return addresses: 576 bytes of stack below the return address in all. The *)
(* stack is aligned as the ABI requires (stackpointer + 8 a multiple of 16), *)
(* since the state is zeroed with MOVAPS.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> !out outlen in1 in1len in2 in2len in3 in3len M1 M2 M3 pc stackpointer
   returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ~(in1len = 0) /\ aligned 16 (word_add stackpointer (word 8)) /\
        ALL (nonoverlapping (word_sub stackpointer (word 576),576))
         [(out,outlen); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        nonoverlapping (out,outlen) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 576),576)]
         [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mld_H65) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; in1; word in1len; in2;
                               word in2len] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  in3 /\
                  read (memory :> bytes64(word_add stackpointer (word 16))) s =
                  word in3len /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(in1,in1len)) s = M1 /\
                  read (memory :> bytes(in2,in2len)) s = M2 /\
                  read (memory :> bytes(in3,in3len)) s = M3)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq
                     (mld_shake256_byte (in1len + in2len + in3len)
                       (M1 + 2 EXP (8 * in1len) *
                             (M2 + 2 EXP (8 * in2len) * M3)))
                     outlen))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 576),576)])`;;

let MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the lengths only (which give   *)
(* the calls and their arguments), with all accesses within the output, the  *)
(* inputs, the stack, the return address, the arguments on the stack and the *)
(* round constants of the permutation, and the writes within the output and  *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e out outlen in1 in1len in2 in2len in3 in3len M1 M2 M3 pc
            stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ~(in1len = 0) /\ aligned 16 (word_add stackpointer (word 8)) /\
        ALL (nonoverlapping (word_sub stackpointer (word 576),576))
         [(out,outlen); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        nonoverlapping (out,outlen) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 576),576)]
         [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mld_H65) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; in1; word in1len; in2;
                               word in2len] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  in3 /\
                  read (memory :> bytes64(word_add stackpointer (word 16))) s =
                  word in3len /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(in1,in1len)) s = M1 /\
                  read (memory :> bytes(in2,in2len)) s = M2 /\
                  read (memory :> bytes(in3,in3len)) s = M3 /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq
                     (mld_shake256_byte (in1len + in2len + in3len)
                       (M1 + 2 EXP (8 * in1len) *
                             (M2 + 2 EXP (8 * in2len) * M3)))
                     outlen) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out outlen in1 in1len in2 in2len in3 in3len
                                 mc pc (word_sub stackpointer (word 576))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; in1,in1len; in2,in2len; in3,in3len;
                       word_sub stackpointer (word 576),576; stackpointer,8;
                       word(pc + got_memcpy),8; ea,el;
                       word_add stackpointer (word 8),16;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,outlen; word_sub stackpointer (word 576),576]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 576),576)])`;;

let MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e out outlen in1 in1len in2 in2len in3 in3len pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ~(in1len = 0) /\ aligned 16 (word_add stackpointer (word 8)) /\
        ALL (nonoverlapping (word_sub stackpointer (word 576),576))
         [(out,outlen); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        nonoverlapping (out,outlen) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 576),576)]
         [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mld_H65) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; in1; word in1len; in2;
                               word in2len] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  in3 /\
                  read (memory :> bytes64(word_add stackpointer (word 16))) s =
                  word in3len /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out outlen in1 in1len in2 in2len in3 in3len
                                 mc pc (word_sub stackpointer (word 576))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; in1,in1len; in2,in2len; in3,in3len;
                       word_sub stackpointer (word 576),576; stackpointer,8;
                       word(pc + got_memcpy),8; ea,el;
                       word_add stackpointer (word 8),16;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,outlen; word_sub stackpointer (word 576),576]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 576),576)])`;;

let MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
