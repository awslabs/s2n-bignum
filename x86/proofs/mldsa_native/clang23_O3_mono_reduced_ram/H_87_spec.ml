(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 of up to three inputs: the statement. This is the code for       *)
(* mld_H87 (mld_H in sign.c, for ML-DSA-87) from mldsa-native's portable C   *)
(* implementation compiled by clang 23 with -O3 as a monolithic build with   *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). Clang inlined the     *)
(* SHAKE256 functions: the function zeroes a Keccak state on its stack,      *)
(* absorbs in1, and in2 and in3 unless their lengths are zero, with vector   *)
(* and scalar loops and calls of mldsa_keccakf1600_permute, finalizes,       *)
(* squeezes the output block by block with calls of                          *)
(* mldsa_keccakf1600_permute and memcpy, and zeroes the state. Clang dropped *)
(* the argument outlen of mld_H87, which is 64 in all its calls, so the      *)
(* output has 64 bytes and the other arguments come one register earlier. It *)
(* is verified in the whole image (see libmldsa.ml) against                  *)
(* mld_shake256_byte of common/mldsa_native_fips202.ml for the concatenation *)
(* of the three inputs; the inputs and the output may overlap, and a pointer *)
(* with a zero length may be anything (NULL), except that in1len must not be *)
(* zero: the code for the first input skips the test for an empty input when *)
(* the input is shorter than a block (presumably because all callers pass a  *)
(* nonzero constant in1len), and for in1len = 0 it does not terminate. It is *)
(* also shown to be constant time and memory safe.                           *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mld_H87:
       +0x0: push    %rbp
       +0x1: push    %r15
       +0x3: push    %r14
       +0x5: push    %r13
       +0x7: push    %r12
       +0x9: push    %rbx
       +0xa: sub     $0xd8,%rsp
      +0x11: mov     %r9,%r14
      +0x14: mov     %r8,%r12
      +0x17: mov     %rcx,%r13
      +0x1a: mov     %rdx,%r15
      +0x1d: mov     %rsi,%rbp
      +0x20: mov     %rdi,0xd0(%rsp)
      +0x28: xorps   %xmm0,%xmm0
      +0x2b: movups  %xmm0,0xbc(%rsp)
      +0x33: movaps  %xmm0,0xb0(%rsp)
      +0x3b: movaps  %xmm0,0xa0(%rsp)
      +0x43: movaps  %xmm0,0x90(%rsp)
      +0x4b: movaps  %xmm0,0x80(%rsp)
      +0x53: movaps  %xmm0,0x70(%rsp)
      +0x58: movaps  %xmm0,0x60(%rsp)
      +0x5d: movaps  %xmm0,0x50(%rsp)
      +0x62: movaps  %xmm0,0x40(%rsp)
      +0x67: movaps  %xmm0,0x30(%rsp)
      +0x6c: movaps  %xmm0,0x20(%rsp)
      +0x71: movaps  %xmm0,0x10(%rsp)
      +0x76: movaps  %xmm0,(%rsp)
      +0x7a: cmp     $0x88,%rdx
      +0x81: jb      <mld_H87+0x139>
      +0x87: mov     %rsp,%rbx
      +0x8a: nopw    0x0(%rax,%rax,1)
      +0x90: movups  0x0(%rbp),%xmm0
      +0x94: movups  0x10(%rbp),%xmm1
      +0x98: xorps   (%rsp),%xmm0
      +0x9c: xorps   0x10(%rsp),%xmm1
      +0xa1: movaps  %xmm0,(%rsp)
      +0xa5: movaps  %xmm1,0x10(%rsp)
      +0xaa: movups  0x20(%rbp),%xmm0
      +0xae: movups  0x30(%rbp),%xmm1
      +0xb2: xorps   0x20(%rsp),%xmm0
      +0xb7: xorps   0x30(%rsp),%xmm1
      +0xbc: movaps  %xmm0,0x20(%rsp)
      +0xc1: movaps  %xmm1,0x30(%rsp)
      +0xc6: movups  0x40(%rbp),%xmm0
      +0xca: movups  0x50(%rbp),%xmm1
      +0xce: xorps   0x40(%rsp),%xmm0
      +0xd3: xorps   0x50(%rsp),%xmm1
      +0xd8: movaps  %xmm0,0x40(%rsp)
      +0xdd: movaps  %xmm1,0x50(%rsp)
      +0xe2: movups  0x60(%rbp),%xmm0
      +0xe6: movups  0x70(%rbp),%xmm1
      +0xea: xorps   0x60(%rsp),%xmm0
      +0xef: xorps   0x70(%rsp),%xmm1
      +0xf4: movaps  %xmm0,0x60(%rsp)
      +0xf9: movaps  %xmm1,0x70(%rsp)
      +0xfe: mov     0x80(%rbp),%rax
     +0x105: xor     %rax,0x80(%rsp)
     +0x10d: add     $0xffffffffffffff78,%r15
     +0x114: add     $0x88,%rbp
     +0x11b: mov     %rbx,%rdi
     +0x11e: call    <mldsa_keccakf1600_permute>
     +0x123: cmp     $0x87,%r15
     +0x12a: ja      <mld_H87+0x90>
     +0x130: test    %r15,%r15
     +0x133: je      <mld_H87+0x1c8>
     +0x139: cmp     $0x4,%r15
     +0x13d: jb      <mld_H87+0x15a>
     +0x13f: lea     (%rsp,%r15,1),%rax
     +0x143: lea     (%r15,%rbp,1),%rcx
     +0x147: mov     %rsp,%rdx
     +0x14a: cmp     %rcx,%rdx
     +0x14d: setb    %cl
     +0x150: cmp     %rax,%rbp
     +0x153: setb    %al
     +0x156: test    %al,%cl
     +0x158: je      <mld_H87+0x1be>
     +0x15a: xor     %eax,%eax
     +0x15c: mov     %r15,%rdx
     +0x15f: mov     %rax,%rcx
     +0x162: and     $0x3,%rdx
     +0x166: je      <mld_H87+0x181>
     +0x168: mov     %rax,%rcx
     +0x16b: nopl    0x0(%rax,%rax,1)
     +0x170: movzbl  0x0(%rbp,%rcx,1),%esi
     +0x175: xor     %sil,(%rsp,%rcx,1)
     +0x179: inc     %rcx
     +0x17c: dec     %rdx
     +0x17f: jne     <mld_H87+0x170>
     +0x181: sub     %r15,%rax
     +0x184: cmp     $0xfffffffffffffffc,%rax
     +0x188: ja      <mld_H87+0x239>
     +0x18e: xchg    %ax,%ax
     +0x190: movzbl  0x0(%rbp,%rcx,1),%eax
     +0x195: xor     %al,(%rsp,%rcx,1)
     +0x198: movzbl  0x1(%rbp,%rcx,1),%eax
     +0x19d: xor     %al,0x1(%rsp,%rcx,1)
     +0x1a1: movzbl  0x2(%rbp,%rcx,1),%eax
     +0x1a6: xor     %al,0x2(%rsp,%rcx,1)
     +0x1aa: movzbl  0x3(%rbp,%rcx,1),%eax
     +0x1af: xor     %al,0x3(%rsp,%rcx,1)
     +0x1b3: add     $0x4,%rcx
     +0x1b7: cmp     %rcx,%r15
     +0x1ba: jne     <mld_H87+0x190>
     +0x1bc: jmp     <mld_H87+0x239>
     +0x1be: cmp     $0x20,%r15
     +0x1c2: jae     <mld_H87+0x1cd>
     +0x1c4: xor     %eax,%eax
     +0x1c6: jmp     <mld_H87+0x214>
     +0x1c8: xor     %r15d,%r15d
     +0x1cb: jmp     <mld_H87+0x239>
     +0x1cd: mov     %r15d,%eax
     +0x1d0: and     $0xe0,%eax
     +0x1d5: xor     %ecx,%ecx
     +0x1d7: nopw    0x0(%rax,%rax,1)
     +0x1e0: movups  0x0(%rbp,%rcx,1),%xmm0
     +0x1e5: movups  0x10(%rbp,%rcx,1),%xmm1
     +0x1ea: xorps   (%rsp,%rcx,1),%xmm0
     +0x1ee: xorps   0x10(%rsp,%rcx,1),%xmm1
     +0x1f3: movaps  %xmm0,(%rsp,%rcx,1)
     +0x1f7: movaps  %xmm1,0x10(%rsp,%rcx,1)
     +0x1fc: add     $0x20,%rcx
     +0x200: cmp     %rcx,%rax
     +0x203: jne     <mld_H87+0x1e0>
     +0x205: cmp     %rax,%r15
     +0x208: je      <mld_H87+0x239>
     +0x20a: test    $0x1c,%r15b
     +0x20e: je      <mld_H87+0x15c>
     +0x214: mov     %rax,%rcx
     +0x217: mov     %r15d,%eax
     +0x21a: and     $0xfc,%eax
     +0x21f: nop     
     +0x220: mov     0x0(%rbp,%rcx,1),%edx
     +0x224: xor     %edx,(%rsp,%rcx,1)
     +0x227: add     $0x4,%rcx
     +0x22b: cmp     %rcx,%rax
     +0x22e: jne     <mld_H87+0x220>
     +0x230: cmp     %rax,%r15
     +0x233: jne     <mld_H87+0x15c>
     +0x239: mov     0x110(%rsp),%rbx
     +0x241: mov     %r15d,0xc8(%rsp)
     +0x249: test    %r12,%r12
     +0x24c: je      <mld_H87+0x51c>
     +0x252: mov     $0x88,%eax
     +0x257: sub     %r15,%rax
     +0x25a: cmp     %rax,%r12
     +0x25d: jae     <mld_H87+0x268>
     +0x25f: lea     (%rsp,%r15,1),%rbp
     +0x263: jmp     <mld_H87+0x483>
     +0x268: mov     %rsp,%rbp
     +0x26b: jmp     <mld_H87+0x296>
     +0x26d: nopl    (%rax)
     +0x270: sub     %rax,%r12
     +0x273: add     %rax,%r13
     +0x276: mov     %rbp,%rdi
     +0x279: call    <mldsa_keccakf1600_permute>
     +0x27e: mov     $0x88,%eax
     +0x283: mov     $0x0,%r15d
     +0x289: cmp     $0x87,%r12
     +0x290: jbe     <mld_H87+0x477>
     +0x296: lea     (%rsp,%r15,1),%rcx
     +0x29a: cmp     $0x4,%rax
     +0x29e: jae     <mld_H87+0x2b0>
     +0x2a0: xor     %edx,%edx
     +0x2a2: jmp     <mld_H87+0x460>
     +0x2a7: nopw    0x0(%rax,%rax,1)
     +0x2b0: cmp     $0x20,%rax
     +0x2b4: jae     <mld_H87+0x2c0>
     +0x2b6: xor     %edx,%edx
     +0x2b8: jmp     <mld_H87+0x42d>
     +0x2bd: nopl    (%rax)
     +0x2c0: mov     %eax,%edx
     +0x2c2: and     $0xe0,%edx
     +0x2c8: movups  0x0(%r13),%xmm0
     +0x2cd: movups  0x10(%r13),%xmm1
     +0x2d2: movups  (%rcx),%xmm2
     +0x2d5: xorps   %xmm0,%xmm2
     +0x2d8: movups  0x10(%rcx),%xmm0
     +0x2dc: xorps   %xmm1,%xmm0
     +0x2df: movups  %xmm2,(%rcx)
     +0x2e2: movups  %xmm0,0x10(%rcx)
     +0x2e6: cmp     $0x20,%rdx
     +0x2ea: je      <mld_H87+0x420>
     +0x2f0: movups  0x20(%r13),%xmm0
     +0x2f5: movups  0x30(%r13),%xmm1
     +0x2fa: movups  0x20(%rcx),%xmm2
     +0x2fe: xorps   %xmm0,%xmm2
     +0x301: movups  0x30(%rcx),%xmm0
     +0x305: xorps   %xmm1,%xmm0
     +0x308: movups  %xmm2,0x20(%rcx)
     +0x30c: movups  %xmm0,0x30(%rcx)
     +0x310: cmp     $0x40,%edx
     +0x313: je      <mld_H87+0x420>
     +0x319: movups  0x40(%r13),%xmm0
     +0x31e: movups  0x50(%r13),%xmm1
     +0x323: movups  0x40(%rcx),%xmm2
     +0x327: xorps   %xmm0,%xmm2
     +0x32a: movups  0x50(%rcx),%xmm0
     +0x32e: xorps   %xmm1,%xmm0
     +0x331: movups  %xmm2,0x40(%rcx)
     +0x335: movups  %xmm0,0x50(%rcx)
     +0x339: cmp     $0x60,%edx
     +0x33c: je      <mld_H87+0x420>
     +0x342: movups  0x60(%r13),%xmm0
     +0x347: movups  0x70(%r13),%xmm1
     +0x34c: movups  0x60(%rcx),%xmm2
     +0x350: xorps   %xmm0,%xmm2
     +0x353: movups  0x70(%rcx),%xmm0
     +0x357: xorps   %xmm1,%xmm0
     +0x35a: movups  %xmm2,0x60(%rcx)
     +0x35e: movups  %xmm0,0x70(%rcx)
     +0x362: cmp     $0x80,%edx
     +0x368: je      <mld_H87+0x420>
     +0x36e: movups  0x80(%r13),%xmm0
     +0x376: movups  0x90(%r13),%xmm1
     +0x37e: movups  0x80(%rcx),%xmm2
     +0x385: xorps   %xmm0,%xmm2
     +0x388: movups  0x90(%rcx),%xmm0
     +0x38f: xorps   %xmm1,%xmm0
     +0x392: movups  %xmm2,0x80(%rcx)
     +0x399: movups  %xmm0,0x90(%rcx)
     +0x3a0: cmp     $0xa0,%edx
     +0x3a6: je      <mld_H87+0x420>
     +0x3a8: movups  0xa0(%r13),%xmm0
     +0x3b0: movups  0xb0(%r13),%xmm1
     +0x3b8: movups  0xa0(%rcx),%xmm2
     +0x3bf: xorps   %xmm0,%xmm2
     +0x3c2: movups  0xb0(%rcx),%xmm0
     +0x3c9: xorps   %xmm1,%xmm0
     +0x3cc: movups  %xmm2,0xa0(%rcx)
     +0x3d3: movups  %xmm0,0xb0(%rcx)
     +0x3da: cmp     $0xc0,%edx
     +0x3e0: je      <mld_H87+0x420>
     +0x3e2: movups  0xc0(%r13),%xmm0
     +0x3ea: movups  0xd0(%r13),%xmm1
     +0x3f2: movups  0xc0(%rcx),%xmm2
     +0x3f9: xorps   %xmm0,%xmm2
     +0x3fc: movups  0xd0(%rcx),%xmm0
     +0x403: xorps   %xmm1,%xmm0
     +0x406: movups  %xmm2,0xc0(%rcx)
     +0x40d: movups  %xmm0,0xd0(%rcx)
     +0x414: data16  data16 cs nopw 0x0(%rax,%rax,1)
     +0x420: cmp     %rdx,%rax
     +0x423: je      <mld_H87+0x270>
     +0x429: test    $0x1c,%al
     +0x42b: je      <mld_H87+0x460>
     +0x42d: mov     %rdx,%rsi
     +0x430: mov     %eax,%edx
     +0x432: and     $0xfc,%edx
     +0x438: nopl    0x0(%rax,%rax,1)
     +0x440: mov     0x0(%r13,%rsi,1),%edi
     +0x445: xor     %edi,(%rcx,%rsi,1)
     +0x448: add     $0x4,%rsi
     +0x44c: cmp     %rsi,%rdx
     +0x44f: jne     <mld_H87+0x440>
     +0x451: jmp     <mld_H87+0x46d>
     +0x453: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x460: movzbl  0x0(%r13,%rdx,1),%esi
     +0x466: xor     %sil,(%rcx,%rdx,1)
     +0x46a: inc     %rdx
     +0x46d: cmp     %rdx,%rax
     +0x470: jne     <mld_H87+0x460>
     +0x472: jmp     <mld_H87+0x270>
     +0x477: xor     %r15d,%r15d
     +0x47a: test    %r12,%r12
     +0x47d: je      <mld_H87+0x514>
     +0x483: cmp     $0x4,%r12
     +0x487: jb      <mld_H87+0x4a5>
     +0x489: lea     (%r12,%rbp,1),%rax
     +0x48d: lea     (%r12,%r13,1),%rcx
     +0x491: cmp     %rcx,%rbp
     +0x494: setb    %cl
     +0x497: cmp     %rax,%r13
     +0x49a: setb    %al
     +0x49d: test    %al,%cl
     +0x49f: je      <mld_H87+0x7fa>
     +0x4a5: xor     %eax,%eax
     +0x4a7: mov     %r12,%rdx
     +0x4aa: mov     %rax,%rcx
     +0x4ad: and     $0x3,%rdx
     +0x4b1: je      <mld_H87+0x4d3>
     +0x4b3: mov     %rax,%rcx
     +0x4b6: cs      nopw 0x0(%rax,%rax,1)
     +0x4c0: movzbl  0x0(%r13,%rcx,1),%esi
     +0x4c6: xor     %sil,0x0(%rbp,%rcx,1)
     +0x4cb: inc     %rcx
     +0x4ce: dec     %rdx
     +0x4d1: jne     <mld_H87+0x4c0>
     +0x4d3: sub     %r12,%rax
     +0x4d6: cmp     $0xfffffffffffffffc,%rax
     +0x4da: ja      <mld_H87+0x511>
     +0x4dc: nopl    0x0(%rax)
     +0x4e0: movzbl  0x0(%r13,%rcx,1),%eax
     +0x4e6: xor     %al,0x0(%rbp,%rcx,1)
     +0x4ea: movzbl  0x1(%r13,%rcx,1),%eax
     +0x4f0: xor     %al,0x1(%rbp,%rcx,1)
     +0x4f4: movzbl  0x2(%r13,%rcx,1),%eax
     +0x4fa: xor     %al,0x2(%rbp,%rcx,1)
     +0x4fe: movzbl  0x3(%r13,%rcx,1),%eax
     +0x504: xor     %al,0x3(%rbp,%rcx,1)
     +0x508: add     $0x4,%rcx
     +0x50c: cmp     %rcx,%r12
     +0x50f: jne     <mld_H87+0x4e0>
     +0x511: add     %r12d,%r15d
     +0x514: mov     %r15d,0xc8(%rsp)
     +0x51c: test    %rbx,%rbx
     +0x51f: je      <mld_H87+0x6de>
     +0x525: mov     $0x88,%eax
     +0x52a: sub     %r15d,%eax
     +0x52d: cmp     %rax,%rbx
     +0x530: jae     <mld_H87+0x53e>
     +0x532: mov     %r15d,%eax
     +0x535: lea     (%rsp,%rax,1),%r12
     +0x539: jmp     <mld_H87+0x642>
     +0x53e: lea     0x10(%rsp),%r13
     +0x543: mov     %rsp,%r12
     +0x546: jmp     <mld_H87+0x573>
     +0x548: nopl    0x0(%rax,%rax,1)
     +0x550: sub     %rax,%rbx
     +0x553: add     %rax,%r14
     +0x556: mov     %r12,%rdi
     +0x559: call    <mldsa_keccakf1600_permute>
     +0x55e: xor     %r15d,%r15d
     +0x561: mov     $0x88,%eax
     +0x566: cmp     $0x87,%rbx
     +0x56d: jbe     <mld_H87+0x636>
     +0x573: cmp     $0x88,%r15d
     +0x57a: je      <mld_H87+0x550>
     +0x57c: mov     %r15d,%esi
     +0x57f: lea     (%rsp,%rsi,1),%rcx
     +0x583: cmp     $0x4,%rax
     +0x587: jae     <mld_H87+0x590>
     +0x589: xor     %edx,%edx
     +0x58b: jmp     <mld_H87+0x620>
     +0x590: cmp     $0x20,%rax
     +0x594: jae     <mld_H87+0x59a>
     +0x596: xor     %edx,%edx
     +0x598: jmp     <mld_H87+0x5e9>
     +0x59a: mov     %eax,%edx
     +0x59c: and     $0xffffffe0,%edx
     +0x59f: add     %r13,%rsi
     +0x5a2: xor     %edi,%edi
     +0x5a4: data16  data16 cs nopw 0x0(%rax,%rax,1)
     +0x5b0: movups  (%r14,%rdi,1),%xmm0
     +0x5b5: movups  0x10(%r14,%rdi,1),%xmm1
     +0x5bb: movups  -0x10(%rsi,%rdi,1),%xmm2
     +0x5c0: xorps   %xmm0,%xmm2
     +0x5c3: movups  (%rsi,%rdi,1),%xmm0
     +0x5c7: xorps   %xmm1,%xmm0
     +0x5ca: movups  %xmm2,-0x10(%rsi,%rdi,1)
     +0x5cf: movups  %xmm0,(%rsi,%rdi,1)
     +0x5d3: add     $0x20,%rdi
     +0x5d7: cmp     %rdi,%rdx
     +0x5da: jne     <mld_H87+0x5b0>
     +0x5dc: cmp     %rdx,%rax
     +0x5df: je      <mld_H87+0x550>
     +0x5e5: test    $0x1c,%al
     +0x5e7: je      <mld_H87+0x620>
     +0x5e9: mov     %rdx,%rsi
     +0x5ec: mov     %eax,%edx
     +0x5ee: and     $0xfffffffc,%edx
     +0x5f1: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x600: mov     (%r14,%rsi,1),%edi
     +0x604: xor     %edi,(%rcx,%rsi,1)
     +0x607: add     $0x4,%rsi
     +0x60b: cmp     %rsi,%rdx
     +0x60e: jne     <mld_H87+0x600>
     +0x610: jmp     <mld_H87+0x62c>
     +0x612: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x620: movzbl  (%r14,%rdx,1),%esi
     +0x625: xor     %sil,(%rcx,%rdx,1)
     +0x629: inc     %rdx
     +0x62c: cmp     %rdx,%rax
     +0x62f: jne     <mld_H87+0x620>
     +0x631: jmp     <mld_H87+0x550>
     +0x636: xor     %r15d,%r15d
     +0x639: test    %rbx,%rbx
     +0x63c: je      <mld_H87+0x6d6>
     +0x642: cmp     $0x4,%rbx
     +0x646: jb      <mld_H87+0x662>
     +0x648: lea     (%r14,%rbx,1),%rax
     +0x64c: cmp     %rax,%r12
     +0x64f: jae     <mld_H87+0x7f0>
     +0x655: lea     (%r12,%rbx,1),%rax
     +0x659: cmp     %rax,%r14
     +0x65c: jae     <mld_H87+0x7f0>
     +0x662: xor     %eax,%eax
     +0x664: mov     %rbx,%rdx
     +0x667: mov     %rax,%rcx
     +0x66a: and     $0x3,%rdx
     +0x66e: je      <mld_H87+0x691>
     +0x670: mov     %rax,%rcx
     +0x673: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x680: movzbl  (%r14,%rcx,1),%esi
     +0x685: xor     %sil,(%r12,%rcx,1)
     +0x689: inc     %rcx
     +0x68c: dec     %rdx
     +0x68f: jne     <mld_H87+0x680>
     +0x691: sub     %rbx,%rax
     +0x694: cmp     $0xfffffffffffffffc,%rax
     +0x698: ja      <mld_H87+0x6d3>
     +0x69a: nopw    0x0(%rax,%rax,1)
     +0x6a0: movzbl  (%r14,%rcx,1),%eax
     +0x6a5: xor     %al,(%r12,%rcx,1)
     +0x6a9: movzbl  0x1(%r14,%rcx,1),%eax
     +0x6af: xor     %al,0x1(%r12,%rcx,1)
     +0x6b4: movzbl  0x2(%r14,%rcx,1),%eax
     +0x6ba: xor     %al,0x2(%r12,%rcx,1)
     +0x6bf: movzbl  0x3(%r14,%rcx,1),%eax
     +0x6c5: xor     %al,0x3(%r12,%rcx,1)
     +0x6ca: add     $0x4,%rcx
     +0x6ce: cmp     %rcx,%rbx
     +0x6d1: jne     <mld_H87+0x6a0>
     +0x6d3: add     %ebx,%r15d
     +0x6d6: mov     %r15d,0xc8(%rsp)
     +0x6de: mov     %r15d,%eax
     +0x6e1: xorb    $0x1f,(%rsp,%rax,1)
     +0x6e5: xorb    $0x80,0x87(%rsp)
     +0x6ed: movl    $0x88,0xc8(%rsp)
     +0x6f8: mov     %rsp,%rbx
     +0x6fb: mov     %rbx,%rdi
     +0x6fe: call    <mldsa_keccakf1600_permute>
     +0x703: movaps  (%rsp),%xmm0
     +0x707: movaps  0x10(%rsp),%xmm1
     +0x70c: movaps  0x20(%rsp),%xmm2
     +0x711: movaps  0x30(%rsp),%xmm3
     +0x716: mov     0xd0(%rsp),%rax
     +0x71e: movups  %xmm3,0x30(%rax)
     +0x722: movups  %xmm2,0x20(%rax)
     +0x726: movups  %xmm1,0x10(%rax)
     +0x72a: movups  %xmm0,(%rax)
     +0x72d: xorps   %xmm0,%xmm0
     +0x730: movaps  %xmm0,(%rsp)
     +0x734: movaps  %xmm0,0x10(%rsp)
     +0x739: movaps  %xmm0,0x20(%rsp)
     +0x73e: movaps  %xmm0,0x30(%rsp)
     +0x743: movaps  %xmm0,0x40(%rsp)
     +0x748: movaps  %xmm0,0x50(%rsp)
     +0x74d: movaps  %xmm0,0x60(%rsp)
     +0x752: movaps  %xmm0,0x70(%rsp)
     +0x757: movaps  %xmm0,0x80(%rsp)
     +0x75f: movaps  %xmm0,0x90(%rsp)
     +0x767: movaps  %xmm0,0xa0(%rsp)
     +0x76f: movaps  %xmm0,0xb0(%rsp)
     +0x777: movaps  %xmm0,0xc0(%rsp)
     +0x77f: movaps  %xmm0,0xc0(%rsp)
     +0x787: movaps  %xmm0,0xb0(%rsp)
     +0x78f: movaps  %xmm0,0xa0(%rsp)
     +0x797: movaps  %xmm0,0x90(%rsp)
     +0x79f: movaps  %xmm0,0x80(%rsp)
     +0x7a7: movaps  %xmm0,0x70(%rsp)
     +0x7ac: movaps  %xmm0,0x60(%rsp)
     +0x7b1: movaps  %xmm0,0x50(%rsp)
     +0x7b6: movaps  %xmm0,0x40(%rsp)
     +0x7bb: movaps  %xmm0,0x30(%rsp)
     +0x7c0: movaps  %xmm0,0x20(%rsp)
     +0x7c5: movaps  %xmm0,0x10(%rsp)
     +0x7ca: movaps  %xmm0,(%rsp)
     +0x7ce: add     $0xd8,%rsp
     +0x7d5: pop     %rbx
     +0x7d6: pop     %r12
     +0x7d8: pop     %r13
     +0x7da: pop     %r14
     +0x7dc: pop     %r15
     +0x7de: pop     %rbp
     +0x7df: xor     %eax,%eax
     +0x7e1: xor     %ecx,%ecx
     +0x7e3: xor     %edi,%edi
     +0x7e5: xor     %edx,%edx
     +0x7e7: xor     %esi,%esi
     +0x7e9: xor     %r8d,%r8d
     +0x7ec: xor     %r9d,%r9d
     +0x7ef: ret     
     +0x7f0: cmp     $0x20,%rbx
     +0x7f4: jae     <mld_H87+0x807>
     +0x7f6: xor     %eax,%eax
     +0x7f8: jmp     <mld_H87+0x852>
     +0x7fa: cmp     $0x20,%r12
     +0x7fe: jae     <mld_H87+0x87f>
     +0x800: xor     %eax,%eax
     +0x802: jmp     <mld_H87+0x8d2>
     +0x807: mov     %rbx,%rax
     +0x80a: and     $0xffffffffffffffe0,%rax
     +0x80e: xor     %ecx,%ecx
     +0x810: movups  (%r14,%rcx,1),%xmm0
     +0x815: movups  0x10(%r14,%rcx,1),%xmm1
     +0x81b: movups  (%r12,%rcx,1),%xmm2
     +0x820: xorps   %xmm0,%xmm2
     +0x823: movups  0x10(%r12,%rcx,1),%xmm0
     +0x829: xorps   %xmm1,%xmm0
     +0x82c: movups  %xmm2,(%r12,%rcx,1)
     +0x831: movups  %xmm0,0x10(%r12,%rcx,1)
     +0x837: add     $0x20,%rcx
     +0x83b: cmp     %rcx,%rax
     +0x83e: jne     <mld_H87+0x810>
     +0x840: cmp     %rax,%rbx
     +0x843: je      <mld_H87+0x6d3>
     +0x849: test    $0x1c,%bl
     +0x84c: je      <mld_H87+0x664>
     +0x852: mov     %rax,%rcx
     +0x855: mov     %rbx,%rax
     +0x858: and     $0xfffffffffffffffc,%rax
     +0x85c: nopl    0x0(%rax)
     +0x860: mov     (%r14,%rcx,1),%edx
     +0x864: xor     %edx,(%r12,%rcx,1)
     +0x868: add     $0x4,%rcx
     +0x86c: cmp     %rcx,%rax
     +0x86f: jne     <mld_H87+0x860>
     +0x871: cmp     %rax,%rbx
     +0x874: je      <mld_H87+0x6d3>
     +0x87a: jmp     <mld_H87+0x664>
     +0x87f: mov     %r12,%rax
     +0x882: and     $0xffffffffffffffe0,%rax
     +0x886: xor     %ecx,%ecx
     +0x888: nopl    0x0(%rax,%rax,1)
     +0x890: movups  0x0(%r13,%rcx,1),%xmm0
     +0x896: movups  0x10(%r13,%rcx,1),%xmm1
     +0x89c: movups  0x0(%rbp,%rcx,1),%xmm2
     +0x8a1: xorps   %xmm0,%xmm2
     +0x8a4: movups  0x10(%rbp,%rcx,1),%xmm0
     +0x8a9: xorps   %xmm1,%xmm0
     +0x8ac: movups  %xmm2,0x0(%rbp,%rcx,1)
     +0x8b1: movups  %xmm0,0x10(%rbp,%rcx,1)
     +0x8b6: add     $0x20,%rcx
     +0x8ba: cmp     %rcx,%rax
     +0x8bd: jne     <mld_H87+0x890>
     +0x8bf: cmp     %rax,%r12
     +0x8c2: je      <mld_H87+0x511>
     +0x8c8: test    $0x1c,%r12b
     +0x8cc: je      <mld_H87+0x4a7>
     +0x8d2: mov     %rax,%rcx
     +0x8d5: mov     %r12,%rax
     +0x8d8: and     $0xfffffffffffffffc,%rax
     +0x8dc: nopl    0x0(%rax)
     +0x8e0: mov     0x0(%r13,%rcx,1),%edx
     +0x8e5: xor     %edx,0x0(%rbp,%rcx,1)
     +0x8e9: add     $0x4,%rcx
     +0x8ed: cmp     %rcx,%rax
     +0x8f0: jne     <mld_H87+0x8e0>
     +0x8f2: cmp     %rax,%r12
     +0x8f5: je      <mld_H87+0x511>
     +0x8fb: jmp     <mld_H87+0x4a7>
 ***)

let MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mld_H87"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The output is SHAKE256 of in1 || in2 || in3, the bytes M1,   *)
(* M2 and M3 as numbers. The last argument, in3len, is on the stack above    *)
(* the return address. The function saves six registers below the return     *)
(* address and reserves 216 bytes for the state and its position (at         *)
(* stackpointer - 264) and the saved output pointer, below which the calls   *)
(* of mldsa_keccakf1600_permute use 296 bytes with their return addresses:   *)
(* 560 bytes of stack below the return address in all. The stack is aligned  *)
(* as the ABI requires (stackpointer + 8 a multiple of 16), since the state  *)
(* is zeroed with MOVAPS. The output is the first 64 bytes of the state      *)
(* after one permutation. The code does not call memcpy; the hypothesis on   *)
(* its contract is kept, as in mld_H44 and mld_H65.                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> !out in1 in1len in2 in2len in3 in3len M1 M2 M3 pc stackpointer
   returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ~(in1len = 0) /\ aligned 16 (word_add stackpointer (word 8)) /\
        ALL (nonoverlapping (word_sub stackpointer (word 560),560))
         [(out,64); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        nonoverlapping (out,64) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(out,64); (word_sub stackpointer (word 560),560)]
         [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mld_H87) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; in1; word in1len; in2; word in2len;
                               in3] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  word in3len /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(in1,in1len)) s = M1 /\
                  read (memory :> bytes(in2,in2len)) s = M2 /\
                  read (memory :> bytes(in3,in3len)) s = M3)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(out,64)) s =
                  num_of_bytelist
                   (list_of_seq
                     (mld_shake256_byte (in1len + in2len + in3len)
                       (M1 + 2 EXP (8 * in1len) *
                             (M2 + 2 EXP (8 * in2len) * M3)))
                     64))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out,64);
                memory :> bytes(word_sub stackpointer (word 560),560)])`;;

let MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the lengths only (which give   *)
(* the calls and their arguments), with all accesses within the output, the  *)
(* inputs, the stack, the return address, the arguments on the stack and the *)
(* round constants of the permutation, and the writes within the output and  *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e out in1 in1len in2 in2len in3 in3len M1 M2 M3 pc
            stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ~(in1len = 0) /\ aligned 16 (word_add stackpointer (word 8)) /\
        ALL (nonoverlapping (word_sub stackpointer (word 560),560))
         [(out,64); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        nonoverlapping (out,64) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(out,64); (word_sub stackpointer (word 560),560)]
         [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mld_H87) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; in1; word in1len; in2; word in2len;
                               in3] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
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
                  read (memory :> bytes(out,64)) s =
                  num_of_bytelist
                   (list_of_seq
                     (mld_shake256_byte (in1len + in2len + in3len)
                       (M1 + 2 EXP (8 * in1len) *
                             (M2 + 2 EXP (8 * in2len) * M3)))
                     64) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out in1 in1len in2 in2len in3 in3len mc pc
                                 (word_sub stackpointer (word 560))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,64; in1,in1len; in2,in2len; in3,in3len;
                       word_sub stackpointer (word 560),560; stackpointer,8;
                       word(pc + got_memcpy),8; ea,el;
                       word_add stackpointer (word 8),8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,64; word_sub stackpointer (word 560),560]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out,64);
                memory :> bytes(word_sub stackpointer (word 560),560)])`;;

let MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e out in1 in1len in2 in2len in3 in3len pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ~(in1len = 0) /\ aligned 16 (word_add stackpointer (word 8)) /\
        ALL (nonoverlapping (word_sub stackpointer (word 560),560))
         [(out,64); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        nonoverlapping (out,64) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(out,64); (word_sub stackpointer (word 560),560)]
         [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mld_H87) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; in1; word in1len; in2; word in2len;
                               in3] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  word in3len /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out in1 in1len in2 in2len in3 in3len mc pc
                                 (word_sub stackpointer (word 560))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,64; in1,in1len; in2,in2len; in3,in3len;
                       word_sub stackpointer (word 560),560; stackpointer,8;
                       word(pc + got_memcpy),8; ea,el;
                       word_add stackpointer (word 8),8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,64; word_sub stackpointer (word 560),560]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out,64);
                memory :> bytes(word_sub stackpointer (word 560),560)])`;;

let MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
