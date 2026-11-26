(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of four polynomials with coefficients in [-2,2] for ML-DSA-87 by *)
(* rejection: the statement. This is the code for                            *)
(* mldsa87_poly_uniform_eta_4x (mld_poly_uniform_eta_4x in poly_kl.c) from   *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3 as *)
(* one translation unit and MLD_CONFIG_REDUCE_RAM (see                       *)
(* mldsa_native/README.md). clang inlines the fourfold SHAKE256 and          *)
(* mld_rej_eta_c: the code extends the seed of 64 bytes with each of the     *)
(* four nonce bytes and a zero byte, zeroes four Keccak states with memset,  *)
(* XORs the extended seeds and the padding into them, permutes them with     *)
(* mldsa_keccakf1600_permute, copies the first block of 136 bytes of each to *)
(* a buffer with memcpy and samples the coefficients from it, and then       *)
(* squeezes one more block of each and samples from those polynomials that   *)
(* need more until each has 256 coefficients, before zeroing the states, the *)
(* buffers and the extended seeds with memset. It calls memset and memcpy    *)
(* through the PLT, under the contracts of utils/mldsa_native_libc.ml, which *)
(* require the direction flag to be clear, as the ABI requires on entry. It  *)
(* is verified in the whole image (see libmldsa.ml) against                  *)
(* mld_poly_uniform_eta of common/mldsa_native_sampling.ml, using the        *)
(* theorems for the callees, and assuming that the SHAKE256 output of each   *)
(* extended seed has 256 acceptable nibbles (mld_rej_eta_terminates),        *)
(* without which the code does not terminate. The nonces are the low bytes   *)
(* of the sixth argument and of the three arguments that the caller puts on  *)
(* the stack, as the System V ABI passes them. It is also shown to be        *)
(* constant time and memory safe, with the events depending on the seed only *)
(* through which nibbles of the SHAKE256 outputs mld_rej_eta_c accepts,      *)
(* which it declassifies (mld_poly_uniform_eta_declass).                     *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa87_poly_uniform_eta_4x:
       +0x0: push    %rbp
       +0x1: mov     %rsp,%rbp
       +0x4: push    %r15
       +0x6: push    %r14
       +0x8: push    %r13
       +0xa: push    %r12
       +0xc: push    %rbx
       +0xd: and     $0xffffffffffffffe0,%rsp
      +0x11: sub     $0x780,%rsp
      +0x18: mov     %rcx,0x30(%rsp)
      +0x1d: mov     %rdx,0x28(%rsp)
      +0x22: mov     %rsi,0x20(%rsp)
      +0x27: mov     %rdi,0x38(%rsp)
      +0x2c: movzbl  0x20(%rbp),%eax
      +0x30: movzbl  0x18(%rbp),%ecx
      +0x34: movzbl  0x10(%rbp),%edx
      +0x38: movups  (%r8),%xmm0
      +0x3c: movups  0x10(%r8),%xmm1
      +0x41: movups  0x20(%r8),%xmm2
      +0x46: movups  0x30(%r8),%xmm3
      +0x4b: movaps  %xmm3,0x70(%rsp)
      +0x50: movaps  %xmm2,0x60(%rsp)
      +0x55: movaps  %xmm1,0x50(%rsp)
      +0x5a: movaps  %xmm0,0x40(%rsp)
      +0x5f: movups  (%r8),%xmm0
      +0x63: movups  0x10(%r8),%xmm1
      +0x68: movups  0x20(%r8),%xmm2
      +0x6d: movups  0x30(%r8),%xmm3
      +0x72: movaps  %xmm3,0xd0(%rsp)
      +0x7a: movaps  %xmm2,0xc0(%rsp)
      +0x82: movaps  %xmm1,0xb0(%rsp)
      +0x8a: movaps  %xmm0,0xa0(%rsp)
      +0x92: movups  (%r8),%xmm0
      +0x96: movups  0x10(%r8),%xmm1
      +0x9b: movups  0x20(%r8),%xmm2
      +0xa0: movups  0x30(%r8),%xmm3
      +0xa5: movaps  %xmm3,0x130(%rsp)
      +0xad: movaps  %xmm2,0x120(%rsp)
      +0xb5: movaps  %xmm1,0x110(%rsp)
      +0xbd: movaps  %xmm0,0x100(%rsp)
      +0xc5: movups  (%r8),%xmm0
      +0xc9: movups  0x10(%r8),%xmm1
      +0xce: movups  0x20(%r8),%xmm2
      +0xd3: movups  0x30(%r8),%xmm3
      +0xd8: movaps  %xmm0,0x160(%rsp)
      +0xe0: movaps  %xmm1,0x170(%rsp)
      +0xe8: movaps  %xmm2,0x180(%rsp)
      +0xf0: movaps  %xmm3,0x190(%rsp)
      +0xf8: mov     %r9b,0x80(%rsp)
     +0x100: mov     %dl,0xe0(%rsp)
     +0x107: mov     %cl,0x140(%rsp)
     +0x10e: mov     %al,0x1a0(%rsp)
     +0x115: movb    $0x0,0x81(%rsp)
     +0x11d: movb    $0x0,0xe1(%rsp)
     +0x125: movb    $0x0,0x141(%rsp)
     +0x12d: movb    $0x0,0x1a1(%rsp)
     +0x135: lea     0x1c0(%rsp),%r13
     +0x13d: xor     %ebx,%ebx
     +0x13f: mov     $0x320,%edx
     +0x144: mov     %r13,%rdi
     +0x147: xor     %esi,%esi
     +0x149: call    <memset>
     +0x14e: movaps  0x1c0(%rsp),%xmm0
     +0x156: movaps  0x1d0(%rsp),%xmm1
     +0x15e: movaps  0x1e0(%rsp),%xmm2
     +0x166: movaps  0x1f0(%rsp),%xmm3
     +0x16e: xorps   0x40(%rsp),%xmm0
     +0x173: xorps   0x50(%rsp),%xmm1
     +0x178: movaps  %xmm0,0x1c0(%rsp)
     +0x180: movaps  %xmm1,0x1d0(%rsp)
     +0x188: xorps   0x60(%rsp),%xmm2
     +0x18d: xorps   0x70(%rsp),%xmm3
     +0x192: movaps  %xmm2,0x1e0(%rsp)
     +0x19a: movaps  %xmm3,0x1f0(%rsp)
     +0x1a2: movdqa  0x200(%rsp),%xmm0
     +0x1ab: pxor    0x80(%rsp),%xmm0
     +0x1b4: movd    %xmm0,%eax
     +0x1b8: mov     %ax,0x200(%rsp)
     +0x1c0: movups  0x288(%rsp),%xmm0
     +0x1c8: xorps   0xa0(%rsp),%xmm0
     +0x1d0: movups  0x298(%rsp),%xmm1
     +0x1d8: xorps   0xb0(%rsp),%xmm1
     +0x1e0: movups  %xmm0,0x288(%rsp)
     +0x1e8: movups  %xmm1,0x298(%rsp)
     +0x1f0: movups  0x2a8(%rsp),%xmm0
     +0x1f8: xorps   0xc0(%rsp),%xmm0
     +0x200: movups  0x2b8(%rsp),%xmm1
     +0x208: xorps   0xd0(%rsp),%xmm1
     +0x210: movups  %xmm0,0x2a8(%rsp)
     +0x218: movups  %xmm1,0x2b8(%rsp)
     +0x220: movq    0x2c8(%rsp),%xmm0
     +0x229: pxor    0xe0(%rsp),%xmm0
     +0x232: movd    %xmm0,%eax
     +0x236: mov     %ax,0x2c8(%rsp)
     +0x23e: movaps  0x350(%rsp),%xmm0
     +0x246: movaps  0x360(%rsp),%xmm1
     +0x24e: xorps   0x100(%rsp),%xmm0
     +0x256: xorps   0x110(%rsp),%xmm1
     +0x25e: movaps  %xmm0,0x350(%rsp)
     +0x266: movaps  %xmm1,0x360(%rsp)
     +0x26e: movaps  0x370(%rsp),%xmm0
     +0x276: movaps  0x380(%rsp),%xmm1
     +0x27e: xorps   0x120(%rsp),%xmm0
     +0x286: xorps   0x130(%rsp),%xmm1
     +0x28e: movaps  %xmm0,0x370(%rsp)
     +0x296: movaps  %xmm1,0x380(%rsp)
     +0x29e: movdqa  0x390(%rsp),%xmm0
     +0x2a7: pxor    0x140(%rsp),%xmm0
     +0x2b0: movd    %xmm0,%eax
     +0x2b4: mov     %ax,0x390(%rsp)
     +0x2bc: movups  0x418(%rsp),%xmm0
     +0x2c4: movups  0x428(%rsp),%xmm1
     +0x2cc: xorps   0x160(%rsp),%xmm0
     +0x2d4: xorps   0x170(%rsp),%xmm1
     +0x2dc: movups  %xmm0,0x418(%rsp)
     +0x2e4: movups  %xmm1,0x428(%rsp)
     +0x2ec: movups  0x438(%rsp),%xmm0
     +0x2f4: movups  0x448(%rsp),%xmm1
     +0x2fc: xorps   0x180(%rsp),%xmm0
     +0x304: xorps   0x190(%rsp),%xmm1
     +0x30c: movups  %xmm0,0x438(%rsp)
     +0x314: movups  %xmm1,0x448(%rsp)
     +0x31c: movq    0x458(%rsp),%xmm0
     +0x325: pxor    0x1a0(%rsp),%xmm0
     +0x32e: movd    %xmm0,%eax
     +0x332: mov     %ax,0x458(%rsp)
     +0x33a: xorb    $0x1f,0x202(%rsp)
     +0x342: xorb    $0x1f,0x2ca(%rsp)
     +0x34a: xorb    $0x1f,0x392(%rsp)
     +0x352: xorb    $0x1f,0x45a(%rsp)
     +0x35a: xorb    $0x80,0x247(%rsp)
     +0x362: lea     0x288(%rsp),%r14
     +0x36a: xorb    $0x80,0x30f(%rsp)
     +0x372: lea     0x350(%rsp),%r15
     +0x37a: xorb    $0x80,0x3d7(%rsp)
     +0x382: lea     0x418(%rsp),%r12
     +0x38a: xorb    $0x80,0x49f(%rsp)
     +0x392: mov     %r13,%rdi
     +0x395: call    <mldsa_keccakf1600_permute>
     +0x39a: mov     %r14,%rdi
     +0x39d: call    <mldsa_keccakf1600_permute>
     +0x3a2: mov     %r15,%rdi
     +0x3a5: call    <mldsa_keccakf1600_permute>
     +0x3aa: mov     %r12,%rdi
     +0x3ad: call    <mldsa_keccakf1600_permute>
     +0x3b2: lea     0x4e0(%rsp),%rdi
     +0x3ba: mov     $0x88,%edx
     +0x3bf: mov     %r13,%rsi
     +0x3c2: call    <memcpy>
     +0x3c7: lea     0x580(%rsp),%rdi
     +0x3cf: mov     $0x88,%edx
     +0x3d4: mov     %r14,%rsi
     +0x3d7: call    <memcpy>
     +0x3dc: lea     0x620(%rsp),%rdi
     +0x3e4: mov     $0x88,%edx
     +0x3e9: mov     %r15,%rsi
     +0x3ec: call    <memcpy>
     +0x3f1: lea     0x6c0(%rsp),%rdi
     +0x3f9: mov     $0x88,%edx
     +0x3fe: mov     %r12,%rsi
     +0x401: call    <memcpy>
     +0x406: xor     %r13d,%r13d
     +0x409: nopl    0x0(%rax)
     +0x410: movzbl  0x4e0(%rsp,%rbx,1),%eax
     +0x418: mov     %eax,%ecx
     +0x41a: and     $0xf,%ecx
     +0x41d: cmp     $0xf,%ecx
     +0x420: jne     <mldsa87_poly_uniform_eta_4x+0x440>
     +0x422: mov     0x38(%rsp),%rsi
     +0x427: shr     $0x4,%eax
     +0x42a: cmp     $0xf,%eax
     +0x42d: jne     <mldsa87_poly_uniform_eta_4x+0x467>
     +0x42f: jmp     <mldsa87_poly_uniform_eta_4x+0x48a>
     +0x431: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x440: imul    $0xcd,%ecx,%edx
     +0x446: shr     $0xa,%edx
     +0x449: lea     (%rdx,%rdx,4),%edx
     +0x44c: sub     %ecx,%edx
     +0x44e: add     $0x2,%edx
     +0x451: mov     %r13d,%ecx
     +0x454: inc     %r13d
     +0x457: mov     0x38(%rsp),%rsi
     +0x45c: mov     %edx,(%rsi,%rcx,4)
     +0x45f: shr     $0x4,%eax
     +0x462: cmp     $0xf,%eax
     +0x465: je      <mldsa87_poly_uniform_eta_4x+0x48a>
     +0x467: cmp     $0xff,%r13d
     +0x46e: ja      <mldsa87_poly_uniform_eta_4x+0x48a>
     +0x470: imul    $0xcd,%eax,%ecx
     +0x476: shr     $0xa,%ecx
     +0x479: lea     (%rcx,%rcx,4),%ecx
     +0x47c: sub     %eax,%ecx
     +0x47e: add     $0x2,%ecx
     +0x481: mov     %r13d,%eax
     +0x484: inc     %r13d
     +0x487: mov     %ecx,(%rsi,%rax,4)
     +0x48a: cmp     $0x100,%r13d
     +0x491: setb    %r11b
     +0x495: jae     <mldsa87_poly_uniform_eta_4x+0x4a8>
     +0x497: cmp     $0x87,%rbx
     +0x49e: lea     0x1(%rbx),%rbx
     +0x4a2: jb      <mldsa87_poly_uniform_eta_4x+0x410>
     +0x4a8: xor     %eax,%eax
     +0x4aa: xor     %ebx,%ebx
     +0x4ac: mov     0x30(%rsp),%rdi
     +0x4b1: mov     0x28(%rsp),%r8
     +0x4b6: mov     0x20(%rsp),%r9
     +0x4bb: nopl    0x0(%rax,%rax,1)
     +0x4c0: movzbl  0x580(%rsp,%rax,1),%ecx
     +0x4c8: mov     %ecx,%edx
     +0x4ca: and     $0xf,%edx
     +0x4cd: cmp     $0xf,%edx
     +0x4d0: je      <mldsa87_poly_uniform_eta_4x+0x4eb>
     +0x4d2: imul    $0xcd,%edx,%esi
     +0x4d8: shr     $0xa,%esi
     +0x4db: lea     (%rsi,%rsi,4),%esi
     +0x4de: sub     %edx,%esi
     +0x4e0: add     $0x2,%esi
     +0x4e3: mov     %ebx,%edx
     +0x4e5: inc     %ebx
     +0x4e7: mov     %esi,(%r9,%rdx,4)
     +0x4eb: shr     $0x4,%ecx
     +0x4ee: cmp     $0xf,%ecx
     +0x4f1: je      <mldsa87_poly_uniform_eta_4x+0x514>
     +0x4f3: cmp     $0xff,%ebx
     +0x4f9: ja      <mldsa87_poly_uniform_eta_4x+0x514>
     +0x4fb: imul    $0xcd,%ecx,%edx
     +0x501: shr     $0xa,%edx
     +0x504: lea     (%rdx,%rdx,4),%edx
     +0x507: sub     %ecx,%edx
     +0x509: add     $0x2,%edx
     +0x50c: mov     %ebx,%ecx
     +0x50e: inc     %ebx
     +0x510: mov     %edx,(%r9,%rcx,4)
     +0x514: cmp     $0x100,%ebx
     +0x51a: setb    %r10b
     +0x51e: jae     <mldsa87_poly_uniform_eta_4x+0x52c>
     +0x520: cmp     $0x87,%rax
     +0x526: lea     0x1(%rax),%rax
     +0x52a: jb      <mldsa87_poly_uniform_eta_4x+0x4c0>
     +0x52c: xor     %eax,%eax
     +0x52e: xor     %r14d,%r14d
     +0x531: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x540: movzbl  0x620(%rsp,%rax,1),%ecx
     +0x548: mov     %ecx,%edx
     +0x54a: and     $0xf,%edx
     +0x54d: cmp     $0xf,%edx
     +0x550: je      <mldsa87_poly_uniform_eta_4x+0x56d>
     +0x552: imul    $0xcd,%edx,%esi
     +0x558: shr     $0xa,%esi
     +0x55b: lea     (%rsi,%rsi,4),%esi
     +0x55e: sub     %edx,%esi
     +0x560: add     $0x2,%esi
     +0x563: mov     %r14d,%edx
     +0x566: inc     %r14d
     +0x569: mov     %esi,(%r8,%rdx,4)
     +0x56d: shr     $0x4,%ecx
     +0x570: cmp     $0xf,%ecx
     +0x573: je      <mldsa87_poly_uniform_eta_4x+0x599>
     +0x575: cmp     $0xff,%r14d
     +0x57c: ja      <mldsa87_poly_uniform_eta_4x+0x599>
     +0x57e: imul    $0xcd,%ecx,%edx
     +0x584: shr     $0xa,%edx
     +0x587: lea     (%rdx,%rdx,4),%edx
     +0x58a: sub     %ecx,%edx
     +0x58c: add     $0x2,%edx
     +0x58f: mov     %r14d,%ecx
     +0x592: inc     %r14d
     +0x595: mov     %edx,(%r8,%rcx,4)
     +0x599: cmp     $0x100,%r14d
     +0x5a0: setb    %r9b
     +0x5a4: jae     <mldsa87_poly_uniform_eta_4x+0x5b2>
     +0x5a6: cmp     $0x87,%rax
     +0x5ac: lea     0x1(%rax),%rax
     +0x5b0: jb      <mldsa87_poly_uniform_eta_4x+0x540>
     +0x5b2: xor     %eax,%eax
     +0x5b4: xor     %r15d,%r15d
     +0x5b7: nopw    0x0(%rax,%rax,1)
     +0x5c0: movzbl  0x6c0(%rsp,%rax,1),%ecx
     +0x5c8: mov     %ecx,%edx
     +0x5ca: and     $0xf,%edx
     +0x5cd: cmp     $0xf,%edx
     +0x5d0: je      <mldsa87_poly_uniform_eta_4x+0x5ec>
     +0x5d2: imul    $0xcd,%edx,%esi
     +0x5d8: shr     $0xa,%esi
     +0x5db: lea     (%rsi,%rsi,4),%esi
     +0x5de: sub     %edx,%esi
     +0x5e0: add     $0x2,%esi
     +0x5e3: mov     %r15d,%edx
     +0x5e6: inc     %r15d
     +0x5e9: mov     %esi,(%rdi,%rdx,4)
     +0x5ec: shr     $0x4,%ecx
     +0x5ef: cmp     $0xf,%ecx
     +0x5f2: je      <mldsa87_poly_uniform_eta_4x+0x617>
     +0x5f4: cmp     $0xff,%r15d
     +0x5fb: ja      <mldsa87_poly_uniform_eta_4x+0x617>
     +0x5fd: imul    $0xcd,%ecx,%edx
     +0x603: shr     $0xa,%edx
     +0x606: lea     (%rdx,%rdx,4),%edx
     +0x609: sub     %ecx,%edx
     +0x60b: add     $0x2,%edx
     +0x60e: mov     %r15d,%ecx
     +0x611: inc     %r15d
     +0x614: mov     %edx,(%rdi,%rcx,4)
     +0x617: cmp     $0x100,%r15d
     +0x61e: setb    %cl
     +0x621: jae     <mldsa87_poly_uniform_eta_4x+0x62f>
     +0x623: cmp     $0x87,%rax
     +0x629: lea     0x1(%rax),%rax
     +0x62d: jb      <mldsa87_poly_uniform_eta_4x+0x5c0>
     +0x62f: cmp     $0x100,%r13d
     +0x636: jb      <mldsa87_poly_uniform_eta_4x+0x660>
     +0x638: cmp     $0x100,%ebx
     +0x63e: jb      <mldsa87_poly_uniform_eta_4x+0x660>
     +0x640: cmp     $0x100,%r14d
     +0x647: jb      <mldsa87_poly_uniform_eta_4x+0x660>
     +0x649: cmp     $0xff,%r15d
     +0x650: ja      <mldsa87_poly_uniform_eta_4x+0x982>
     +0x656: cs      nopw 0x0(%rax,%rax,1)
     +0x660: mov     %r11b,0x1c(%rsp)
     +0x665: mov     %r10b,0x1d(%rsp)
     +0x66a: mov     %r9b,0x1e(%rsp)
     +0x66f: mov     %cl,0x1f(%rsp)
     +0x673: lea     0x1c0(%rsp),%rdi
     +0x67b: call    <mldsa_keccakf1600_permute>
     +0x680: lea     0x288(%rsp),%r12
     +0x688: mov     %r12,%rdi
     +0x68b: call    <mldsa_keccakf1600_permute>
     +0x690: lea     0x350(%rsp),%rdi
     +0x698: call    <mldsa_keccakf1600_permute>
     +0x69d: lea     0x418(%rsp),%rdi
     +0x6a5: call    <mldsa_keccakf1600_permute>
     +0x6aa: mov     $0x88,%edx
     +0x6af: lea     0x4e0(%rsp),%rdi
     +0x6b7: lea     0x1c0(%rsp),%rsi
     +0x6bf: call    <memcpy>
     +0x6c4: mov     $0x88,%edx
     +0x6c9: lea     0x580(%rsp),%rdi
     +0x6d1: mov     %r12,%rsi
     +0x6d4: call    <memcpy>
     +0x6d9: mov     $0x88,%edx
     +0x6de: lea     0x620(%rsp),%rdi
     +0x6e6: lea     0x350(%rsp),%rsi
     +0x6ee: call    <memcpy>
     +0x6f3: mov     $0x88,%edx
     +0x6f8: lea     0x6c0(%rsp),%rdi
     +0x700: lea     0x418(%rsp),%rsi
     +0x708: call    <memcpy>
     +0x70d: testb   $0x1,0x1c(%rsp)
     +0x712: je      <mldsa87_poly_uniform_eta_4x+0x7a0>
     +0x718: xor     %eax,%eax
     +0x71a: mov     0x30(%rsp),%rdi
     +0x71f: mov     0x28(%rsp),%r8
     +0x724: mov     0x20(%rsp),%r9
     +0x729: mov     0x38(%rsp),%r10
     +0x72e: xchg    %ax,%ax
     +0x730: movzbl  0x4e0(%rsp,%rax,1),%ecx
     +0x738: mov     %ecx,%edx
     +0x73a: and     $0xf,%edx
     +0x73d: cmp     $0xf,%edx
     +0x740: je      <mldsa87_poly_uniform_eta_4x+0x75d>
     +0x742: imul    $0xcd,%edx,%esi
     +0x748: shr     $0xa,%esi
     +0x74b: lea     (%rsi,%rsi,4),%esi
     +0x74e: sub     %edx,%esi
     +0x750: add     $0x2,%esi
     +0x753: mov     %r13d,%edx
     +0x756: inc     %r13d
     +0x759: mov     %esi,(%r10,%rdx,4)
     +0x75d: shr     $0x4,%ecx
     +0x760: cmp     $0xf,%ecx
     +0x763: je      <mldsa87_poly_uniform_eta_4x+0x789>
     +0x765: cmp     $0xff,%r13d
     +0x76c: ja      <mldsa87_poly_uniform_eta_4x+0x789>
     +0x76e: imul    $0xcd,%ecx,%edx
     +0x774: shr     $0xa,%edx
     +0x777: lea     (%rdx,%rdx,4),%edx
     +0x77a: sub     %ecx,%edx
     +0x77c: add     $0x2,%edx
     +0x77f: mov     %r13d,%ecx
     +0x782: inc     %r13d
     +0x785: mov     %edx,(%r10,%rcx,4)
     +0x789: cmp     $0xff,%r13d
     +0x790: ja      <mldsa87_poly_uniform_eta_4x+0x7af>
     +0x792: cmp     $0x87,%rax
     +0x798: lea     0x1(%rax),%rax
     +0x79c: jb      <mldsa87_poly_uniform_eta_4x+0x730>
     +0x79e: jmp     <mldsa87_poly_uniform_eta_4x+0x7af>
     +0x7a0: mov     0x30(%rsp),%rdi
     +0x7a5: mov     0x28(%rsp),%r8
     +0x7aa: mov     0x20(%rsp),%r9
     +0x7af: testb   $0x1,0x1d(%rsp)
     +0x7b4: je      <mldsa87_poly_uniform_eta_4x+0x828>
     +0x7b6: xor     %eax,%eax
     +0x7b8: nopl    0x0(%rax,%rax,1)
     +0x7c0: movzbl  0x580(%rsp,%rax,1),%ecx
     +0x7c8: mov     %ecx,%edx
     +0x7ca: and     $0xf,%edx
     +0x7cd: cmp     $0xf,%edx
     +0x7d0: je      <mldsa87_poly_uniform_eta_4x+0x7eb>
     +0x7d2: imul    $0xcd,%edx,%esi
     +0x7d8: shr     $0xa,%esi
     +0x7db: lea     (%rsi,%rsi,4),%esi
     +0x7de: sub     %edx,%esi
     +0x7e0: add     $0x2,%esi
     +0x7e3: mov     %ebx,%edx
     +0x7e5: inc     %ebx
     +0x7e7: mov     %esi,(%r9,%rdx,4)
     +0x7eb: shr     $0x4,%ecx
     +0x7ee: cmp     $0xf,%ecx
     +0x7f1: je      <mldsa87_poly_uniform_eta_4x+0x814>
     +0x7f3: cmp     $0xff,%ebx
     +0x7f9: ja      <mldsa87_poly_uniform_eta_4x+0x814>
     +0x7fb: imul    $0xcd,%ecx,%edx
     +0x801: shr     $0xa,%edx
     +0x804: lea     (%rdx,%rdx,4),%edx
     +0x807: sub     %ecx,%edx
     +0x809: add     $0x2,%edx
     +0x80c: mov     %ebx,%ecx
     +0x80e: inc     %ebx
     +0x810: mov     %edx,(%r9,%rcx,4)
     +0x814: cmp     $0xff,%ebx
     +0x81a: ja      <mldsa87_poly_uniform_eta_4x+0x828>
     +0x81c: cmp     $0x87,%rax
     +0x822: lea     0x1(%rax),%rax
     +0x826: jb      <mldsa87_poly_uniform_eta_4x+0x7c0>
     +0x828: testb   $0x1,0x1e(%rsp)
     +0x82d: je      <mldsa87_poly_uniform_eta_4x+0x8ae>
     +0x82f: xor     %eax,%eax
     +0x831: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x840: movzbl  0x620(%rsp,%rax,1),%ecx
     +0x848: mov     %ecx,%edx
     +0x84a: and     $0xf,%edx
     +0x84d: cmp     $0xf,%edx
     +0x850: je      <mldsa87_poly_uniform_eta_4x+0x86d>
     +0x852: imul    $0xcd,%edx,%esi
     +0x858: shr     $0xa,%esi
     +0x85b: lea     (%rsi,%rsi,4),%esi
     +0x85e: sub     %edx,%esi
     +0x860: add     $0x2,%esi
     +0x863: mov     %r14d,%edx
     +0x866: inc     %r14d
     +0x869: mov     %esi,(%r8,%rdx,4)
     +0x86d: shr     $0x4,%ecx
     +0x870: cmp     $0xf,%ecx
     +0x873: je      <mldsa87_poly_uniform_eta_4x+0x899>
     +0x875: cmp     $0xff,%r14d
     +0x87c: ja      <mldsa87_poly_uniform_eta_4x+0x899>
     +0x87e: imul    $0xcd,%ecx,%edx
     +0x884: shr     $0xa,%edx
     +0x887: lea     (%rdx,%rdx,4),%edx
     +0x88a: sub     %ecx,%edx
     +0x88c: add     $0x2,%edx
     +0x88f: mov     %r14d,%ecx
     +0x892: inc     %r14d
     +0x895: mov     %edx,(%r8,%rcx,4)
     +0x899: cmp     $0xff,%r14d
     +0x8a0: ja      <mldsa87_poly_uniform_eta_4x+0x8ae>
     +0x8a2: cmp     $0x87,%rax
     +0x8a8: lea     0x1(%rax),%rax
     +0x8ac: jb      <mldsa87_poly_uniform_eta_4x+0x840>
     +0x8ae: testb   $0x1,0x1f(%rsp)
     +0x8b3: je      <mldsa87_poly_uniform_eta_4x+0x92c>
     +0x8b5: xor     %eax,%eax
     +0x8b7: nopw    0x0(%rax,%rax,1)
     +0x8c0: movzbl  0x6c0(%rsp,%rax,1),%ecx
     +0x8c8: mov     %ecx,%edx
     +0x8ca: and     $0xf,%edx
     +0x8cd: cmp     $0xf,%edx
     +0x8d0: je      <mldsa87_poly_uniform_eta_4x+0x8ec>
     +0x8d2: imul    $0xcd,%edx,%esi
     +0x8d8: shr     $0xa,%esi
     +0x8db: lea     (%rsi,%rsi,4),%esi
     +0x8de: sub     %edx,%esi
     +0x8e0: add     $0x2,%esi
     +0x8e3: mov     %r15d,%edx
     +0x8e6: inc     %r15d
     +0x8e9: mov     %esi,(%rdi,%rdx,4)
     +0x8ec: shr     $0x4,%ecx
     +0x8ef: cmp     $0xf,%ecx
     +0x8f2: je      <mldsa87_poly_uniform_eta_4x+0x917>
     +0x8f4: cmp     $0xff,%r15d
     +0x8fb: ja      <mldsa87_poly_uniform_eta_4x+0x917>
     +0x8fd: imul    $0xcd,%ecx,%edx
     +0x903: shr     $0xa,%edx
     +0x906: lea     (%rdx,%rdx,4),%edx
     +0x909: sub     %ecx,%edx
     +0x90b: add     $0x2,%edx
     +0x90e: mov     %r15d,%ecx
     +0x911: inc     %r15d
     +0x914: mov     %edx,(%rdi,%rcx,4)
     +0x917: cmp     $0xff,%r15d
     +0x91e: ja      <mldsa87_poly_uniform_eta_4x+0x92c>
     +0x920: cmp     $0x87,%rax
     +0x926: lea     0x1(%rax),%rax
     +0x92a: jb      <mldsa87_poly_uniform_eta_4x+0x8c0>
     +0x92c: cmp     $0x100,%ebx
     +0x932: setb    %r10b
     +0x936: cmp     $0x100,%r14d
     +0x93d: setb    %r9b
     +0x941: cmp     $0x100,%r15d
     +0x948: setb    %cl
     +0x94b: cmp     $0x100,%r13d
     +0x952: setb    %r11b
     +0x956: jb      <mldsa87_poly_uniform_eta_4x+0x660>
     +0x95c: cmp     $0x100,%ebx
     +0x962: jb      <mldsa87_poly_uniform_eta_4x+0x660>
     +0x968: cmp     $0x100,%r14d
     +0x96f: jb      <mldsa87_poly_uniform_eta_4x+0x660>
     +0x975: cmp     $0x100,%r15d
     +0x97c: jb      <mldsa87_poly_uniform_eta_4x+0x660>
     +0x982: lea     0x1c0(%rsp),%rbx
     +0x98a: mov     $0x320,%edx
     +0x98f: mov     %rbx,%rdi
     +0x992: xor     %esi,%esi
     +0x994: call    <memset>
     +0x999: lea     0x4e0(%rsp),%rbx
     +0x9a1: mov     $0x280,%edx
     +0x9a6: mov     %rbx,%rdi
     +0x9a9: xor     %esi,%esi
     +0x9ab: call    <memset>
     +0x9b0: lea     0x40(%rsp),%rbx
     +0x9b5: mov     $0x180,%edx
     +0x9ba: mov     %rbx,%rdi
     +0x9bd: xor     %esi,%esi
     +0x9bf: call    <memset>
     +0x9c4: lea     -0x28(%rbp),%rsp
     +0x9c8: pop     %rbx
     +0x9c9: pop     %r12
     +0x9cb: pop     %r13
     +0x9cd: pop     %r14
     +0x9cf: pop     %r15
     +0x9d1: pop     %rbp
     +0x9d2: xor     %eax,%eax
     +0x9d4: xor     %ecx,%ecx
     +0x9d6: xor     %edi,%edi
     +0x9d8: xor     %edx,%edx
     +0x9da: xor     %esi,%esi
     +0x9dc: xor     %r8d,%r8d
     +0x9df: xor     %r9d,%r9d
     +0x9e2: xor     %r10d,%r10d
     +0x9e5: xor     %r11d,%r11d
     +0x9e8: ret     
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa87_poly_uniform_eta_4x";
    layout_range "plt_memcpy";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The seed is the 64 bytes sd at seed, and polynomial j        *)
(* becomes mld_poly_uniform_eta 2 sd of the nonce j, the low byte of nj, if  *)
(* the SHAKE256 output of the extended seed has 256 acceptable nibbles. The  *)
(* nonces n1, n2 and n3 are in the 8 bytes each above the return address.    *)
(* The function saves RBP, the frame pointer, and five more registers below  *)
(* the return address, lowers RSP by up to 31 bytes to align it to 32 bytes, *)
(* and then reserves 1920 bytes for the arguments, the extended seeds, the   *)
(* states, the buffers and the flags, below which the calls of               *)
(* mldsa_keccakf1600_permute use 296 bytes, with their return address: 2295  *)
(* bytes of stack below the return address in all.                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !r0 r1 r2 r3 seed sd n0 n1 n2 n3 pc stackpointer
   returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n3:byte))) /\
        PAIRWISE nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2295),2295)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024)]
         [(stackpointer,32)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2295),2295)]
         [(seed,64); (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_poly_uniform_eta_4x) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r0; r1; r2; r3; seed; n0] s /\
                  read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                  n1 /\
                  read (memory :> bytes64 (word_add stackpointer (word 16))) s =
                  n2 /\
                  read (memory :> bytes64 (word_add stackpointer (word 24))) s =
                  n3 /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,64)) s = sd)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r0 (word(4 * i))))
                             s = mld_poly_uniform_eta 2 sd (word_zx n0) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                             s = mld_poly_uniform_eta 2 sd (word_zx n1) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                             s = mld_poly_uniform_eta 2 sd (word_zx n2) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                             s = mld_poly_uniform_eta 2 sd (word_zx n3) i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                memory :> bytes(word_sub stackpointer (word 2295),2295)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the stack and the lists of the    *)
(* values that mld_rej_eta_c declassifies for each polynomial, with all      *)
(* accesses within the arguments, the stack, the return address and the      *)
(* stack arguments, the GOT entries of memset and memcpy, the region (ea,el) *)
(* of their code and data and the round constants of Keccak, and the writes  *)
(* within the polynomials and the stack.                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n3:byte))) /\
        PAIRWISE nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2295),2295)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024)]
         [(stackpointer,32)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2295),2295)]
         [(seed,64); (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_poly_uniform_eta_4x) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r0; r1; r2; r3; seed; n0] s /\
                  read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                  n1 /\
                  read (memory :> bytes64 (word_add stackpointer (word 16))) s =
                  n2 /\
                  read (memory :> bytes64 (word_add stackpointer (word 24))) s =
                  n3 /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,64)) s = sd /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r0 (word(4 * i))))
                             s = mld_poly_uniform_eta 2 sd (word_zx n0) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                             s = mld_poly_uniform_eta 2 sd (word_zx n1) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                             s = mld_poly_uniform_eta 2 sd (word_zx n2) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                             s = mld_poly_uniform_eta 2 sd (word_zx n3) i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r0 r1 r2 r3 seed
                            (mld_poly_uniform_eta_declass 2
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n0:byte))))
                            (mld_poly_uniform_eta_declass 2
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n1:byte))))
                            (mld_poly_uniform_eta_declass 2
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n2:byte))))
                            (mld_poly_uniform_eta_declass 2
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n3:byte))))
                            mf mc pc (word_sub stackpointer (word 2295))
                            returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 2295),2295; stackpointer,32;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 2295),2295]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                memory :> bytes(word_sub stackpointer (word 2295),2295)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* seed only through the declassified validity of the nibbles of the         *)
(* streams, as above.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
        mld_rej_eta_terminates 2
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n3:byte))) /\
        PAIRWISE nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2295),2295)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024)]
         [(stackpointer,32)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2295),2295)]
         [(seed,64); (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_poly_uniform_eta_4x) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r0; r1; r2; r3; seed; n0] s /\
                  read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                  n1 /\
                  read (memory :> bytes64 (word_add stackpointer (word 16))) s =
                  n2 /\
                  read (memory :> bytes64 (word_add stackpointer (word 24))) s =
                  n3 /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,64)) s = sd /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r0 r1 r2 r3 seed
                            (mld_poly_uniform_eta_declass 2
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n0:byte))))
                            (mld_poly_uniform_eta_declass 2
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n1:byte))))
                            (mld_poly_uniform_eta_declass 2
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n2:byte))))
                            (mld_poly_uniform_eta_declass 2
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n3:byte))))
                            mf mc pc (word_sub stackpointer (word 2295))
                            returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 2295),2295; stackpointer,32;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 2295),2295]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                memory :> bytes(word_sub stackpointer (word 2295),2295)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
