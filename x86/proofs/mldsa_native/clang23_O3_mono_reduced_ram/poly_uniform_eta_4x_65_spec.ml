(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of four polynomials with coefficients in [-4,4] for ML-DSA-65 by *)
(* rejection: the statement. This is the code for                            *)
(* mldsa65_poly_uniform_eta_4x (mld_poly_uniform_eta_4x in poly_kl.c) from   *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3 as *)
(* one translation unit and MLD_CONFIG_REDUCE_RAM (see                       *)
(* mldsa_native/README.md). clang inlines the fourfold SHAKE256 and          *)
(* mld_rej_eta_c: the code extends the seed of 64 bytes with each of the     *)
(* four nonce bytes and a zero byte, zeroes four Keccak states with memset,  *)
(* XORs the extended seeds and the padding into them, permutes them with     *)
(* mldsa_keccakf1600_permute, copies the first two blocks of 136 bytes of    *)
(* each to a buffer with memcpy and samples the coefficients from it, and    *)
(* then squeezes one more block of each and samples from those polynomials   *)
(* that need more until each has 256 coefficients, before zeroing the        *)
(* states, the buffers and the extended seeds with memset. It calls memset   *)
(* and memcpy through the PLT, under the contracts of                        *)
(* utils/mldsa_native_libc.ml, which require the direction flag to be clear, *)
(* as the ABI requires on entry. It is verified in the whole image (see      *)
(* libmldsa.ml) against mld_poly_uniform_eta of                              *)
(* common/mldsa_native_sampling.ml, using the theorems for the callees, and  *)
(* assuming that the SHAKE256 output of each extended seed has 256           *)
(* acceptable nibbles (mld_rej_eta_terminates), without which the code does  *)
(* not terminate. The nonces are the low bytes of the sixth argument and of  *)
(* the three arguments that the caller puts on the stack, as the System V    *)
(* ABI passes them. It is also shown to be constant time and memory safe,    *)
(* with the events depending on the seed only through which nibbles of the   *)
(* SHAKE256 outputs mld_rej_eta_c accepts, which it declassifies             *)
(* (mld_poly_uniform_eta_declass).                                           *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa65_poly_uniform_eta_4x:
       +0x0: push    %rbp
       +0x1: mov     %rsp,%rbp
       +0x4: push    %r15
       +0x6: push    %r14
       +0x8: push    %r13
       +0xa: push    %r12
       +0xc: push    %rbx
       +0xd: and     $0xffffffffffffffe0,%rsp
      +0x11: sub     $0x980,%rsp
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
     +0x135: lea     0x1c0(%rsp),%r12
     +0x13d: xor     %ebx,%ebx
     +0x13f: mov     $0x320,%edx
     +0x144: mov     %r12,%rdi
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
     +0x362: xorb    $0x80,0x30f(%rsp)
     +0x36a: lea     0x288(%rsp),%r13
     +0x372: xorb    $0x80,0x3d7(%rsp)
     +0x37a: lea     0x350(%rsp),%r14
     +0x382: xorb    $0x80,0x49f(%rsp)
     +0x38a: lea     0x418(%rsp),%r15
     +0x392: mov     %r12,%rdi
     +0x395: call    <mldsa_keccakf1600_permute>
     +0x39a: mov     %r13,%rdi
     +0x39d: call    <mldsa_keccakf1600_permute>
     +0x3a2: mov     %r14,%rdi
     +0x3a5: call    <mldsa_keccakf1600_permute>
     +0x3aa: mov     %r15,%rdi
     +0x3ad: call    <mldsa_keccakf1600_permute>
     +0x3b2: lea     0x4e0(%rsp),%rdi
     +0x3ba: mov     $0x88,%edx
     +0x3bf: mov     %r12,%rsi
     +0x3c2: call    <memcpy>
     +0x3c7: mov     $0x88,%edx
     +0x3cc: lea     0x600(%rsp),%rdi
     +0x3d4: mov     %r13,%rsi
     +0x3d7: call    <memcpy>
     +0x3dc: mov     $0x88,%edx
     +0x3e1: lea     0x720(%rsp),%rdi
     +0x3e9: mov     %r14,%rsi
     +0x3ec: call    <memcpy>
     +0x3f1: mov     $0x88,%edx
     +0x3f6: lea     0x840(%rsp),%rdi
     +0x3fe: mov     %r15,%rsi
     +0x401: call    <memcpy>
     +0x406: mov     %r12,%rdi
     +0x409: call    <mldsa_keccakf1600_permute>
     +0x40e: mov     %r13,%rdi
     +0x411: call    <mldsa_keccakf1600_permute>
     +0x416: mov     %r14,%rdi
     +0x419: call    <mldsa_keccakf1600_permute>
     +0x41e: mov     %r15,%rdi
     +0x421: call    <mldsa_keccakf1600_permute>
     +0x426: mov     $0x88,%edx
     +0x42b: lea     0x568(%rsp),%rdi
     +0x433: mov     %r12,%rsi
     +0x436: call    <memcpy>
     +0x43b: mov     $0x88,%edx
     +0x440: lea     0x688(%rsp),%rdi
     +0x448: mov     %r13,%rsi
     +0x44b: call    <memcpy>
     +0x450: mov     $0x88,%edx
     +0x455: lea     0x7a8(%rsp),%rdi
     +0x45d: mov     %r14,%rsi
     +0x460: call    <memcpy>
     +0x465: mov     $0x88,%edx
     +0x46a: lea     0x8c8(%rsp),%rdi
     +0x472: mov     %r15,%rsi
     +0x475: call    <memcpy>
     +0x47a: xor     %r13d,%r13d
     +0x47d: nopl    (%rax)
     +0x480: movzbl  0x4e0(%rsp,%rbx,1),%eax
     +0x488: mov     %eax,%ecx
     +0x48a: and     $0xf,%ecx
     +0x48d: cmp     $0x8,%ecx
     +0x490: ja      <mldsa65_poly_uniform_eta_4x+0x4b0>
     +0x492: mov     $0x4,%edx
     +0x497: sub     %ecx,%edx
     +0x499: mov     %r13d,%ecx
     +0x49c: inc     %r13d
     +0x49f: mov     0x38(%rsp),%rsi
     +0x4a4: mov     %edx,(%rsi,%rcx,4)
     +0x4a7: cmp     $0x8f,%al
     +0x4a9: jbe     <mldsa65_poly_uniform_eta_4x+0x4b9>
     +0x4ab: jmp     <mldsa65_poly_uniform_eta_4x+0x4d5>
     +0x4ad: nopl    (%rax)
     +0x4b0: mov     0x38(%rsp),%rsi
     +0x4b5: cmp     $0x8f,%al
     +0x4b7: ja      <mldsa65_poly_uniform_eta_4x+0x4d5>
     +0x4b9: cmp     $0xff,%r13d
     +0x4c0: ja      <mldsa65_poly_uniform_eta_4x+0x4d5>
     +0x4c2: shr     $0x4,%eax
     +0x4c5: mov     $0x4,%ecx
     +0x4ca: sub     %eax,%ecx
     +0x4cc: mov     %r13d,%eax
     +0x4cf: inc     %r13d
     +0x4d2: mov     %ecx,(%rsi,%rax,4)
     +0x4d5: cmp     $0x100,%r13d
     +0x4dc: setb    %r11b
     +0x4e0: jae     <mldsa65_poly_uniform_eta_4x+0x4ef>
     +0x4e2: cmp     $0x10f,%rbx
     +0x4e9: lea     0x1(%rbx),%rbx
     +0x4ed: jb      <mldsa65_poly_uniform_eta_4x+0x480>
     +0x4ef: xor     %eax,%eax
     +0x4f1: xor     %ebx,%ebx
     +0x4f3: mov     0x30(%rsp),%rdi
     +0x4f8: mov     0x28(%rsp),%r8
     +0x4fd: mov     0x20(%rsp),%r9
     +0x502: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x510: movzbl  0x600(%rsp,%rax,1),%ecx
     +0x518: mov     %ecx,%edx
     +0x51a: and     $0xf,%edx
     +0x51d: cmp     $0x8,%edx
     +0x520: ja      <mldsa65_poly_uniform_eta_4x+0x531>
     +0x522: mov     $0x4,%esi
     +0x527: sub     %edx,%esi
     +0x529: mov     %ebx,%edx
     +0x52b: inc     %ebx
     +0x52d: mov     %esi,(%r9,%rdx,4)
     +0x531: cmp     $0x8f,%cl
     +0x534: ja      <mldsa65_poly_uniform_eta_4x+0x550>
     +0x536: cmp     $0xff,%ebx
     +0x53c: ja      <mldsa65_poly_uniform_eta_4x+0x550>
     +0x53e: shr     $0x4,%ecx
     +0x541: mov     $0x4,%edx
     +0x546: sub     %ecx,%edx
     +0x548: mov     %ebx,%ecx
     +0x54a: inc     %ebx
     +0x54c: mov     %edx,(%r9,%rcx,4)
     +0x550: cmp     $0x100,%ebx
     +0x556: setb    %r10b
     +0x55a: jae     <mldsa65_poly_uniform_eta_4x+0x568>
     +0x55c: cmp     $0x10f,%rax
     +0x562: lea     0x1(%rax),%rax
     +0x566: jb      <mldsa65_poly_uniform_eta_4x+0x510>
     +0x568: xor     %eax,%eax
     +0x56a: xor     %r14d,%r14d
     +0x56d: nopl    (%rax)
     +0x570: movzbl  0x720(%rsp,%rax,1),%ecx
     +0x578: mov     %ecx,%edx
     +0x57a: and     $0xf,%edx
     +0x57d: cmp     $0x8,%edx
     +0x580: ja      <mldsa65_poly_uniform_eta_4x+0x593>
     +0x582: mov     $0x4,%esi
     +0x587: sub     %edx,%esi
     +0x589: mov     %r14d,%edx
     +0x58c: inc     %r14d
     +0x58f: mov     %esi,(%r8,%rdx,4)
     +0x593: cmp     $0x8f,%cl
     +0x596: ja      <mldsa65_poly_uniform_eta_4x+0x5b5>
     +0x598: cmp     $0xff,%r14d
     +0x59f: ja      <mldsa65_poly_uniform_eta_4x+0x5b5>
     +0x5a1: shr     $0x4,%ecx
     +0x5a4: mov     $0x4,%edx
     +0x5a9: sub     %ecx,%edx
     +0x5ab: mov     %r14d,%ecx
     +0x5ae: inc     %r14d
     +0x5b1: mov     %edx,(%r8,%rcx,4)
     +0x5b5: cmp     $0x100,%r14d
     +0x5bc: setb    %r9b
     +0x5c0: jae     <mldsa65_poly_uniform_eta_4x+0x5ce>
     +0x5c2: cmp     $0x10f,%rax
     +0x5c8: lea     0x1(%rax),%rax
     +0x5cc: jb      <mldsa65_poly_uniform_eta_4x+0x570>
     +0x5ce: xor     %eax,%eax
     +0x5d0: xor     %r15d,%r15d
     +0x5d3: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x5e0: movzbl  0x840(%rsp,%rax,1),%ecx
     +0x5e8: mov     %ecx,%edx
     +0x5ea: and     $0xf,%edx
     +0x5ed: cmp     $0x8,%edx
     +0x5f0: ja      <mldsa65_poly_uniform_eta_4x+0x602>
     +0x5f2: mov     $0x4,%esi
     +0x5f7: sub     %edx,%esi
     +0x5f9: mov     %r15d,%edx
     +0x5fc: inc     %r15d
     +0x5ff: mov     %esi,(%rdi,%rdx,4)
     +0x602: cmp     $0x8f,%cl
     +0x605: ja      <mldsa65_poly_uniform_eta_4x+0x623>
     +0x607: cmp     $0xff,%r15d
     +0x60e: ja      <mldsa65_poly_uniform_eta_4x+0x623>
     +0x610: shr     $0x4,%ecx
     +0x613: mov     $0x4,%edx
     +0x618: sub     %ecx,%edx
     +0x61a: mov     %r15d,%ecx
     +0x61d: inc     %r15d
     +0x620: mov     %edx,(%rdi,%rcx,4)
     +0x623: cmp     $0x100,%r15d
     +0x62a: setb    %cl
     +0x62d: jae     <mldsa65_poly_uniform_eta_4x+0x63b>
     +0x62f: cmp     $0x10f,%rax
     +0x635: lea     0x1(%rax),%rax
     +0x639: jb      <mldsa65_poly_uniform_eta_4x+0x5e0>
     +0x63b: cmp     $0x100,%r13d
     +0x642: jb      <mldsa65_poly_uniform_eta_4x+0x670>
     +0x644: cmp     $0x100,%ebx
     +0x64a: jb      <mldsa65_poly_uniform_eta_4x+0x670>
     +0x64c: cmp     $0x100,%r14d
     +0x653: jb      <mldsa65_poly_uniform_eta_4x+0x670>
     +0x655: cmp     $0xff,%r15d
     +0x65c: ja      <mldsa65_poly_uniform_eta_4x+0x93e>
     +0x662: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x670: mov     %r11b,0x1c(%rsp)
     +0x675: mov     %r10b,0x1d(%rsp)
     +0x67a: mov     %r9b,0x1e(%rsp)
     +0x67f: mov     %cl,0x1f(%rsp)
     +0x683: lea     0x1c0(%rsp),%rdi
     +0x68b: call    <mldsa_keccakf1600_permute>
     +0x690: lea     0x288(%rsp),%r12
     +0x698: mov     %r12,%rdi
     +0x69b: call    <mldsa_keccakf1600_permute>
     +0x6a0: lea     0x350(%rsp),%rdi
     +0x6a8: call    <mldsa_keccakf1600_permute>
     +0x6ad: lea     0x418(%rsp),%rdi
     +0x6b5: call    <mldsa_keccakf1600_permute>
     +0x6ba: mov     $0x88,%edx
     +0x6bf: lea     0x4e0(%rsp),%rdi
     +0x6c7: lea     0x1c0(%rsp),%rsi
     +0x6cf: call    <memcpy>
     +0x6d4: mov     $0x88,%edx
     +0x6d9: lea     0x600(%rsp),%rdi
     +0x6e1: mov     %r12,%rsi
     +0x6e4: call    <memcpy>
     +0x6e9: mov     $0x88,%edx
     +0x6ee: lea     0x720(%rsp),%rdi
     +0x6f6: lea     0x350(%rsp),%rsi
     +0x6fe: call    <memcpy>
     +0x703: mov     $0x88,%edx
     +0x708: lea     0x840(%rsp),%rdi
     +0x710: lea     0x418(%rsp),%rsi
     +0x718: call    <memcpy>
     +0x71d: testb   $0x1,0x1c(%rsp)
     +0x722: je      <mldsa65_poly_uniform_eta_4x+0x7a0>
     +0x724: xor     %eax,%eax
     +0x726: mov     0x30(%rsp),%rdi
     +0x72b: mov     0x28(%rsp),%r8
     +0x730: mov     0x20(%rsp),%r9
     +0x735: mov     0x38(%rsp),%r10
     +0x73a: nopw    0x0(%rax,%rax,1)
     +0x740: movzbl  0x4e0(%rsp,%rax,1),%ecx
     +0x748: mov     %ecx,%edx
     +0x74a: and     $0xf,%edx
     +0x74d: cmp     $0x8,%edx
     +0x750: ja      <mldsa65_poly_uniform_eta_4x+0x763>
     +0x752: mov     $0x4,%esi
     +0x757: sub     %edx,%esi
     +0x759: mov     %r13d,%edx
     +0x75c: inc     %r13d
     +0x75f: mov     %esi,(%r10,%rdx,4)
     +0x763: cmp     $0x8f,%cl
     +0x766: ja      <mldsa65_poly_uniform_eta_4x+0x785>
     +0x768: cmp     $0xff,%r13d
     +0x76f: ja      <mldsa65_poly_uniform_eta_4x+0x785>
     +0x771: shr     $0x4,%ecx
     +0x774: mov     $0x4,%edx
     +0x779: sub     %ecx,%edx
     +0x77b: mov     %r13d,%ecx
     +0x77e: inc     %r13d
     +0x781: mov     %edx,(%r10,%rcx,4)
     +0x785: cmp     $0xff,%r13d
     +0x78c: ja      <mldsa65_poly_uniform_eta_4x+0x7af>
     +0x78e: cmp     $0x87,%rax
     +0x794: lea     0x1(%rax),%rax
     +0x798: jb      <mldsa65_poly_uniform_eta_4x+0x740>
     +0x79a: jmp     <mldsa65_poly_uniform_eta_4x+0x7af>
     +0x79c: nopl    0x0(%rax)
     +0x7a0: mov     0x30(%rsp),%rdi
     +0x7a5: mov     0x28(%rsp),%r8
     +0x7aa: mov     0x20(%rsp),%r9
     +0x7af: testb   $0x1,0x1d(%rsp)
     +0x7b4: je      <mldsa65_poly_uniform_eta_4x+0x814>
     +0x7b6: xor     %eax,%eax
     +0x7b8: nopl    0x0(%rax,%rax,1)
     +0x7c0: movzbl  0x600(%rsp,%rax,1),%ecx
     +0x7c8: mov     %ecx,%edx
     +0x7ca: and     $0xf,%edx
     +0x7cd: cmp     $0x8,%edx
     +0x7d0: ja      <mldsa65_poly_uniform_eta_4x+0x7e1>
     +0x7d2: mov     $0x4,%esi
     +0x7d7: sub     %edx,%esi
     +0x7d9: mov     %ebx,%edx
     +0x7db: inc     %ebx
     +0x7dd: mov     %esi,(%r9,%rdx,4)
     +0x7e1: cmp     $0x8f,%cl
     +0x7e4: ja      <mldsa65_poly_uniform_eta_4x+0x800>
     +0x7e6: cmp     $0xff,%ebx
     +0x7ec: ja      <mldsa65_poly_uniform_eta_4x+0x800>
     +0x7ee: shr     $0x4,%ecx
     +0x7f1: mov     $0x4,%edx
     +0x7f6: sub     %ecx,%edx
     +0x7f8: mov     %ebx,%ecx
     +0x7fa: inc     %ebx
     +0x7fc: mov     %edx,(%r9,%rcx,4)
     +0x800: cmp     $0xff,%ebx
     +0x806: ja      <mldsa65_poly_uniform_eta_4x+0x814>
     +0x808: cmp     $0x87,%rax
     +0x80e: lea     0x1(%rax),%rax
     +0x812: jb      <mldsa65_poly_uniform_eta_4x+0x7c0>
     +0x814: testb   $0x1,0x1e(%rsp)
     +0x819: je      <mldsa65_poly_uniform_eta_4x+0x87a>
     +0x81b: xor     %eax,%eax
     +0x81d: nopl    (%rax)
     +0x820: movzbl  0x720(%rsp,%rax,1),%ecx
     +0x828: mov     %ecx,%edx
     +0x82a: and     $0xf,%edx
     +0x82d: cmp     $0x8,%edx
     +0x830: ja      <mldsa65_poly_uniform_eta_4x+0x843>
     +0x832: mov     $0x4,%esi
     +0x837: sub     %edx,%esi
     +0x839: mov     %r14d,%edx
     +0x83c: inc     %r14d
     +0x83f: mov     %esi,(%r8,%rdx,4)
     +0x843: cmp     $0x8f,%cl
     +0x846: ja      <mldsa65_poly_uniform_eta_4x+0x865>
     +0x848: cmp     $0xff,%r14d
     +0x84f: ja      <mldsa65_poly_uniform_eta_4x+0x865>
     +0x851: shr     $0x4,%ecx
     +0x854: mov     $0x4,%edx
     +0x859: sub     %ecx,%edx
     +0x85b: mov     %r14d,%ecx
     +0x85e: inc     %r14d
     +0x861: mov     %edx,(%r8,%rcx,4)
     +0x865: cmp     $0xff,%r14d
     +0x86c: ja      <mldsa65_poly_uniform_eta_4x+0x87a>
     +0x86e: cmp     $0x87,%rax
     +0x874: lea     0x1(%rax),%rax
     +0x878: jb      <mldsa65_poly_uniform_eta_4x+0x820>
     +0x87a: testb   $0x1,0x1f(%rsp)
     +0x87f: je      <mldsa65_poly_uniform_eta_4x+0x8e8>
     +0x881: xor     %eax,%eax
     +0x883: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x890: movzbl  0x840(%rsp,%rax,1),%ecx
     +0x898: mov     %ecx,%edx
     +0x89a: and     $0xf,%edx
     +0x89d: cmp     $0x8,%edx
     +0x8a0: ja      <mldsa65_poly_uniform_eta_4x+0x8b2>
     +0x8a2: mov     $0x4,%esi
     +0x8a7: sub     %edx,%esi
     +0x8a9: mov     %r15d,%edx
     +0x8ac: inc     %r15d
     +0x8af: mov     %esi,(%rdi,%rdx,4)
     +0x8b2: cmp     $0x8f,%cl
     +0x8b5: ja      <mldsa65_poly_uniform_eta_4x+0x8d3>
     +0x8b7: cmp     $0xff,%r15d
     +0x8be: ja      <mldsa65_poly_uniform_eta_4x+0x8d3>
     +0x8c0: shr     $0x4,%ecx
     +0x8c3: mov     $0x4,%edx
     +0x8c8: sub     %ecx,%edx
     +0x8ca: mov     %r15d,%ecx
     +0x8cd: inc     %r15d
     +0x8d0: mov     %edx,(%rdi,%rcx,4)
     +0x8d3: cmp     $0xff,%r15d
     +0x8da: ja      <mldsa65_poly_uniform_eta_4x+0x8e8>
     +0x8dc: cmp     $0x87,%rax
     +0x8e2: lea     0x1(%rax),%rax
     +0x8e6: jb      <mldsa65_poly_uniform_eta_4x+0x890>
     +0x8e8: cmp     $0x100,%ebx
     +0x8ee: setb    %r10b
     +0x8f2: cmp     $0x100,%r14d
     +0x8f9: setb    %r9b
     +0x8fd: cmp     $0x100,%r15d
     +0x904: setb    %cl
     +0x907: cmp     $0x100,%r13d
     +0x90e: setb    %r11b
     +0x912: jb      <mldsa65_poly_uniform_eta_4x+0x670>
     +0x918: cmp     $0x100,%ebx
     +0x91e: jb      <mldsa65_poly_uniform_eta_4x+0x670>
     +0x924: cmp     $0x100,%r14d
     +0x92b: jb      <mldsa65_poly_uniform_eta_4x+0x670>
     +0x931: cmp     $0x100,%r15d
     +0x938: jb      <mldsa65_poly_uniform_eta_4x+0x670>
     +0x93e: lea     0x1c0(%rsp),%rbx
     +0x946: mov     $0x320,%edx
     +0x94b: mov     %rbx,%rdi
     +0x94e: xor     %esi,%esi
     +0x950: call    <memset>
     +0x955: lea     0x4e0(%rsp),%rbx
     +0x95d: mov     $0x480,%edx
     +0x962: mov     %rbx,%rdi
     +0x965: xor     %esi,%esi
     +0x967: call    <memset>
     +0x96c: lea     0x40(%rsp),%rbx
     +0x971: mov     $0x180,%edx
     +0x976: mov     %rbx,%rdi
     +0x979: xor     %esi,%esi
     +0x97b: call    <memset>
     +0x980: lea     -0x28(%rbp),%rsp
     +0x984: pop     %rbx
     +0x985: pop     %r12
     +0x987: pop     %r13
     +0x989: pop     %r14
     +0x98b: pop     %r15
     +0x98d: pop     %rbp
     +0x98e: xor     %eax,%eax
     +0x990: xor     %ecx,%ecx
     +0x992: xor     %edi,%edi
     +0x994: xor     %edx,%edx
     +0x996: xor     %esi,%esi
     +0x998: xor     %r8d,%r8d
     +0x99b: xor     %r9d,%r9d
     +0x99e: xor     %r10d,%r10d
     +0x9a1: xor     %r11d,%r11d
     +0x9a4: ret     
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa65_poly_uniform_eta_4x";
    layout_range "plt_memcpy";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The seed is the 64 bytes sd at seed, and polynomial j        *)
(* becomes mld_poly_uniform_eta 4 sd of the nonce j, the low byte of nj, if  *)
(* the SHAKE256 output of the extended seed has 256 acceptable nibbles. The  *)
(* nonces n1, n2 and n3 are in the 8 bytes each above the return address.    *)
(* The function saves RBP, the frame pointer, and five more registers below  *)
(* the return address, lowers RSP by up to 31 bytes to align it to 32 bytes, *)
(* and then reserves 2432 bytes for the arguments, the extended seeds, the   *)
(* states, the buffers and the flags, below which the calls of               *)
(* mldsa_keccakf1600_permute use 296 bytes, with their return address: 2807  *)
(* bytes of stack below the return address in all.                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !r0 r1 r2 r3 seed sd n0 n1 n2 n3 pc stackpointer
   returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n3:byte))) /\
        PAIRWISE nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2807),2807)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024)]
         [(stackpointer,32)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2807),2807)]
         [(seed,64); (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_poly_uniform_eta_4x) /\
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
                             s = mld_poly_uniform_eta 4 sd (word_zx n0) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                             s = mld_poly_uniform_eta 4 sd (word_zx n1) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                             s = mld_poly_uniform_eta 4 sd (word_zx n2) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                             s = mld_poly_uniform_eta 4 sd (word_zx n3) i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                memory :> bytes(word_sub stackpointer (word 2807),2807)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the stack and the lists of the    *)
(* values that mld_rej_eta_c declassifies for each polynomial, with all      *)
(* accesses within the arguments, the stack, the return address and the      *)
(* stack arguments, the GOT entries of memset and memcpy, the region (ea,el) *)
(* of their code and data and the round constants of Keccak, and the writes  *)
(* within the polynomials and the stack.                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n3:byte))) /\
        PAIRWISE nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2807),2807)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024)]
         [(stackpointer,32)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2807),2807)]
         [(seed,64); (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_poly_uniform_eta_4x) /\
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
                             s = mld_poly_uniform_eta 4 sd (word_zx n0) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                             s = mld_poly_uniform_eta 4 sd (word_zx n1) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                             s = mld_poly_uniform_eta 4 sd (word_zx n2) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                             s = mld_poly_uniform_eta 4 sd (word_zx n3) i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r0 r1 r2 r3 seed
                            (mld_poly_uniform_eta_declass 4
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n0:byte))))
                            (mld_poly_uniform_eta_declass 4
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n1:byte))))
                            (mld_poly_uniform_eta_declass 4
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n2:byte))))
                            (mld_poly_uniform_eta_declass 4
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n3:byte))))
                            mf mc pc (word_sub stackpointer (word 2807))
                            returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 2807),2807; stackpointer,32;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 2807),2807]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                memory :> bytes(word_sub stackpointer (word 2807),2807)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* seed only through the declassified validity of the nibbles of the         *)
(* streams, as above.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
        mld_rej_eta_terminates 4
          (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n3:byte))) /\
        PAIRWISE nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2807),2807)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024)]
         [(stackpointer,32)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 2807),2807)]
         [(seed,64); (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_poly_uniform_eta_4x) /\
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
                            (mld_poly_uniform_eta_declass 4
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n0:byte))))
                            (mld_poly_uniform_eta_declass 4
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n1:byte))))
                            (mld_poly_uniform_eta_declass 4
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n2:byte))))
                            (mld_poly_uniform_eta_declass 4
                              (mld_shake256_stream 66
                                (sd + 2 EXP 512 * val(word_zx n3:byte))))
                            mf mc pc (word_sub stackpointer (word 2807))
                            returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 2807),2807; stackpointer,32;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 2807),2807]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                memory :> bytes(word_sub stackpointer (word 2807),2807)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
