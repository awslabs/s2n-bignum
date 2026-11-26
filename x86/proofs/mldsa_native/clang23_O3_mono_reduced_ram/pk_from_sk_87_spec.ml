(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the statement. This is the code for       *)
(* mldsa87_pk_from_sk (mld_sign_pk_from_sk in sign.c) from mldsa-native's    *)
(* portable C implementation compiled by clang 23 with -O3 and               *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which copies rho, the *)
(* key and tr from the secret key, unpacks s1 and s2 with                    *)
(* mldsa87_polyeta_unpack and checks their norms (s1 with                    *)
(* mldsa87_polyvecl_chknorm, each polynomial of s2 in an inlined loop, in    *)
(* constant time), transforms s1 with calls of mldsa_poly_ntt, recomputes t1 *)
(* into the public key and t0 into a buffer with mld_compute_pack_t0_t187,   *)
(* compares t0 with that in the secret key, hashes the public key with an    *)
(* inlined SHAKE256 and compares the hash with tr, all in constant time, and *)
(* then zeroes the public key if a check failed, and its buffers, with       *)
(* memset, which it calls through the PLT, so that the direction flag must   *)
(* be clear, as the ABI requires on entry. It is verified in the whole image *)
(* (see libmldsa.ml) against mld_pk_from_sk_pk and mld_pk_from_sk_valid of   *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and the   *)
(* contracts memset_full_contract and memcpy_full_contract of                *)
(* utils/mldsa_native_libc.ml for the C library functions that it and its    *)
(* callees call, assuming that the expansion of the matrix from rho          *)
(* terminates (mld_matrix_terminates), and shown to be constant time and     *)
(* memory safe, with the events depending on rho, which is part of the       *)
(* public key, and on the result of the checks, which the C code             *)
(* declassifies.                                                             *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/compute_pack_t0_t1_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa87_pk_from_sk:
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
      +0x20: sub     $0x1000,%rsp
      +0x27: movq    $0x0,(%rsp)
      +0x2f: sub     $0xf20,%rsp
      +0x36: mov     %rsi,%r15
      +0x39: mov     %rdi,%rbx
      +0x3c: movups  (%rsi),%xmm0
      +0x3f: movups  0x10(%rsi),%xmm1
      +0x43: movaps  %xmm1,0xf0(%rsp)
      +0x4b: movaps  %xmm0,0xe0(%rsp)
      +0x53: movups  0x20(%rsi),%xmm0
      +0x57: movups  0x30(%rsi),%xmm1
      +0x5b: movaps  %xmm0,0x1c0(%rsp)
      +0x63: movaps  %xmm1,0x1d0(%rsp)
      +0x6b: movups  0x40(%rsi),%xmm0
      +0x6f: movups  0x50(%rsi),%xmm1
      +0x73: movdqu  0x60(%rsi),%xmm2
      +0x78: movdqu  0x70(%rsi),%xmm3
      +0x7d: movaps  %xmm0,0x180(%rsp)
      +0x85: movaps  %xmm1,0x190(%rsp)
      +0x8d: movdqa  %xmm2,0x1a0(%rsp)
      +0x96: movdqa  %xmm3,0x1b0(%rsp)
      +0x9f: add     $0x80,%rsi
      +0xa6: lea     0x5e0(%rsp),%r14
      +0xae: mov     %r14,%rdi
      +0xb1: call    <mldsa87_polyeta_unpack>
      +0xb6: lea     0x9e0(%rsp),%rdi
      +0xbe: lea     0xe0(%r15),%rsi
      +0xc5: call    <mldsa87_polyeta_unpack>
      +0xca: lea     0xde0(%rsp),%rdi
      +0xd2: lea     0x140(%r15),%rsi
      +0xd9: call    <mldsa87_polyeta_unpack>
      +0xde: lea     0x11e0(%rsp),%rdi
      +0xe6: lea     0x1a0(%r15),%rsi
      +0xed: call    <mldsa87_polyeta_unpack>
      +0xf2: lea     0x15e0(%rsp),%rdi
      +0xfa: lea     0x200(%r15),%rsi
     +0x101: call    <mldsa87_polyeta_unpack>
     +0x106: lea     0x19e0(%rsp),%rdi
     +0x10e: lea     0x260(%r15),%rsi
     +0x115: call    <mldsa87_polyeta_unpack>
     +0x11a: lea     0x1de0(%rsp),%rdi
     +0x122: lea     0x2c0(%r15),%rsi
     +0x129: call    <mldsa87_polyeta_unpack>
     +0x12e: mov     %r14,%rdi
     +0x131: mov     $0x3,%esi
     +0x136: call    <mldsa87_polyvecl_chknorm>
     +0x13b: mov     %eax,0xd4(%rsp)
     +0x142: lea     0x320(%r15),%rsi
     +0x149: lea     0x1e0(%rsp),%rdi
     +0x151: call    <mldsa87_polyeta_unpack>
     +0x156: xor     %edi,%edi
     +0x158: xor     %eax,%eax
     +0x15a: nopw    0x0(%rax,%rax,1)
     +0x160: movslq  0x1e0(%rsp,%rax,4),%rcx
     +0x168: mov     %ecx,%edx
     +0x16a: neg     %edx
     +0x16c: mov     %rcx,%rsi
     +0x16f: shr     $0x1f,%rsi
     +0x173: xor     %ecx,%edx
     +0x175: and     %esi,%edx
     +0x177: xor     %ecx,%edx
     +0x179: mov     $0x2,%ecx
     +0x17e: sub     %edx,%ecx
     +0x180: movslq  %ecx,%rcx
     +0x183: shr     $0x1f,%rcx
     +0x187: or      %ecx,%edi
     +0x189: inc     %rax
     +0x18c: cmp     $0x100,%rax
     +0x192: jne     <mldsa87_pk_from_sk+0x160>
     +0x194: mov     %rdi,0x138(%rsp)
     +0x19c: lea     0x380(%r15),%rsi
     +0x1a3: lea     0x1e0(%rsp),%rdi
     +0x1ab: call    <mldsa87_polyeta_unpack>
     +0x1b0: xor     %edi,%edi
     +0x1b2: xor     %eax,%eax
     +0x1b4: data16  data16 cs nopw 0x0(%rax,%rax,1)
     +0x1c0: movslq  0x1e0(%rsp,%rax,4),%rcx
     +0x1c8: mov     %ecx,%edx
     +0x1ca: neg     %edx
     +0x1cc: mov     %rcx,%rsi
     +0x1cf: shr     $0x1f,%rsi
     +0x1d3: xor     %ecx,%edx
     +0x1d5: and     %esi,%edx
     +0x1d7: xor     %ecx,%edx
     +0x1d9: mov     $0x2,%ecx
     +0x1de: sub     %edx,%ecx
     +0x1e0: movslq  %ecx,%rcx
     +0x1e3: shr     $0x1f,%rcx
     +0x1e7: or      %ecx,%edi
     +0x1e9: inc     %rax
     +0x1ec: cmp     $0x100,%rax
     +0x1f2: jne     <mldsa87_pk_from_sk+0x1c0>
     +0x1f4: mov     %rdi,0x130(%rsp)
     +0x1fc: lea     0x3e0(%r15),%rsi
     +0x203: lea     0x1e0(%rsp),%rdi
     +0x20b: call    <mldsa87_polyeta_unpack>
     +0x210: xor     %edi,%edi
     +0x212: xor     %eax,%eax
     +0x214: data16  data16 cs nopw 0x0(%rax,%rax,1)
     +0x220: movslq  0x1e0(%rsp,%rax,4),%rcx
     +0x228: mov     %ecx,%edx
     +0x22a: neg     %edx
     +0x22c: mov     %rcx,%rsi
     +0x22f: shr     $0x1f,%rsi
     +0x233: xor     %ecx,%edx
     +0x235: and     %esi,%edx
     +0x237: xor     %ecx,%edx
     +0x239: mov     $0x2,%ecx
     +0x23e: sub     %edx,%ecx
     +0x240: movslq  %ecx,%rcx
     +0x243: shr     $0x1f,%rcx
     +0x247: or      %ecx,%edi
     +0x249: inc     %rax
     +0x24c: cmp     $0x100,%rax
     +0x252: jne     <mldsa87_pk_from_sk+0x220>
     +0x254: mov     %rdi,0x128(%rsp)
     +0x25c: lea     0x440(%r15),%rsi
     +0x263: lea     0x1e0(%rsp),%rdi
     +0x26b: call    <mldsa87_polyeta_unpack>
     +0x270: xor     %edi,%edi
     +0x272: xor     %eax,%eax
     +0x274: data16  data16 cs nopw 0x0(%rax,%rax,1)
     +0x280: movslq  0x1e0(%rsp,%rax,4),%rcx
     +0x288: mov     %ecx,%edx
     +0x28a: neg     %edx
     +0x28c: mov     %rcx,%rsi
     +0x28f: shr     $0x1f,%rsi
     +0x293: xor     %ecx,%edx
     +0x295: and     %esi,%edx
     +0x297: xor     %ecx,%edx
     +0x299: mov     $0x2,%ecx
     +0x29e: sub     %edx,%ecx
     +0x2a0: movslq  %ecx,%rcx
     +0x2a3: shr     $0x1f,%rcx
     +0x2a7: or      %ecx,%edi
     +0x2a9: inc     %rax
     +0x2ac: cmp     $0x100,%rax
     +0x2b2: jne     <mldsa87_pk_from_sk+0x280>
     +0x2b4: mov     %rdi,0x120(%rsp)
     +0x2bc: lea     0x4a0(%r15),%rsi
     +0x2c3: lea     0x1e0(%rsp),%rdi
     +0x2cb: call    <mldsa87_polyeta_unpack>
     +0x2d0: xor     %r14d,%r14d
     +0x2d3: xor     %eax,%eax
     +0x2d5: data16  cs nopw 0x0(%rax,%rax,1)
     +0x2e0: movslq  0x1e0(%rsp,%rax,4),%rcx
     +0x2e8: mov     %ecx,%edx
     +0x2ea: neg     %edx
     +0x2ec: mov     %rcx,%rsi
     +0x2ef: shr     $0x1f,%rsi
     +0x2f3: xor     %ecx,%edx
     +0x2f5: and     %esi,%edx
     +0x2f7: xor     %ecx,%edx
     +0x2f9: mov     $0x2,%ecx
     +0x2fe: sub     %edx,%ecx
     +0x300: movslq  %ecx,%rcx
     +0x303: shr     $0x1f,%rcx
     +0x307: or      %ecx,%r14d
     +0x30a: inc     %rax
     +0x30d: cmp     $0x100,%rax
     +0x313: jne     <mldsa87_pk_from_sk+0x2e0>
     +0x315: lea     0x500(%r15),%rsi
     +0x31c: lea     0x1e0(%rsp),%rdi
     +0x324: call    <mldsa87_polyeta_unpack>
     +0x329: xor     %r12d,%r12d
     +0x32c: xor     %eax,%eax
     +0x32e: xchg    %ax,%ax
     +0x330: movslq  0x1e0(%rsp,%rax,4),%rcx
     +0x338: mov     %ecx,%edx
     +0x33a: neg     %edx
     +0x33c: mov     %rcx,%rsi
     +0x33f: shr     $0x1f,%rsi
     +0x343: xor     %ecx,%edx
     +0x345: and     %esi,%edx
     +0x347: xor     %ecx,%edx
     +0x349: mov     $0x2,%ecx
     +0x34e: sub     %edx,%ecx
     +0x350: movslq  %ecx,%rcx
     +0x353: shr     $0x1f,%rcx
     +0x357: or      %ecx,%r12d
     +0x35a: inc     %rax
     +0x35d: cmp     $0x100,%rax
     +0x363: jne     <mldsa87_pk_from_sk+0x330>
     +0x365: mov     %rbx,0xd8(%rsp)
     +0x36d: lea     0x560(%r15),%rsi
     +0x374: lea     0x1e0(%rsp),%rdi
     +0x37c: call    <mldsa87_polyeta_unpack>
     +0x381: xor     %r13d,%r13d
     +0x384: xor     %eax,%eax
     +0x386: cs      nopw 0x0(%rax,%rax,1)
     +0x390: movslq  0x1e0(%rsp,%rax,4),%rcx
     +0x398: mov     %ecx,%edx
     +0x39a: neg     %edx
     +0x39c: mov     %rcx,%rsi
     +0x39f: shr     $0x1f,%rsi
     +0x3a3: xor     %ecx,%edx
     +0x3a5: and     %esi,%edx
     +0x3a7: xor     %ecx,%edx
     +0x3a9: mov     $0x2,%ecx
     +0x3ae: sub     %edx,%ecx
     +0x3b0: movslq  %ecx,%rcx
     +0x3b3: shr     $0x1f,%rcx
     +0x3b7: or      %ecx,%r13d
     +0x3ba: inc     %rax
     +0x3bd: cmp     $0x100,%rax
     +0x3c3: jne     <mldsa87_pk_from_sk+0x390>
     +0x3c5: lea     0x5c0(%r15),%rsi
     +0x3cc: lea     0x1e0(%rsp),%rdi
     +0x3d4: call    <mldsa87_polyeta_unpack>
     +0x3d9: xor     %ebx,%ebx
     +0x3db: xor     %eax,%eax
     +0x3dd: nopl    (%rax)
     +0x3e0: movslq  0x1e0(%rsp,%rax,4),%rcx
     +0x3e8: mov     %ecx,%edx
     +0x3ea: neg     %edx
     +0x3ec: mov     %rcx,%rsi
     +0x3ef: shr     $0x1f,%rsi
     +0x3f3: xor     %ecx,%edx
     +0x3f5: and     %esi,%edx
     +0x3f7: xor     %ecx,%edx
     +0x3f9: mov     $0x2,%ecx
     +0x3fe: sub     %edx,%ecx
     +0x400: movslq  %ecx,%rcx
     +0x403: shr     $0x1f,%rcx
     +0x407: or      %ecx,%ebx
     +0x409: inc     %rax
     +0x40c: cmp     $0x100,%rax
     +0x412: jne     <mldsa87_pk_from_sk+0x3e0>
     +0x414: lea     0x5e0(%rsp),%rdi
     +0x41c: call    <mldsa_poly_ntt>
     +0x421: lea     0x9e0(%rsp),%rdi
     +0x429: call    <mldsa_poly_ntt>
     +0x42e: lea     0xde0(%rsp),%rdi
     +0x436: call    <mldsa_poly_ntt>
     +0x43b: lea     0x11e0(%rsp),%rdi
     +0x443: call    <mldsa_poly_ntt>
     +0x448: lea     0x15e0(%rsp),%rdi
     +0x450: call    <mldsa_poly_ntt>
     +0x455: lea     0x19e0(%rsp),%rdi
     +0x45d: call    <mldsa_poly_ntt>
     +0x462: lea     0x1de0(%rsp),%rdi
     +0x46a: call    <mldsa_poly_ntt>
     +0x46f: movdqa  0xe0(%rsp),%xmm0
     +0x478: movdqa  0xf0(%rsp),%xmm1
     +0x481: mov     0xd8(%rsp),%rax
     +0x489: movdqu  %xmm1,0x10(%rax)
     +0x48e: movdqu  %xmm0,(%rax)
     +0x492: lea     0x20(%rax),%rdi
     +0x496: lea     0x21e0(%rsp),%rsi
     +0x49e: lea     0xe0(%rsp),%r8
     +0x4a6: lea     0x5e0(%rsp),%rdx
     +0x4ae: lea     0x320(%r15),%rcx
     +0x4b5: call    <mld_compute_pack_t0_t187>
     +0x4ba: pxor    %xmm2,%xmm2
     +0x4be: xor     %eax,%eax
     +0x4c0: pxor    %xmm3,%xmm3
     +0x4c4: pxor    %xmm1,%xmm1
     +0x4c8: pxor    %xmm0,%xmm0
     +0x4cc: nopl    0x0(%rax)
     +0x4d0: movdqu  0x620(%r15,%rax,1),%xmm4
     +0x4da: movdqu  0x630(%r15,%rax,1),%xmm5
     +0x4e4: movdqa  %xmm2,%xmm6
     +0x4e8: movdqu  0x640(%r15,%rax,1),%xmm2
     +0x4f2: movdqa  %xmm3,%xmm7
     +0x4f6: movdqu  0x650(%r15,%rax,1),%xmm3
     +0x500: pxor    0x21e0(%rsp,%rax,1),%xmm4
     +0x509: pxor    0x21f0(%rsp,%rax,1),%xmm5
     +0x512: por     %xmm4,%xmm1
     +0x516: por     %xmm5,%xmm0
     +0x51a: pxor    %xmm4,%xmm6
     +0x51e: pxor    %xmm5,%xmm7
     +0x522: pxor    0x2200(%rsp,%rax,1),%xmm2
     +0x52b: pxor    0x2210(%rsp,%rax,1),%xmm3
     +0x534: por     %xmm2,%xmm1
     +0x538: por     %xmm3,%xmm0
     +0x53c: pxor    %xmm6,%xmm2
     +0x540: pxor    %xmm7,%xmm3
     +0x544: add     $0x40,%rax
     +0x548: cmp     $0xd00,%rax
     +0x54e: jne     <mldsa87_pk_from_sk+0x4d0>
     +0x550: pxor    %xmm2,%xmm3
     +0x554: pshufd  $0xee,%xmm3,%xmm2
     +0x559: pxor    %xmm3,%xmm2
     +0x55d: pshufd  $0x55,%xmm2,%xmm3
     +0x562: pxor    %xmm2,%xmm3
     +0x566: movdqa  %xmm3,%xmm2
     +0x56a: psrld   $0x10,%xmm2
     +0x56f: pxor    %xmm3,%xmm2
     +0x573: movdqa  %xmm2,%xmm3
     +0x577: psrlw   $0x8,%xmm3
     +0x57c: pxor    %xmm2,%xmm3
     +0x580: movd    %xmm3,%ecx
     +0x584: mov     %ecx,0xd0(%rsp)
     +0x58b: por     %xmm1,%xmm0
     +0x58f: pshufd  $0xee,%xmm0,%xmm1
     +0x594: por     %xmm0,%xmm1
     +0x598: pshufd  $0x55,%xmm1,%xmm0
     +0x59d: por     %xmm1,%xmm0
     +0x5a1: movdqa  %xmm0,%xmm1
     +0x5a5: psrld   $0x10,%xmm1
     +0x5aa: por     %xmm0,%xmm1
     +0x5ae: movdqa  %xmm1,%xmm0
     +0x5b2: psrlw   $0x8,%xmm0
     +0x5b7: por     %xmm1,%xmm0
     +0x5bb: movd    %xmm0,%eax
     +0x5bf: movzbl  %al,%eax
     +0x5c2: neg     %rax
     +0x5c5: shr     $0x20,%rax
     +0x5c9: xor     %cl,%al
     +0x5cb: mov     %rax,0x118(%rsp)
     +0x5d3: pxor    %xmm0,%xmm0
     +0x5d7: movdqu  %xmm0,0xbc(%rsp)
     +0x5e0: movdqa  %xmm0,0xb0(%rsp)
     +0x5e9: movdqa  %xmm0,0xa0(%rsp)
     +0x5f2: movdqa  %xmm0,0x90(%rsp)
     +0x5fb: movdqa  %xmm0,0x80(%rsp)
     +0x604: movdqa  %xmm0,0x70(%rsp)
     +0x60a: movdqa  %xmm0,0x60(%rsp)
     +0x610: movdqa  %xmm0,0x50(%rsp)
     +0x616: movdqa  %xmm0,0x40(%rsp)
     +0x61c: movdqa  %xmm0,0x30(%rsp)
     +0x622: movdqa  %xmm0,0x20(%rsp)
     +0x628: movdqa  %xmm0,0x10(%rsp)
     +0x62e: movdqa  %xmm0,(%rsp)
     +0x633: mov     0xd8(%rsp),%r15
     +0x63b: movups  (%r15),%xmm0
     +0x63f: movups  0x10(%r15),%xmm1
     +0x644: movaps  %xmm0,(%rsp)
     +0x648: movaps  %xmm1,0x10(%rsp)
     +0x64d: movups  0x20(%r15),%xmm0
     +0x652: movups  0x30(%r15),%xmm1
     +0x657: movaps  %xmm0,0x20(%rsp)
     +0x65c: movaps  %xmm1,0x30(%rsp)
     +0x661: movups  0x40(%r15),%xmm0
     +0x666: movups  0x50(%r15),%xmm1
     +0x66b: xorps   0x40(%rsp),%xmm0
     +0x670: xorps   0x50(%rsp),%xmm1
     +0x675: movaps  %xmm0,0x40(%rsp)
     +0x67a: movaps  %xmm1,0x50(%rsp)
     +0x67f: movups  0x60(%r15),%xmm0
     +0x684: movups  0x70(%r15),%xmm1
     +0x689: xorps   0x60(%rsp),%xmm0
     +0x68e: xorps   0x70(%rsp),%xmm1
     +0x693: movaps  %xmm0,0x60(%rsp)
     +0x698: movaps  %xmm1,0x70(%rsp)
     +0x69d: mov     0x80(%r15),%rax
     +0x6a4: xor     %rax,0x80(%rsp)
     +0x6ac: mov     %rsp,%rdi
     +0x6af: call    <mldsa_keccakf1600_permute>
     +0x6b4: movups  0x88(%r15),%xmm0
     +0x6bc: movups  0x98(%r15),%xmm1
     +0x6c4: xorps   (%rsp),%xmm0
     +0x6c8: xorps   0x10(%rsp),%xmm1
     +0x6cd: movaps  %xmm0,(%rsp)
     +0x6d1: movaps  %xmm1,0x10(%rsp)
     +0x6d6: movups  0xa8(%r15),%xmm0
     +0x6de: movups  0xb8(%r15),%xmm1
     +0x6e6: xorps   0x20(%rsp),%xmm0
     +0x6eb: xorps   0x30(%rsp),%xmm1
     +0x6f0: movaps  %xmm0,0x20(%rsp)
     +0x6f5: movaps  %xmm1,0x30(%rsp)
     +0x6fa: movups  0xc8(%r15),%xmm0
     +0x702: movups  0xd8(%r15),%xmm1
     +0x70a: xorps   0x40(%rsp),%xmm0
     +0x70f: xorps   0x50(%rsp),%xmm1
     +0x714: movaps  %xmm0,0x40(%rsp)
     +0x719: movaps  %xmm1,0x50(%rsp)
     +0x71e: movups  0xe8(%r15),%xmm0
     +0x726: movups  0xf8(%r15),%xmm1
     +0x72e: xorps   0x60(%rsp),%xmm0
     +0x733: xorps   0x70(%rsp),%xmm1
     +0x738: movaps  %xmm0,0x60(%rsp)
     +0x73d: movaps  %xmm1,0x70(%rsp)
     +0x742: mov     0x108(%r15),%rax
     +0x749: xor     %rax,0x80(%rsp)
     +0x751: mov     %rsp,%rdi
     +0x754: call    <mldsa_keccakf1600_permute>
     +0x759: movups  0x110(%r15),%xmm0
     +0x761: movups  0x120(%r15),%xmm1
     +0x769: xorps   (%rsp),%xmm0
     +0x76d: xorps   0x10(%rsp),%xmm1
     +0x772: movaps  %xmm0,(%rsp)
     +0x776: movaps  %xmm1,0x10(%rsp)
     +0x77b: movups  0x130(%r15),%xmm0
     +0x783: movups  0x140(%r15),%xmm1
     +0x78b: xorps   0x20(%rsp),%xmm0
     +0x790: xorps   0x30(%rsp),%xmm1
     +0x795: movaps  %xmm0,0x20(%rsp)
     +0x79a: movaps  %xmm1,0x30(%rsp)
     +0x79f: movups  0x150(%r15),%xmm0
     +0x7a7: movups  0x160(%r15),%xmm1
     +0x7af: xorps   0x40(%rsp),%xmm0
     +0x7b4: xorps   0x50(%rsp),%xmm1
     +0x7b9: movaps  %xmm0,0x40(%rsp)
     +0x7be: movaps  %xmm1,0x50(%rsp)
     +0x7c3: movups  0x170(%r15),%xmm0
     +0x7cb: movups  0x180(%r15),%xmm1
     +0x7d3: xorps   0x60(%rsp),%xmm0
     +0x7d8: xorps   0x70(%rsp),%xmm1
     +0x7dd: movaps  %xmm0,0x60(%rsp)
     +0x7e2: movaps  %xmm1,0x70(%rsp)
     +0x7e7: mov     0x190(%r15),%rax
     +0x7ee: xor     %rax,0x80(%rsp)
     +0x7f6: mov     %rsp,%rdi
     +0x7f9: call    <mldsa_keccakf1600_permute>
     +0x7fe: movups  0x198(%r15),%xmm0
     +0x806: movups  0x1a8(%r15),%xmm1
     +0x80e: xorps   (%rsp),%xmm0
     +0x812: xorps   0x10(%rsp),%xmm1
     +0x817: movaps  %xmm0,(%rsp)
     +0x81b: movaps  %xmm1,0x10(%rsp)
     +0x820: movups  0x1b8(%r15),%xmm0
     +0x828: movups  0x1c8(%r15),%xmm1
     +0x830: xorps   0x20(%rsp),%xmm0
     +0x835: xorps   0x30(%rsp),%xmm1
     +0x83a: movaps  %xmm0,0x20(%rsp)
     +0x83f: movaps  %xmm1,0x30(%rsp)
     +0x844: movups  0x1d8(%r15),%xmm0
     +0x84c: movups  0x1e8(%r15),%xmm1
     +0x854: xorps   0x40(%rsp),%xmm0
     +0x859: xorps   0x50(%rsp),%xmm1
     +0x85e: movaps  %xmm0,0x40(%rsp)
     +0x863: movaps  %xmm1,0x50(%rsp)
     +0x868: movups  0x1f8(%r15),%xmm0
     +0x870: movups  0x208(%r15),%xmm1
     +0x878: xorps   0x60(%rsp),%xmm0
     +0x87d: xorps   0x70(%rsp),%xmm1
     +0x882: movaps  %xmm0,0x60(%rsp)
     +0x887: movaps  %xmm1,0x70(%rsp)
     +0x88c: mov     0x218(%r15),%rax
     +0x893: xor     %rax,0x80(%rsp)
     +0x89b: mov     %rsp,%rdi
     +0x89e: call    <mldsa_keccakf1600_permute>
     +0x8a3: movups  0x220(%r15),%xmm0
     +0x8ab: movups  0x230(%r15),%xmm1
     +0x8b3: xorps   (%rsp),%xmm0
     +0x8b7: xorps   0x10(%rsp),%xmm1
     +0x8bc: movaps  %xmm0,(%rsp)
     +0x8c0: movaps  %xmm1,0x10(%rsp)
     +0x8c5: movups  0x240(%r15),%xmm0
     +0x8cd: movups  0x250(%r15),%xmm1
     +0x8d5: xorps   0x20(%rsp),%xmm0
     +0x8da: xorps   0x30(%rsp),%xmm1
     +0x8df: movaps  %xmm0,0x20(%rsp)
     +0x8e4: movaps  %xmm1,0x30(%rsp)
     +0x8e9: movups  0x260(%r15),%xmm0
     +0x8f1: movups  0x270(%r15),%xmm1
     +0x8f9: xorps   0x40(%rsp),%xmm0
     +0x8fe: xorps   0x50(%rsp),%xmm1
     +0x903: movaps  %xmm0,0x40(%rsp)
     +0x908: movaps  %xmm1,0x50(%rsp)
     +0x90d: movups  0x280(%r15),%xmm0
     +0x915: movups  0x290(%r15),%xmm1
     +0x91d: xorps   0x60(%rsp),%xmm0
     +0x922: xorps   0x70(%rsp),%xmm1
     +0x927: movaps  %xmm0,0x60(%rsp)
     +0x92c: movaps  %xmm1,0x70(%rsp)
     +0x931: mov     0x2a0(%r15),%rax
     +0x938: xor     %rax,0x80(%rsp)
     +0x940: mov     %rsp,%rdi
     +0x943: call    <mldsa_keccakf1600_permute>
     +0x948: movups  0x2a8(%r15),%xmm0
     +0x950: movups  0x2b8(%r15),%xmm1
     +0x958: xorps   (%rsp),%xmm0
     +0x95c: xorps   0x10(%rsp),%xmm1
     +0x961: movaps  %xmm0,(%rsp)
     +0x965: movaps  %xmm1,0x10(%rsp)
     +0x96a: movups  0x2c8(%r15),%xmm0
     +0x972: movups  0x2d8(%r15),%xmm1
     +0x97a: xorps   0x20(%rsp),%xmm0
     +0x97f: xorps   0x30(%rsp),%xmm1
     +0x984: movaps  %xmm0,0x20(%rsp)
     +0x989: movaps  %xmm1,0x30(%rsp)
     +0x98e: movups  0x2e8(%r15),%xmm0
     +0x996: movups  0x2f8(%r15),%xmm1
     +0x99e: xorps   0x40(%rsp),%xmm0
     +0x9a3: xorps   0x50(%rsp),%xmm1
     +0x9a8: movaps  %xmm0,0x40(%rsp)
     +0x9ad: movaps  %xmm1,0x50(%rsp)
     +0x9b2: movups  0x308(%r15),%xmm0
     +0x9ba: movups  0x318(%r15),%xmm1
     +0x9c2: xorps   0x60(%rsp),%xmm0
     +0x9c7: xorps   0x70(%rsp),%xmm1
     +0x9cc: movaps  %xmm0,0x60(%rsp)
     +0x9d1: movaps  %xmm1,0x70(%rsp)
     +0x9d6: mov     0x328(%r15),%rax
     +0x9dd: xor     %rax,0x80(%rsp)
     +0x9e5: mov     %rsp,%rdi
     +0x9e8: call    <mldsa_keccakf1600_permute>
     +0x9ed: movups  0x330(%r15),%xmm0
     +0x9f5: movups  0x340(%r15),%xmm1
     +0x9fd: xorps   (%rsp),%xmm0
     +0xa01: xorps   0x10(%rsp),%xmm1
     +0xa06: movaps  %xmm0,(%rsp)
     +0xa0a: movaps  %xmm1,0x10(%rsp)
     +0xa0f: movups  0x350(%r15),%xmm0
     +0xa17: movups  0x360(%r15),%xmm1
     +0xa1f: xorps   0x20(%rsp),%xmm0
     +0xa24: xorps   0x30(%rsp),%xmm1
     +0xa29: movaps  %xmm0,0x20(%rsp)
     +0xa2e: movaps  %xmm1,0x30(%rsp)
     +0xa33: movups  0x370(%r15),%xmm0
     +0xa3b: movups  0x380(%r15),%xmm1
     +0xa43: xorps   0x40(%rsp),%xmm0
     +0xa48: xorps   0x50(%rsp),%xmm1
     +0xa4d: movaps  %xmm0,0x40(%rsp)
     +0xa52: movaps  %xmm1,0x50(%rsp)
     +0xa57: movups  0x390(%r15),%xmm0
     +0xa5f: movups  0x3a0(%r15),%xmm1
     +0xa67: xorps   0x60(%rsp),%xmm0
     +0xa6c: xorps   0x70(%rsp),%xmm1
     +0xa71: movaps  %xmm0,0x60(%rsp)
     +0xa76: movaps  %xmm1,0x70(%rsp)
     +0xa7b: mov     0x3b0(%r15),%rax
     +0xa82: xor     %rax,0x80(%rsp)
     +0xa8a: mov     %rsp,%rdi
     +0xa8d: call    <mldsa_keccakf1600_permute>
     +0xa92: movups  0x3b8(%r15),%xmm0
     +0xa9a: movups  0x3c8(%r15),%xmm1
     +0xaa2: xorps   (%rsp),%xmm0
     +0xaa6: xorps   0x10(%rsp),%xmm1
     +0xaab: movaps  %xmm0,(%rsp)
     +0xaaf: movaps  %xmm1,0x10(%rsp)
     +0xab4: movups  0x3d8(%r15),%xmm0
     +0xabc: movups  0x3e8(%r15),%xmm1
     +0xac4: xorps   0x20(%rsp),%xmm0
     +0xac9: xorps   0x30(%rsp),%xmm1
     +0xace: movaps  %xmm0,0x20(%rsp)
     +0xad3: movaps  %xmm1,0x30(%rsp)
     +0xad8: movups  0x3f8(%r15),%xmm0
     +0xae0: movups  0x408(%r15),%xmm1
     +0xae8: xorps   0x40(%rsp),%xmm0
     +0xaed: xorps   0x50(%rsp),%xmm1
     +0xaf2: movaps  %xmm0,0x40(%rsp)
     +0xaf7: movaps  %xmm1,0x50(%rsp)
     +0xafc: movups  0x418(%r15),%xmm0
     +0xb04: movups  0x428(%r15),%xmm1
     +0xb0c: xorps   0x60(%rsp),%xmm0
     +0xb11: xorps   0x70(%rsp),%xmm1
     +0xb16: movaps  %xmm0,0x60(%rsp)
     +0xb1b: movaps  %xmm1,0x70(%rsp)
     +0xb20: mov     0x438(%r15),%rax
     +0xb27: xor     %rax,0x80(%rsp)
     +0xb2f: mov     %rsp,%rdi
     +0xb32: call    <mldsa_keccakf1600_permute>
     +0xb37: movups  0x440(%r15),%xmm0
     +0xb3f: movups  0x450(%r15),%xmm1
     +0xb47: xorps   (%rsp),%xmm0
     +0xb4b: xorps   0x10(%rsp),%xmm1
     +0xb50: movaps  %xmm0,(%rsp)
     +0xb54: movaps  %xmm1,0x10(%rsp)
     +0xb59: movups  0x460(%r15),%xmm0
     +0xb61: movups  0x470(%r15),%xmm1
     +0xb69: xorps   0x20(%rsp),%xmm0
     +0xb6e: xorps   0x30(%rsp),%xmm1
     +0xb73: movaps  %xmm0,0x20(%rsp)
     +0xb78: movaps  %xmm1,0x30(%rsp)
     +0xb7d: movups  0x480(%r15),%xmm0
     +0xb85: movups  0x490(%r15),%xmm1
     +0xb8d: xorps   0x40(%rsp),%xmm0
     +0xb92: xorps   0x50(%rsp),%xmm1
     +0xb97: movaps  %xmm0,0x40(%rsp)
     +0xb9c: movaps  %xmm1,0x50(%rsp)
     +0xba1: movups  0x4a0(%r15),%xmm0
     +0xba9: movups  0x4b0(%r15),%xmm1
     +0xbb1: xorps   0x60(%rsp),%xmm0
     +0xbb6: xorps   0x70(%rsp),%xmm1
     +0xbbb: movaps  %xmm0,0x60(%rsp)
     +0xbc0: movaps  %xmm1,0x70(%rsp)
     +0xbc5: mov     0x4c0(%r15),%rax
     +0xbcc: xor     %rax,0x80(%rsp)
     +0xbd4: mov     %rsp,%rdi
     +0xbd7: call    <mldsa_keccakf1600_permute>
     +0xbdc: movups  0x4c8(%r15),%xmm0
     +0xbe4: movups  0x4d8(%r15),%xmm1
     +0xbec: xorps   (%rsp),%xmm0
     +0xbf0: xorps   0x10(%rsp),%xmm1
     +0xbf5: movaps  %xmm0,(%rsp)
     +0xbf9: movaps  %xmm1,0x10(%rsp)
     +0xbfe: movups  0x4e8(%r15),%xmm0
     +0xc06: movups  0x4f8(%r15),%xmm1
     +0xc0e: xorps   0x20(%rsp),%xmm0
     +0xc13: xorps   0x30(%rsp),%xmm1
     +0xc18: movaps  %xmm0,0x20(%rsp)
     +0xc1d: movaps  %xmm1,0x30(%rsp)
     +0xc22: movups  0x508(%r15),%xmm0
     +0xc2a: movups  0x518(%r15),%xmm1
     +0xc32: xorps   0x40(%rsp),%xmm0
     +0xc37: xorps   0x50(%rsp),%xmm1
     +0xc3c: movaps  %xmm0,0x40(%rsp)
     +0xc41: movaps  %xmm1,0x50(%rsp)
     +0xc46: movups  0x528(%r15),%xmm0
     +0xc4e: movups  0x538(%r15),%xmm1
     +0xc56: xorps   0x60(%rsp),%xmm0
     +0xc5b: xorps   0x70(%rsp),%xmm1
     +0xc60: movaps  %xmm0,0x60(%rsp)
     +0xc65: movaps  %xmm1,0x70(%rsp)
     +0xc6a: mov     0x548(%r15),%rax
     +0xc71: xor     %rax,0x80(%rsp)
     +0xc79: mov     %rsp,%rdi
     +0xc7c: call    <mldsa_keccakf1600_permute>
     +0xc81: movups  0x550(%r15),%xmm0
     +0xc89: movups  0x560(%r15),%xmm1
     +0xc91: xorps   (%rsp),%xmm0
     +0xc95: xorps   0x10(%rsp),%xmm1
     +0xc9a: movaps  %xmm0,(%rsp)
     +0xc9e: movaps  %xmm1,0x10(%rsp)
     +0xca3: movups  0x570(%r15),%xmm0
     +0xcab: movups  0x580(%r15),%xmm1
     +0xcb3: xorps   0x20(%rsp),%xmm0
     +0xcb8: xorps   0x30(%rsp),%xmm1
     +0xcbd: movaps  %xmm0,0x20(%rsp)
     +0xcc2: movaps  %xmm1,0x30(%rsp)
     +0xcc7: movups  0x590(%r15),%xmm0
     +0xccf: movups  0x5a0(%r15),%xmm1
     +0xcd7: xorps   0x40(%rsp),%xmm0
     +0xcdc: xorps   0x50(%rsp),%xmm1
     +0xce1: movaps  %xmm0,0x40(%rsp)
     +0xce6: movaps  %xmm1,0x50(%rsp)
     +0xceb: movups  0x5b0(%r15),%xmm0
     +0xcf3: movups  0x5c0(%r15),%xmm1
     +0xcfb: xorps   0x60(%rsp),%xmm0
     +0xd00: xorps   0x70(%rsp),%xmm1
     +0xd05: movaps  %xmm0,0x60(%rsp)
     +0xd0a: movaps  %xmm1,0x70(%rsp)
     +0xd0f: mov     0x5d0(%r15),%rax
     +0xd16: xor     %rax,0x80(%rsp)
     +0xd1e: mov     %rsp,%rdi
     +0xd21: call    <mldsa_keccakf1600_permute>
     +0xd26: movups  0x5d8(%r15),%xmm0
     +0xd2e: movups  0x5e8(%r15),%xmm1
     +0xd36: xorps   (%rsp),%xmm0
     +0xd3a: xorps   0x10(%rsp),%xmm1
     +0xd3f: movaps  %xmm0,(%rsp)
     +0xd43: movaps  %xmm1,0x10(%rsp)
     +0xd48: movups  0x5f8(%r15),%xmm0
     +0xd50: movups  0x608(%r15),%xmm1
     +0xd58: xorps   0x20(%rsp),%xmm0
     +0xd5d: xorps   0x30(%rsp),%xmm1
     +0xd62: movaps  %xmm0,0x20(%rsp)
     +0xd67: movaps  %xmm1,0x30(%rsp)
     +0xd6c: movups  0x618(%r15),%xmm0
     +0xd74: movups  0x628(%r15),%xmm1
     +0xd7c: xorps   0x40(%rsp),%xmm0
     +0xd81: xorps   0x50(%rsp),%xmm1
     +0xd86: movaps  %xmm0,0x40(%rsp)
     +0xd8b: movaps  %xmm1,0x50(%rsp)
     +0xd90: movups  0x638(%r15),%xmm0
     +0xd98: movups  0x648(%r15),%xmm1
     +0xda0: xorps   0x60(%rsp),%xmm0
     +0xda5: xorps   0x70(%rsp),%xmm1
     +0xdaa: movaps  %xmm0,0x60(%rsp)
     +0xdaf: movaps  %xmm1,0x70(%rsp)
     +0xdb4: mov     0x658(%r15),%rax
     +0xdbb: xor     %rax,0x80(%rsp)
     +0xdc3: mov     %rsp,%rdi
     +0xdc6: call    <mldsa_keccakf1600_permute>
     +0xdcb: movups  0x660(%r15),%xmm0
     +0xdd3: movups  0x670(%r15),%xmm1
     +0xddb: xorps   (%rsp),%xmm0
     +0xddf: xorps   0x10(%rsp),%xmm1
     +0xde4: movaps  %xmm0,(%rsp)
     +0xde8: movaps  %xmm1,0x10(%rsp)
     +0xded: movups  0x680(%r15),%xmm0
     +0xdf5: movups  0x690(%r15),%xmm1
     +0xdfd: xorps   0x20(%rsp),%xmm0
     +0xe02: xorps   0x30(%rsp),%xmm1
     +0xe07: movaps  %xmm0,0x20(%rsp)
     +0xe0c: movaps  %xmm1,0x30(%rsp)
     +0xe11: movups  0x6a0(%r15),%xmm0
     +0xe19: movups  0x6b0(%r15),%xmm1
     +0xe21: xorps   0x40(%rsp),%xmm0
     +0xe26: xorps   0x50(%rsp),%xmm1
     +0xe2b: movaps  %xmm0,0x40(%rsp)
     +0xe30: movaps  %xmm1,0x50(%rsp)
     +0xe35: movups  0x6c0(%r15),%xmm0
     +0xe3d: movups  0x6d0(%r15),%xmm1
     +0xe45: xorps   0x60(%rsp),%xmm0
     +0xe4a: xorps   0x70(%rsp),%xmm1
     +0xe4f: movaps  %xmm0,0x60(%rsp)
     +0xe54: movaps  %xmm1,0x70(%rsp)
     +0xe59: mov     0x6e0(%r15),%rax
     +0xe60: xor     %rax,0x80(%rsp)
     +0xe68: mov     %rsp,%rdi
     +0xe6b: call    <mldsa_keccakf1600_permute>
     +0xe70: movups  0x6e8(%r15),%xmm0
     +0xe78: movups  0x6f8(%r15),%xmm1
     +0xe80: xorps   (%rsp),%xmm0
     +0xe84: xorps   0x10(%rsp),%xmm1
     +0xe89: movaps  %xmm0,(%rsp)
     +0xe8d: movaps  %xmm1,0x10(%rsp)
     +0xe92: movups  0x708(%r15),%xmm0
     +0xe9a: movups  0x718(%r15),%xmm1
     +0xea2: xorps   0x20(%rsp),%xmm0
     +0xea7: xorps   0x30(%rsp),%xmm1
     +0xeac: movaps  %xmm0,0x20(%rsp)
     +0xeb1: movaps  %xmm1,0x30(%rsp)
     +0xeb6: movups  0x728(%r15),%xmm0
     +0xebe: movups  0x738(%r15),%xmm1
     +0xec6: xorps   0x40(%rsp),%xmm0
     +0xecb: xorps   0x50(%rsp),%xmm1
     +0xed0: movaps  %xmm0,0x40(%rsp)
     +0xed5: movaps  %xmm1,0x50(%rsp)
     +0xeda: movups  0x748(%r15),%xmm0
     +0xee2: movups  0x758(%r15),%xmm1
     +0xeea: xorps   0x60(%rsp),%xmm0
     +0xeef: xorps   0x70(%rsp),%xmm1
     +0xef4: movaps  %xmm0,0x60(%rsp)
     +0xef9: movaps  %xmm1,0x70(%rsp)
     +0xefe: mov     0x768(%r15),%rax
     +0xf05: xor     %rax,0x80(%rsp)
     +0xf0d: mov     %rsp,%rdi
     +0xf10: call    <mldsa_keccakf1600_permute>
     +0xf15: movups  0x770(%r15),%xmm0
     +0xf1d: movups  0x780(%r15),%xmm1
     +0xf25: xorps   (%rsp),%xmm0
     +0xf29: xorps   0x10(%rsp),%xmm1
     +0xf2e: movaps  %xmm0,(%rsp)
     +0xf32: movaps  %xmm1,0x10(%rsp)
     +0xf37: movups  0x790(%r15),%xmm0
     +0xf3f: movups  0x7a0(%r15),%xmm1
     +0xf47: xorps   0x20(%rsp),%xmm0
     +0xf4c: xorps   0x30(%rsp),%xmm1
     +0xf51: movaps  %xmm0,0x20(%rsp)
     +0xf56: movaps  %xmm1,0x30(%rsp)
     +0xf5b: movups  0x7b0(%r15),%xmm0
     +0xf63: movups  0x7c0(%r15),%xmm1
     +0xf6b: xorps   0x40(%rsp),%xmm0
     +0xf70: xorps   0x50(%rsp),%xmm1
     +0xf75: movaps  %xmm0,0x40(%rsp)
     +0xf7a: movaps  %xmm1,0x50(%rsp)
     +0xf7f: movups  0x7d0(%r15),%xmm0
     +0xf87: movups  0x7e0(%r15),%xmm1
     +0xf8f: xorps   0x60(%rsp),%xmm0
     +0xf94: xorps   0x70(%rsp),%xmm1
     +0xf99: movaps  %xmm0,0x60(%rsp)
     +0xf9e: movaps  %xmm1,0x70(%rsp)
     +0xfa3: mov     0x7f0(%r15),%rax
     +0xfaa: xor     %rax,0x80(%rsp)
     +0xfb2: mov     %rsp,%rdi
     +0xfb5: call    <mldsa_keccakf1600_permute>
     +0xfba: movups  0x7f8(%r15),%xmm0
     +0xfc2: movups  0x808(%r15),%xmm1
     +0xfca: xorps   (%rsp),%xmm0
     +0xfce: xorps   0x10(%rsp),%xmm1
     +0xfd3: movaps  %xmm0,(%rsp)
     +0xfd7: movaps  %xmm1,0x10(%rsp)
     +0xfdc: movups  0x818(%r15),%xmm0
     +0xfe4: movups  0x828(%r15),%xmm1
     +0xfec: xorps   0x20(%rsp),%xmm0
     +0xff1: xorps   0x30(%rsp),%xmm1
     +0xff6: movaps  %xmm0,0x20(%rsp)
     +0xffb: movaps  %xmm1,0x30(%rsp)
    +0x1000: movups  0x838(%r15),%xmm0
    +0x1008: movups  0x848(%r15),%xmm1
    +0x1010: xorps   0x40(%rsp),%xmm0
    +0x1015: xorps   0x50(%rsp),%xmm1
    +0x101a: movaps  %xmm0,0x40(%rsp)
    +0x101f: movaps  %xmm1,0x50(%rsp)
    +0x1024: movups  0x858(%r15),%xmm0
    +0x102c: movups  0x868(%r15),%xmm1
    +0x1034: xorps   0x60(%rsp),%xmm0
    +0x1039: xorps   0x70(%rsp),%xmm1
    +0x103e: movaps  %xmm0,0x60(%rsp)
    +0x1043: movaps  %xmm1,0x70(%rsp)
    +0x1048: mov     0x878(%r15),%rax
    +0x104f: xor     %rax,0x80(%rsp)
    +0x1057: mov     %rsp,%rdi
    +0x105a: call    <mldsa_keccakf1600_permute>
    +0x105f: movups  0x880(%r15),%xmm0
    +0x1067: movups  0x890(%r15),%xmm1
    +0x106f: xorps   (%rsp),%xmm0
    +0x1073: xorps   0x10(%rsp),%xmm1
    +0x1078: movaps  %xmm0,(%rsp)
    +0x107c: movaps  %xmm1,0x10(%rsp)
    +0x1081: movups  0x8a0(%r15),%xmm0
    +0x1089: movups  0x8b0(%r15),%xmm1
    +0x1091: xorps   0x20(%rsp),%xmm0
    +0x1096: xorps   0x30(%rsp),%xmm1
    +0x109b: movaps  %xmm0,0x20(%rsp)
    +0x10a0: movaps  %xmm1,0x30(%rsp)
    +0x10a5: movups  0x8c0(%r15),%xmm0
    +0x10ad: movups  0x8d0(%r15),%xmm1
    +0x10b5: xorps   0x40(%rsp),%xmm0
    +0x10ba: xorps   0x50(%rsp),%xmm1
    +0x10bf: movaps  %xmm0,0x40(%rsp)
    +0x10c4: movaps  %xmm1,0x50(%rsp)
    +0x10c9: movups  0x8e0(%r15),%xmm0
    +0x10d1: movups  0x8f0(%r15),%xmm1
    +0x10d9: xorps   0x60(%rsp),%xmm0
    +0x10de: xorps   0x70(%rsp),%xmm1
    +0x10e3: movaps  %xmm0,0x60(%rsp)
    +0x10e8: movaps  %xmm1,0x70(%rsp)
    +0x10ed: mov     0x900(%r15),%rax
    +0x10f4: xor     %rax,0x80(%rsp)
    +0x10fc: mov     %rsp,%rdi
    +0x10ff: call    <mldsa_keccakf1600_permute>
    +0x1104: movups  0x908(%r15),%xmm0
    +0x110c: movups  0x918(%r15),%xmm1
    +0x1114: xorps   (%rsp),%xmm0
    +0x1118: xorps   0x10(%rsp),%xmm1
    +0x111d: movaps  %xmm0,(%rsp)
    +0x1121: movaps  %xmm1,0x10(%rsp)
    +0x1126: movups  0x928(%r15),%xmm0
    +0x112e: movups  0x938(%r15),%xmm1
    +0x1136: xorps   0x20(%rsp),%xmm0
    +0x113b: xorps   0x30(%rsp),%xmm1
    +0x1140: movaps  %xmm0,0x20(%rsp)
    +0x1145: movaps  %xmm1,0x30(%rsp)
    +0x114a: movups  0x948(%r15),%xmm0
    +0x1152: movups  0x958(%r15),%xmm1
    +0x115a: xorps   0x40(%rsp),%xmm0
    +0x115f: xorps   0x50(%rsp),%xmm1
    +0x1164: movaps  %xmm0,0x40(%rsp)
    +0x1169: movaps  %xmm1,0x50(%rsp)
    +0x116e: movups  0x968(%r15),%xmm0
    +0x1176: movups  0x978(%r15),%xmm1
    +0x117e: xorps   0x60(%rsp),%xmm0
    +0x1183: xorps   0x70(%rsp),%xmm1
    +0x1188: movaps  %xmm0,0x60(%rsp)
    +0x118d: movaps  %xmm1,0x70(%rsp)
    +0x1192: mov     0x988(%r15),%rax
    +0x1199: xor     %rax,0x80(%rsp)
    +0x11a1: mov     %rsp,%rdi
    +0x11a4: call    <mldsa_keccakf1600_permute>
    +0x11a9: movups  0x990(%r15),%xmm0
    +0x11b1: movups  0x9a0(%r15),%xmm1
    +0x11b9: xorps   (%rsp),%xmm0
    +0x11bd: xorps   0x10(%rsp),%xmm1
    +0x11c2: movaps  %xmm0,(%rsp)
    +0x11c6: movaps  %xmm1,0x10(%rsp)
    +0x11cb: movups  0x9b0(%r15),%xmm0
    +0x11d3: movups  0x9c0(%r15),%xmm1
    +0x11db: xorps   0x20(%rsp),%xmm0
    +0x11e0: xorps   0x30(%rsp),%xmm1
    +0x11e5: movaps  %xmm0,0x20(%rsp)
    +0x11ea: movaps  %xmm1,0x30(%rsp)
    +0x11ef: movups  0x9d0(%r15),%xmm0
    +0x11f7: movups  0x9e0(%r15),%xmm1
    +0x11ff: xorps   0x40(%rsp),%xmm0
    +0x1204: xorps   0x50(%rsp),%xmm1
    +0x1209: movaps  %xmm0,0x40(%rsp)
    +0x120e: movaps  %xmm1,0x50(%rsp)
    +0x1213: movups  0x9f0(%r15),%xmm0
    +0x121b: movups  0xa00(%r15),%xmm1
    +0x1223: xorps   0x60(%rsp),%xmm0
    +0x1228: xorps   0x70(%rsp),%xmm1
    +0x122d: movaps  %xmm0,0x60(%rsp)
    +0x1232: movaps  %xmm1,0x70(%rsp)
    +0x1237: mov     0xa10(%r15),%rax
    +0x123e: xor     %rax,0x80(%rsp)
    +0x1246: mov     %rsp,%rdi
    +0x1249: call    <mldsa_keccakf1600_permute>
    +0x124e: mov     0xa18(%r15),%rax
    +0x1255: xor     %rax,(%rsp)
    +0x1259: xorb    $0x1f,0x8(%rsp)
    +0x125e: xorb    $0x80,0x87(%rsp)
    +0x1266: movl    $0x88,0xc8(%rsp)
    +0x1271: mov     %rsp,%rdi
    +0x1274: call    <mldsa_keccakf1600_permute>
    +0x1279: movaps  (%rsp),%xmm0
    +0x127d: movaps  0x10(%rsp),%xmm1
    +0x1282: movaps  0x20(%rsp),%xmm2
    +0x1287: movaps  0x30(%rsp),%xmm3
    +0x128c: movaps  %xmm3,0x170(%rsp)
    +0x1294: movaps  %xmm2,0x160(%rsp)
    +0x129c: movaps  %xmm1,0x150(%rsp)
    +0x12a4: movaps  %xmm0,0x140(%rsp)
    +0x12ac: xorps   %xmm0,%xmm0
    +0x12af: movaps  %xmm0,0x40(%rsp)
    +0x12b4: movaps  %xmm0,0x50(%rsp)
    +0x12b9: movaps  %xmm0,0x60(%rsp)
    +0x12be: movaps  %xmm0,0x70(%rsp)
    +0x12c3: movaps  %xmm0,0x80(%rsp)
    +0x12cb: movaps  %xmm0,0x90(%rsp)
    +0x12d3: movaps  %xmm0,0xa0(%rsp)
    +0x12db: movaps  %xmm0,0xb0(%rsp)
    +0x12e3: movaps  %xmm0,0xc0(%rsp)
    +0x12eb: movaps  %xmm0,(%rsp)
    +0x12ef: movaps  %xmm0,0x10(%rsp)
    +0x12f4: movaps  %xmm0,0x20(%rsp)
    +0x12f9: movaps  %xmm0,0x30(%rsp)
    +0x12fe: mov     %rsp,%rax
    +0x1301: mov     0x118(%rsp),%rsi
    +0x1309: xor     0xd0(%rsp),%sil
    +0x1311: movdqa  0x140(%rsp),%xmm2
    +0x131a: movdqa  0x150(%rsp),%xmm1
    +0x1323: movdqa  0x160(%rsp),%xmm0
    +0x132c: pxor    0x180(%rsp),%xmm2
    +0x1335: pxor    0x190(%rsp),%xmm1
    +0x133e: pxor    0x1a0(%rsp),%xmm0
    +0x1347: movdqa  0x170(%rsp),%xmm3
    +0x1350: pxor    0x1b0(%rsp),%xmm3
    +0x1359: movdqa  %xmm0,%xmm4
    +0x135d: por     %xmm2,%xmm4
    +0x1361: pxor    %xmm2,%xmm0
    +0x1365: movdqa  %xmm1,%xmm2
    +0x1369: por     %xmm3,%xmm2
    +0x136d: por     %xmm4,%xmm2
    +0x1371: pshufd  $0xee,%xmm2,%xmm4
    +0x1376: por     %xmm2,%xmm4
    +0x137a: pshufd  $0x55,%xmm4,%xmm2
    +0x137f: por     %xmm4,%xmm2
    +0x1383: movdqa  %xmm2,%xmm4
    +0x1387: psrld   $0x10,%xmm4
    +0x138c: por     %xmm2,%xmm4
    +0x1390: movdqa  %xmm4,%xmm2
    +0x1394: psrlw   $0x8,%xmm2
    +0x1399: por     %xmm4,%xmm2
    +0x139d: movd    %xmm2,%eax
    +0x13a1: pxor    %xmm1,%xmm3
    +0x13a5: pxor    %xmm0,%xmm3
    +0x13a9: pshufd  $0xee,%xmm3,%xmm0
    +0x13ae: pxor    %xmm3,%xmm0
    +0x13b2: pshufd  $0x55,%xmm0,%xmm1
    +0x13b7: pxor    %xmm0,%xmm1
    +0x13bb: movdqa  %xmm1,%xmm0
    +0x13bf: psrld   $0x10,%xmm0
    +0x13c4: pxor    %xmm1,%xmm0
    +0x13c8: movdqa  %xmm0,%xmm1
    +0x13cc: psrlw   $0x8,%xmm1
    +0x13d1: pxor    %xmm0,%xmm1
    +0x13d5: movd    %xmm1,%ecx
    +0x13d9: movzbl  %al,%eax
    +0x13dc: neg     %rax
    +0x13df: shr     $0x20,%rax
    +0x13e3: xor     %cl,%al
    +0x13e5: xor     %cl,%al
    +0x13e7: mov     0x138(%rsp),%rcx
    +0x13ef: or      0xd4(%rsp),%ecx
    +0x13f6: or      0x130(%rsp),%ecx
    +0x13fd: mov     0x128(%rsp),%rdx
    +0x1405: or      0x120(%rsp),%edx
    +0x140c: or      %r14d,%edx
    +0x140f: or      %ecx,%edx
    +0x1411: or      %r13d,%r12d
    +0x1414: or      %ebx,%r12d
    +0x1417: or      %edx,%r12d
    +0x141a: or      %al,%r12b
    +0x141d: or      %sil,%r12b
    +0x1420: test    %r12b,%r12b
    +0x1423: je      <mldsa87_pk_from_sk+0x143b>
    +0x1425: mov     $0xa20,%edx
    +0x142a: mov     %r15,%rdi
    +0x142d: xor     %esi,%esi
    +0x142f: call    <memset>
    +0x1434: mov     $0xfffffff9,%ebx
    +0x1439: jmp     <mldsa87_pk_from_sk+0x143d>
    +0x143b: xor     %ebx,%ebx
    +0x143d: lea     0x21e0(%rsp),%r14
    +0x1445: mov     $0xd00,%edx
    +0x144a: mov     %r14,%rdi
    +0x144d: xor     %esi,%esi
    +0x144f: call    <memset>
    +0x1454: lea     0x1e0(%rsp),%r14
    +0x145c: mov     $0x400,%edx
    +0x1461: mov     %r14,%rdi
    +0x1464: xor     %esi,%esi
    +0x1466: call    <memset>
    +0x146b: lea     0x5e0(%rsp),%r14
    +0x1473: mov     $0x1c00,%edx
    +0x1478: mov     %r14,%rdi
    +0x147b: xor     %esi,%esi
    +0x147d: call    <memset>
    +0x1482: pxor    %xmm0,%xmm0
    +0x1486: movdqa  %xmm0,0x1d0(%rsp)
    +0x148f: movdqa  %xmm0,0x1c0(%rsp)
    +0x1498: lea     0x1c0(%rsp),%rax
    +0x14a0: movdqa  %xmm0,0x170(%rsp)
    +0x14a9: movdqa  %xmm0,0x160(%rsp)
    +0x14b2: movdqa  %xmm0,0x150(%rsp)
    +0x14bb: movdqa  %xmm0,0x140(%rsp)
    +0x14c4: lea     0x140(%rsp),%rax
    +0x14cc: movdqa  %xmm0,0x1b0(%rsp)
    +0x14d5: movdqa  %xmm0,0x1a0(%rsp)
    +0x14de: movdqa  %xmm0,0x190(%rsp)
    +0x14e7: movdqa  %xmm0,0x180(%rsp)
    +0x14f0: lea     0x180(%rsp),%rax
    +0x14f8: movdqa  %xmm0,0xf0(%rsp)
    +0x1501: movdqa  %xmm0,0xe0(%rsp)
    +0x150a: lea     0xe0(%rsp),%rax
    +0x1512: mov     %ebx,%eax
    +0x1514: lea     -0x28(%rbp),%rsp
    +0x1518: pop     %rbx
    +0x1519: pop     %r12
    +0x151b: pop     %r13
    +0x151d: pop     %r14
    +0x151f: pop     %r15
    +0x1521: pop     %rbp
    +0x1522: xor     %ecx,%ecx
    +0x1524: xor     %edi,%edi
    +0x1526: xor     %edx,%edx
    +0x1528: xor     %esi,%esi
    +0x152a: xor     %r8d,%r8d
    +0x152d: ret     
 ***)

let MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa87_pk_from_sk";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The secret key at sk is the 4896 bytes skb; if it passes the *)
(* checks, mld_pk_from_sk_valid, the public key at pk becomes                *)
(* mld_pk_from_sk_pk and the result is 0, and otherwise the public key is    *)
(* zeroed and the result is MLD_ERR_INVALID_KEY (-7 as a 32-bit integer).    *)
(* The expansion of the matrix from rho is assumed to terminate. The         *)
(* function saves RBP, the frame pointer, and five more registers below the  *)
(* return address, lowers RSP by up to 31 bytes to align it to 32 bytes, and *)
(* then reserves its frame, below which the call of mld_compute_pack_t0_t187 *)
(* uses 4901 bytes, with its return address: 17020 bytes of stack below the  *)
(* return address in all.                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !pk sk skb pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
        nonoverlapping (pk,2592) (word_sub stackpointer (word 17020),17020) /\
        ALLPAIRS nonoverlapping
         [(pk,2592); (word_sub stackpointer (word 17020),17020)]
         [(sk,4896); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        nonoverlapping (pk,2592) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_pk_from_sk) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pk; sk] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  (!j. j < 4896
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           skb j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                  (if mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2 96
                        skb
                   then word 0 else word 4294967289) /\
                  (!j. j < 2592
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           if mld_pk_from_sk_valid 8 7 2
                                mld_polyeta_unpack_2 96 skb
                           then mld_pk_from_sk_pk 7 mld_polyeta_unpack_2 96
                                 skb j
                           else word 0))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,2592);
                memory :> bytes(word_sub stackpointer (word 17020),17020)])`;;

let MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the result of the checks and *)
(* the stack, with all accesses within the arguments, the stack, the return  *)
(* address and the constants of the callees, and the writes within the       *)
(* public key and the stack.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e pk sk skb pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
        nonoverlapping (pk,2592) (word_sub stackpointer (word 17020),17020) /\
        ALLPAIRS nonoverlapping
         [(pk,2592); (word_sub stackpointer (word 17020),17020)]
         [(sk,4896); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        nonoverlapping (pk,2592) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_pk_from_sk) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pk; sk] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  (!j. j < 4896
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           skb j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                  (if mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2 96
                        skb
                   then word 0 else word 4294967289) /\
                  (!j. j < 2592
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           if mld_pk_from_sk_valid 8 7 2
                                mld_polyeta_unpack_2 96 skb
                           then mld_pk_from_sk_pk 7 mld_polyeta_unpack_2 96
                                 skb j
                           else word 0) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events pk sk (mld_sk_rho skb)
                            (mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2
                              96 skb)
                            mf mc pc (word_sub stackpointer (word 17020))
                            returnaddress /\
                     memaccess_inbounds e2
                      [sk,4896; pk,2592;
                       word_sub stackpointer (word 17020),17020;
                       stackpointer,8; word(pc + got_memset),8;
                       word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_ntt_consts),256;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word(pc + mld_compute_pack_t0_t187_consts),64;
                       word(pc + mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32]
                      [pk,2592; word_sub stackpointer (word 17020),17020]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,2592);
                memory :> bytes(word_sub stackpointer (word 17020),17020)])`;;

let MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e pk sk skb pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
        nonoverlapping (pk,2592) (word_sub stackpointer (word 17020),17020) /\
        ALLPAIRS nonoverlapping
         [(pk,2592); (word_sub stackpointer (word 17020),17020)]
         [(sk,4896); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        nonoverlapping (pk,2592) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_pk_from_sk) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pk; sk] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  (!j. j < 4896
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           skb j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events pk sk (mld_sk_rho skb)
                            (mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2
                              96 skb)
                            mf mc pc (word_sub stackpointer (word 17020))
                            returnaddress /\
                     memaccess_inbounds e2
                      [sk,4896; pk,2592;
                       word_sub stackpointer (word 17020),17020;
                       stackpointer,8; word(pc + got_memset),8;
                       word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_ntt_consts),256;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word(pc + mld_compute_pack_t0_t187_consts),64;
                       word(pc + mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32]
                      [pk,2592; word_sub stackpointer (word 17020),17020]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,2592);
                memory :> bytes(word_sub stackpointer (word 17020),17020)])`;;

let MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
