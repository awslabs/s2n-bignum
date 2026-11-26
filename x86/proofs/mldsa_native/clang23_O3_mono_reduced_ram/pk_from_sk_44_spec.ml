(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the statement. This is the code for       *)
(* mldsa44_pk_from_sk (mld_sign_pk_from_sk in sign.c) from mldsa-native's    *)
(* portable C implementation compiled by clang 23 with -O3 and               *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which copies rho, the *)
(* key and tr from the secret key, unpacks s1 and s2 with                    *)
(* mldsa44_polyeta_unpack and checks their norms (s1 with                    *)
(* mldsa44_polyvecl_chknorm, each polynomial of s2 in an inlined loop, in    *)
(* constant time), transforms s1 with calls of mldsa_poly_ntt, recomputes t1 *)
(* into the public key and t0 into a buffer with mld_compute_pack_t0_t144,   *)
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
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/compute_pack_t0_t1_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_pk_from_sk:
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
      +0x20: sub     $0xc80,%rsp
      +0x27: mov     %rsi,%r15
      +0x2a: mov     %rdi,%rbx
      +0x2d: movups  (%rsi),%xmm0
      +0x30: movups  0x10(%rsi),%xmm1
      +0x34: movaps  %xmm1,0x110(%rsp)
      +0x3c: movaps  %xmm0,0x100(%rsp)
      +0x44: movups  0x20(%rsi),%xmm0
      +0x48: movups  0x30(%rsi),%xmm1
      +0x4c: movaps  %xmm0,0x1a0(%rsp)
      +0x54: movaps  %xmm1,0x1b0(%rsp)
      +0x5c: movups  0x40(%rsi),%xmm0
      +0x60: movups  0x50(%rsi),%xmm1
      +0x64: movdqu  0x60(%rsi),%xmm2
      +0x69: movdqu  0x70(%rsi),%xmm3
      +0x6e: movaps  %xmm0,0x160(%rsp)
      +0x76: movaps  %xmm1,0x170(%rsp)
      +0x7e: movdqa  %xmm2,0x180(%rsp)
      +0x87: movdqa  %xmm3,0x190(%rsp)
      +0x90: add     $0x80,%rsi
      +0x97: lea     0xc40(%rsp),%r14
      +0x9f: mov     %r14,%rdi
      +0xa2: call    <mldsa44_polyeta_unpack>
      +0xa7: lea     0x1040(%rsp),%rdi
      +0xaf: lea     0xe0(%r15),%rsi
      +0xb6: call    <mldsa44_polyeta_unpack>
      +0xbb: lea     0x1440(%rsp),%rdi
      +0xc3: lea     0x140(%r15),%rsi
      +0xca: call    <mldsa44_polyeta_unpack>
      +0xcf: lea     0x1840(%rsp),%rdi
      +0xd7: lea     0x1a0(%r15),%rsi
      +0xde: call    <mldsa44_polyeta_unpack>
      +0xe3: mov     %r14,%rdi
      +0xe6: mov     $0x3,%esi
      +0xeb: call    <mldsa44_polyvecl_chknorm>
      +0xf0: mov     %eax,0xf4(%rsp)
      +0xf7: lea     0x200(%r15),%rsi
      +0xfe: lea     0x1c0(%rsp),%rdi
     +0x106: call    <mldsa44_polyeta_unpack>
     +0x10b: xor     %r14d,%r14d
     +0x10e: xor     %eax,%eax
     +0x110: movslq  0x1c0(%rsp,%rax,4),%rcx
     +0x118: mov     %ecx,%edx
     +0x11a: neg     %edx
     +0x11c: mov     %rcx,%rsi
     +0x11f: shr     $0x1f,%rsi
     +0x123: xor     %ecx,%edx
     +0x125: and     %esi,%edx
     +0x127: xor     %ecx,%edx
     +0x129: mov     $0x2,%ecx
     +0x12e: sub     %edx,%ecx
     +0x130: movslq  %ecx,%rcx
     +0x133: shr     $0x1f,%rcx
     +0x137: or      %ecx,%r14d
     +0x13a: inc     %rax
     +0x13d: cmp     $0x100,%rax
     +0x143: jne     <mldsa44_pk_from_sk+0x110>
     +0x145: lea     0x260(%r15),%rsi
     +0x14c: lea     0x1c0(%rsp),%rdi
     +0x154: call    <mldsa44_polyeta_unpack>
     +0x159: xor     %r12d,%r12d
     +0x15c: xor     %eax,%eax
     +0x15e: xchg    %ax,%ax
     +0x160: movslq  0x1c0(%rsp,%rax,4),%rcx
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
     +0x187: or      %ecx,%r12d
     +0x18a: inc     %rax
     +0x18d: cmp     $0x100,%rax
     +0x193: jne     <mldsa44_pk_from_sk+0x160>
     +0x195: mov     %rbx,0xf8(%rsp)
     +0x19d: lea     0x2c0(%r15),%rsi
     +0x1a4: lea     0x1c0(%rsp),%rdi
     +0x1ac: call    <mldsa44_polyeta_unpack>
     +0x1b1: xor     %r13d,%r13d
     +0x1b4: xor     %eax,%eax
     +0x1b6: cs      nopw 0x0(%rax,%rax,1)
     +0x1c0: movslq  0x1c0(%rsp,%rax,4),%rcx
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
     +0x1e7: or      %ecx,%r13d
     +0x1ea: inc     %rax
     +0x1ed: cmp     $0x100,%rax
     +0x1f3: jne     <mldsa44_pk_from_sk+0x1c0>
     +0x1f5: lea     0x320(%r15),%rsi
     +0x1fc: lea     0x1c0(%rsp),%rdi
     +0x204: call    <mldsa44_polyeta_unpack>
     +0x209: xor     %ebx,%ebx
     +0x20b: xor     %eax,%eax
     +0x20d: nopl    (%rax)
     +0x210: movslq  0x1c0(%rsp,%rax,4),%rcx
     +0x218: mov     %ecx,%edx
     +0x21a: neg     %edx
     +0x21c: mov     %rcx,%rsi
     +0x21f: shr     $0x1f,%rsi
     +0x223: xor     %ecx,%edx
     +0x225: and     %esi,%edx
     +0x227: xor     %ecx,%edx
     +0x229: mov     $0x2,%ecx
     +0x22e: sub     %edx,%ecx
     +0x230: movslq  %ecx,%rcx
     +0x233: shr     $0x1f,%rcx
     +0x237: or      %ecx,%ebx
     +0x239: inc     %rax
     +0x23c: cmp     $0x100,%rax
     +0x242: jne     <mldsa44_pk_from_sk+0x210>
     +0x244: lea     0xc40(%rsp),%rdi
     +0x24c: call    <mldsa_poly_ntt>
     +0x251: lea     0x1040(%rsp),%rdi
     +0x259: call    <mldsa_poly_ntt>
     +0x25e: lea     0x1440(%rsp),%rdi
     +0x266: call    <mldsa_poly_ntt>
     +0x26b: lea     0x1840(%rsp),%rdi
     +0x273: call    <mldsa_poly_ntt>
     +0x278: movdqa  0x100(%rsp),%xmm0
     +0x281: movdqa  0x110(%rsp),%xmm1
     +0x28a: mov     0xf8(%rsp),%rax
     +0x292: movdqu  %xmm1,0x10(%rax)
     +0x297: movdqu  %xmm0,(%rax)
     +0x29b: lea     0x20(%rax),%rdi
     +0x29f: lea     0x5c0(%rsp),%rsi
     +0x2a7: lea     0x100(%rsp),%r8
     +0x2af: lea     0xc40(%rsp),%rdx
     +0x2b7: lea     0x200(%r15),%rcx
     +0x2be: call    <mld_compute_pack_t0_t144>
     +0x2c3: pxor    %xmm2,%xmm2
     +0x2c7: xor     %eax,%eax
     +0x2c9: pxor    %xmm3,%xmm3
     +0x2cd: pxor    %xmm1,%xmm1
     +0x2d1: pxor    %xmm0,%xmm0
     +0x2d5: data16  cs nopw 0x0(%rax,%rax,1)
     +0x2e0: movdqu  0x380(%r15,%rax,1),%xmm4
     +0x2ea: movdqu  0x390(%r15,%rax,1),%xmm5
     +0x2f4: movdqa  %xmm2,%xmm6
     +0x2f8: movdqu  0x3a0(%r15,%rax,1),%xmm2
     +0x302: movdqa  %xmm3,%xmm7
     +0x306: movdqu  0x3b0(%r15,%rax,1),%xmm3
     +0x310: pxor    0x5c0(%rsp,%rax,1),%xmm4
     +0x319: pxor    0x5d0(%rsp,%rax,1),%xmm5
     +0x322: por     %xmm4,%xmm1
     +0x326: por     %xmm5,%xmm0
     +0x32a: pxor    %xmm4,%xmm6
     +0x32e: pxor    %xmm5,%xmm7
     +0x332: pxor    0x5e0(%rsp,%rax,1),%xmm2
     +0x33b: pxor    0x5f0(%rsp,%rax,1),%xmm3
     +0x344: por     %xmm2,%xmm1
     +0x348: por     %xmm3,%xmm0
     +0x34c: pxor    %xmm6,%xmm2
     +0x350: pxor    %xmm7,%xmm3
     +0x354: add     $0x40,%rax
     +0x358: cmp     $0x680,%rax
     +0x35e: jne     <mldsa44_pk_from_sk+0x2e0>
     +0x360: pxor    %xmm2,%xmm3
     +0x364: pshufd  $0xee,%xmm3,%xmm2
     +0x369: pxor    %xmm3,%xmm2
     +0x36d: pshufd  $0x55,%xmm2,%xmm3
     +0x372: pxor    %xmm2,%xmm3
     +0x376: movdqa  %xmm3,%xmm2
     +0x37a: psrld   $0x10,%xmm2
     +0x37f: pxor    %xmm3,%xmm2
     +0x383: movdqa  %xmm2,%xmm3
     +0x387: psrlw   $0x8,%xmm3
     +0x38c: pxor    %xmm2,%xmm3
     +0x390: movd    %xmm3,%ecx
     +0x394: mov     %ecx,0xf0(%rsp)
     +0x39b: por     %xmm1,%xmm0
     +0x39f: pshufd  $0xee,%xmm0,%xmm1
     +0x3a4: por     %xmm0,%xmm1
     +0x3a8: pshufd  $0x55,%xmm1,%xmm0
     +0x3ad: por     %xmm1,%xmm0
     +0x3b1: movdqa  %xmm0,%xmm1
     +0x3b5: psrld   $0x10,%xmm1
     +0x3ba: por     %xmm0,%xmm1
     +0x3be: movdqa  %xmm1,%xmm0
     +0x3c2: psrlw   $0x8,%xmm0
     +0x3c7: por     %xmm1,%xmm0
     +0x3cb: movd    %xmm0,%eax
     +0x3cf: movzbl  %al,%eax
     +0x3d2: neg     %rax
     +0x3d5: shr     $0x20,%rax
     +0x3d9: xor     %cl,%al
     +0x3db: mov     %rax,0xe8(%rsp)
     +0x3e3: pxor    %xmm0,%xmm0
     +0x3e7: movdqu  %xmm0,0xcc(%rsp)
     +0x3f0: movdqa  %xmm0,0xc0(%rsp)
     +0x3f9: movdqa  %xmm0,0xb0(%rsp)
     +0x402: movdqa  %xmm0,0xa0(%rsp)
     +0x40b: movdqa  %xmm0,0x90(%rsp)
     +0x414: movdqa  %xmm0,0x80(%rsp)
     +0x41d: movdqa  %xmm0,0x70(%rsp)
     +0x423: movdqa  %xmm0,0x60(%rsp)
     +0x429: movdqa  %xmm0,0x50(%rsp)
     +0x42f: movdqa  %xmm0,0x40(%rsp)
     +0x435: movdqa  %xmm0,0x30(%rsp)
     +0x43b: movdqa  %xmm0,0x20(%rsp)
     +0x441: movdqa  %xmm0,0x10(%rsp)
     +0x447: mov     0xf8(%rsp),%r15
     +0x44f: movups  (%r15),%xmm0
     +0x453: movups  0x10(%r15),%xmm1
     +0x458: movaps  %xmm0,0x10(%rsp)
     +0x45d: movaps  %xmm1,0x20(%rsp)
     +0x462: movups  0x20(%r15),%xmm0
     +0x467: movups  0x30(%r15),%xmm1
     +0x46c: movaps  %xmm0,0x30(%rsp)
     +0x471: movaps  %xmm1,0x40(%rsp)
     +0x476: movups  0x40(%r15),%xmm0
     +0x47b: movups  0x50(%r15),%xmm1
     +0x480: xorps   0x50(%rsp),%xmm0
     +0x485: xorps   0x60(%rsp),%xmm1
     +0x48a: movaps  %xmm0,0x50(%rsp)
     +0x48f: movaps  %xmm1,0x60(%rsp)
     +0x494: movups  0x60(%r15),%xmm0
     +0x499: movups  0x70(%r15),%xmm1
     +0x49e: xorps   0x70(%rsp),%xmm0
     +0x4a3: xorps   0x80(%rsp),%xmm1
     +0x4ab: movaps  %xmm0,0x70(%rsp)
     +0x4b0: movaps  %xmm1,0x80(%rsp)
     +0x4b8: mov     0x80(%r15),%rax
     +0x4bf: xor     %rax,0x90(%rsp)
     +0x4c7: lea     0x10(%rsp),%rdi
     +0x4cc: call    <mldsa_keccakf1600_permute>
     +0x4d1: movups  0x88(%r15),%xmm0
     +0x4d9: movups  0x98(%r15),%xmm1
     +0x4e1: xorps   0x10(%rsp),%xmm0
     +0x4e6: xorps   0x20(%rsp),%xmm1
     +0x4eb: movaps  %xmm0,0x10(%rsp)
     +0x4f0: movaps  %xmm1,0x20(%rsp)
     +0x4f5: movups  0xa8(%r15),%xmm0
     +0x4fd: movups  0xb8(%r15),%xmm1
     +0x505: xorps   0x30(%rsp),%xmm0
     +0x50a: xorps   0x40(%rsp),%xmm1
     +0x50f: movaps  %xmm0,0x30(%rsp)
     +0x514: movaps  %xmm1,0x40(%rsp)
     +0x519: movups  0xc8(%r15),%xmm0
     +0x521: movups  0xd8(%r15),%xmm1
     +0x529: xorps   0x50(%rsp),%xmm0
     +0x52e: xorps   0x60(%rsp),%xmm1
     +0x533: movaps  %xmm0,0x50(%rsp)
     +0x538: movaps  %xmm1,0x60(%rsp)
     +0x53d: movups  0xe8(%r15),%xmm0
     +0x545: movups  0xf8(%r15),%xmm1
     +0x54d: xorps   0x70(%rsp),%xmm0
     +0x552: xorps   0x80(%rsp),%xmm1
     +0x55a: movaps  %xmm0,0x70(%rsp)
     +0x55f: movaps  %xmm1,0x80(%rsp)
     +0x567: mov     0x108(%r15),%rax
     +0x56e: xor     %rax,0x90(%rsp)
     +0x576: lea     0x10(%rsp),%rdi
     +0x57b: call    <mldsa_keccakf1600_permute>
     +0x580: movups  0x110(%r15),%xmm0
     +0x588: movups  0x120(%r15),%xmm1
     +0x590: xorps   0x10(%rsp),%xmm0
     +0x595: xorps   0x20(%rsp),%xmm1
     +0x59a: movaps  %xmm0,0x10(%rsp)
     +0x59f: movaps  %xmm1,0x20(%rsp)
     +0x5a4: movups  0x130(%r15),%xmm0
     +0x5ac: movups  0x140(%r15),%xmm1
     +0x5b4: xorps   0x30(%rsp),%xmm0
     +0x5b9: xorps   0x40(%rsp),%xmm1
     +0x5be: movaps  %xmm0,0x30(%rsp)
     +0x5c3: movaps  %xmm1,0x40(%rsp)
     +0x5c8: movups  0x150(%r15),%xmm0
     +0x5d0: movups  0x160(%r15),%xmm1
     +0x5d8: xorps   0x50(%rsp),%xmm0
     +0x5dd: xorps   0x60(%rsp),%xmm1
     +0x5e2: movaps  %xmm0,0x50(%rsp)
     +0x5e7: movaps  %xmm1,0x60(%rsp)
     +0x5ec: movups  0x170(%r15),%xmm0
     +0x5f4: movups  0x180(%r15),%xmm1
     +0x5fc: xorps   0x70(%rsp),%xmm0
     +0x601: xorps   0x80(%rsp),%xmm1
     +0x609: movaps  %xmm0,0x70(%rsp)
     +0x60e: movaps  %xmm1,0x80(%rsp)
     +0x616: mov     0x190(%r15),%rax
     +0x61d: xor     %rax,0x90(%rsp)
     +0x625: lea     0x10(%rsp),%rdi
     +0x62a: call    <mldsa_keccakf1600_permute>
     +0x62f: movups  0x198(%r15),%xmm0
     +0x637: movups  0x1a8(%r15),%xmm1
     +0x63f: xorps   0x10(%rsp),%xmm0
     +0x644: xorps   0x20(%rsp),%xmm1
     +0x649: movaps  %xmm0,0x10(%rsp)
     +0x64e: movaps  %xmm1,0x20(%rsp)
     +0x653: movups  0x1b8(%r15),%xmm0
     +0x65b: movups  0x1c8(%r15),%xmm1
     +0x663: xorps   0x30(%rsp),%xmm0
     +0x668: xorps   0x40(%rsp),%xmm1
     +0x66d: movaps  %xmm0,0x30(%rsp)
     +0x672: movaps  %xmm1,0x40(%rsp)
     +0x677: movups  0x1d8(%r15),%xmm0
     +0x67f: movups  0x1e8(%r15),%xmm1
     +0x687: xorps   0x50(%rsp),%xmm0
     +0x68c: xorps   0x60(%rsp),%xmm1
     +0x691: movaps  %xmm0,0x50(%rsp)
     +0x696: movaps  %xmm1,0x60(%rsp)
     +0x69b: movups  0x1f8(%r15),%xmm0
     +0x6a3: movups  0x208(%r15),%xmm1
     +0x6ab: xorps   0x70(%rsp),%xmm0
     +0x6b0: xorps   0x80(%rsp),%xmm1
     +0x6b8: movaps  %xmm0,0x70(%rsp)
     +0x6bd: movaps  %xmm1,0x80(%rsp)
     +0x6c5: mov     0x218(%r15),%rax
     +0x6cc: xor     %rax,0x90(%rsp)
     +0x6d4: lea     0x10(%rsp),%rdi
     +0x6d9: call    <mldsa_keccakf1600_permute>
     +0x6de: movups  0x220(%r15),%xmm0
     +0x6e6: movups  0x230(%r15),%xmm1
     +0x6ee: xorps   0x10(%rsp),%xmm0
     +0x6f3: xorps   0x20(%rsp),%xmm1
     +0x6f8: movaps  %xmm0,0x10(%rsp)
     +0x6fd: movaps  %xmm1,0x20(%rsp)
     +0x702: movups  0x240(%r15),%xmm0
     +0x70a: movups  0x250(%r15),%xmm1
     +0x712: xorps   0x30(%rsp),%xmm0
     +0x717: xorps   0x40(%rsp),%xmm1
     +0x71c: movaps  %xmm0,0x30(%rsp)
     +0x721: movaps  %xmm1,0x40(%rsp)
     +0x726: movups  0x260(%r15),%xmm0
     +0x72e: movups  0x270(%r15),%xmm1
     +0x736: xorps   0x50(%rsp),%xmm0
     +0x73b: xorps   0x60(%rsp),%xmm1
     +0x740: movaps  %xmm0,0x50(%rsp)
     +0x745: movaps  %xmm1,0x60(%rsp)
     +0x74a: movups  0x280(%r15),%xmm0
     +0x752: movups  0x290(%r15),%xmm1
     +0x75a: xorps   0x70(%rsp),%xmm0
     +0x75f: xorps   0x80(%rsp),%xmm1
     +0x767: movaps  %xmm0,0x70(%rsp)
     +0x76c: movaps  %xmm1,0x80(%rsp)
     +0x774: mov     0x2a0(%r15),%rax
     +0x77b: xor     %rax,0x90(%rsp)
     +0x783: lea     0x10(%rsp),%rdi
     +0x788: call    <mldsa_keccakf1600_permute>
     +0x78d: movups  0x2a8(%r15),%xmm0
     +0x795: movups  0x2b8(%r15),%xmm1
     +0x79d: xorps   0x10(%rsp),%xmm0
     +0x7a2: xorps   0x20(%rsp),%xmm1
     +0x7a7: movaps  %xmm0,0x10(%rsp)
     +0x7ac: movaps  %xmm1,0x20(%rsp)
     +0x7b1: movups  0x2c8(%r15),%xmm0
     +0x7b9: movups  0x2d8(%r15),%xmm1
     +0x7c1: xorps   0x30(%rsp),%xmm0
     +0x7c6: xorps   0x40(%rsp),%xmm1
     +0x7cb: movaps  %xmm0,0x30(%rsp)
     +0x7d0: movaps  %xmm1,0x40(%rsp)
     +0x7d5: movups  0x2e8(%r15),%xmm0
     +0x7dd: movups  0x2f8(%r15),%xmm1
     +0x7e5: xorps   0x50(%rsp),%xmm0
     +0x7ea: xorps   0x60(%rsp),%xmm1
     +0x7ef: movaps  %xmm0,0x50(%rsp)
     +0x7f4: movaps  %xmm1,0x60(%rsp)
     +0x7f9: movups  0x308(%r15),%xmm0
     +0x801: movups  0x318(%r15),%xmm1
     +0x809: xorps   0x70(%rsp),%xmm0
     +0x80e: xorps   0x80(%rsp),%xmm1
     +0x816: movaps  %xmm0,0x70(%rsp)
     +0x81b: movaps  %xmm1,0x80(%rsp)
     +0x823: mov     0x328(%r15),%rax
     +0x82a: xor     %rax,0x90(%rsp)
     +0x832: lea     0x10(%rsp),%rdi
     +0x837: call    <mldsa_keccakf1600_permute>
     +0x83c: movups  0x330(%r15),%xmm0
     +0x844: movups  0x340(%r15),%xmm1
     +0x84c: xorps   0x10(%rsp),%xmm0
     +0x851: xorps   0x20(%rsp),%xmm1
     +0x856: movaps  %xmm0,0x10(%rsp)
     +0x85b: movaps  %xmm1,0x20(%rsp)
     +0x860: movups  0x350(%r15),%xmm0
     +0x868: movups  0x360(%r15),%xmm1
     +0x870: xorps   0x30(%rsp),%xmm0
     +0x875: xorps   0x40(%rsp),%xmm1
     +0x87a: movaps  %xmm0,0x30(%rsp)
     +0x87f: movaps  %xmm1,0x40(%rsp)
     +0x884: movups  0x370(%r15),%xmm0
     +0x88c: movups  0x380(%r15),%xmm1
     +0x894: xorps   0x50(%rsp),%xmm0
     +0x899: xorps   0x60(%rsp),%xmm1
     +0x89e: movaps  %xmm0,0x50(%rsp)
     +0x8a3: movaps  %xmm1,0x60(%rsp)
     +0x8a8: movups  0x390(%r15),%xmm0
     +0x8b0: movups  0x3a0(%r15),%xmm1
     +0x8b8: xorps   0x70(%rsp),%xmm0
     +0x8bd: xorps   0x80(%rsp),%xmm1
     +0x8c5: movaps  %xmm0,0x70(%rsp)
     +0x8ca: movaps  %xmm1,0x80(%rsp)
     +0x8d2: mov     0x3b0(%r15),%rax
     +0x8d9: xor     %rax,0x90(%rsp)
     +0x8e1: lea     0x10(%rsp),%rdi
     +0x8e6: call    <mldsa_keccakf1600_permute>
     +0x8eb: movups  0x3b8(%r15),%xmm0
     +0x8f3: movups  0x3c8(%r15),%xmm1
     +0x8fb: xorps   0x10(%rsp),%xmm0
     +0x900: xorps   0x20(%rsp),%xmm1
     +0x905: movaps  %xmm0,0x10(%rsp)
     +0x90a: movaps  %xmm1,0x20(%rsp)
     +0x90f: movups  0x3d8(%r15),%xmm0
     +0x917: movups  0x3e8(%r15),%xmm1
     +0x91f: xorps   0x30(%rsp),%xmm0
     +0x924: xorps   0x40(%rsp),%xmm1
     +0x929: movaps  %xmm0,0x30(%rsp)
     +0x92e: movaps  %xmm1,0x40(%rsp)
     +0x933: movups  0x3f8(%r15),%xmm0
     +0x93b: movups  0x408(%r15),%xmm1
     +0x943: xorps   0x50(%rsp),%xmm0
     +0x948: xorps   0x60(%rsp),%xmm1
     +0x94d: movaps  %xmm0,0x50(%rsp)
     +0x952: movaps  %xmm1,0x60(%rsp)
     +0x957: movups  0x418(%r15),%xmm0
     +0x95f: movups  0x428(%r15),%xmm1
     +0x967: xorps   0x70(%rsp),%xmm0
     +0x96c: xorps   0x80(%rsp),%xmm1
     +0x974: movaps  %xmm0,0x70(%rsp)
     +0x979: movaps  %xmm1,0x80(%rsp)
     +0x981: mov     0x438(%r15),%rax
     +0x988: xor     %rax,0x90(%rsp)
     +0x990: lea     0x10(%rsp),%rdi
     +0x995: call    <mldsa_keccakf1600_permute>
     +0x99a: movups  0x440(%r15),%xmm0
     +0x9a2: movups  0x450(%r15),%xmm1
     +0x9aa: xorps   0x10(%rsp),%xmm0
     +0x9af: xorps   0x20(%rsp),%xmm1
     +0x9b4: movaps  %xmm0,0x10(%rsp)
     +0x9b9: movaps  %xmm1,0x20(%rsp)
     +0x9be: movups  0x460(%r15),%xmm0
     +0x9c6: movups  0x470(%r15),%xmm1
     +0x9ce: xorps   0x30(%rsp),%xmm0
     +0x9d3: xorps   0x40(%rsp),%xmm1
     +0x9d8: movaps  %xmm0,0x30(%rsp)
     +0x9dd: movaps  %xmm1,0x40(%rsp)
     +0x9e2: movups  0x480(%r15),%xmm0
     +0x9ea: movups  0x490(%r15),%xmm1
     +0x9f2: xorps   0x50(%rsp),%xmm0
     +0x9f7: xorps   0x60(%rsp),%xmm1
     +0x9fc: movaps  %xmm0,0x50(%rsp)
     +0xa01: movaps  %xmm1,0x60(%rsp)
     +0xa06: movups  0x4a0(%r15),%xmm0
     +0xa0e: movups  0x4b0(%r15),%xmm1
     +0xa16: xorps   0x70(%rsp),%xmm0
     +0xa1b: xorps   0x80(%rsp),%xmm1
     +0xa23: movaps  %xmm0,0x70(%rsp)
     +0xa28: movaps  %xmm1,0x80(%rsp)
     +0xa30: mov     0x4c0(%r15),%rax
     +0xa37: xor     %rax,0x90(%rsp)
     +0xa3f: lea     0x10(%rsp),%rdi
     +0xa44: call    <mldsa_keccakf1600_permute>
     +0xa49: mov     0x4c8(%r15),%rax
     +0xa50: mov     0x4d0(%r15),%rcx
     +0xa57: xor     %rax,0x10(%rsp)
     +0xa5c: xor     %rcx,0x18(%rsp)
     +0xa61: mov     0x4d8(%r15),%rax
     +0xa68: mov     0x4e0(%r15),%rcx
     +0xa6f: xor     %rax,0x20(%rsp)
     +0xa74: xor     %rcx,0x28(%rsp)
     +0xa79: mov     0x4e8(%r15),%rax
     +0xa80: mov     0x4f0(%r15),%rcx
     +0xa87: xor     %rax,0x30(%rsp)
     +0xa8c: xor     %rcx,0x38(%rsp)
     +0xa91: mov     0x4f8(%r15),%rax
     +0xa98: mov     0x500(%r15),%rcx
     +0xa9f: xor     %rax,0x40(%rsp)
     +0xaa4: xor     %rcx,0x48(%rsp)
     +0xaa9: mov     0x508(%r15),%rax
     +0xab0: mov     0x510(%r15),%rcx
     +0xab7: xor     %rax,0x50(%rsp)
     +0xabc: xor     %rcx,0x58(%rsp)
     +0xac1: mov     0x518(%r15),%rax
     +0xac8: xor     %rax,0x60(%rsp)
     +0xacd: mov     0xe8(%rsp),%rax
     +0xad5: xor     0xf0(%rsp),%al
     +0xadc: mov     %rax,0xe8(%rsp)
     +0xae4: xorb    $0x1f,0x68(%rsp)
     +0xae9: xorb    $0x80,0x97(%rsp)
     +0xaf1: movl    $0x88,0xd8(%rsp)
     +0xafc: lea     0x10(%rsp),%rdi
     +0xb01: call    <mldsa_keccakf1600_permute>
     +0xb06: movaps  0x10(%rsp),%xmm0
     +0xb0b: movaps  0x20(%rsp),%xmm1
     +0xb10: movaps  0x30(%rsp),%xmm2
     +0xb15: movaps  0x40(%rsp),%xmm3
     +0xb1a: movaps  %xmm3,0x150(%rsp)
     +0xb22: movaps  %xmm2,0x140(%rsp)
     +0xb2a: movaps  %xmm1,0x130(%rsp)
     +0xb32: movaps  %xmm0,0x120(%rsp)
     +0xb3a: xorps   %xmm0,%xmm0
     +0xb3d: movaps  %xmm0,0x50(%rsp)
     +0xb42: movaps  %xmm0,0x60(%rsp)
     +0xb47: movaps  %xmm0,0x70(%rsp)
     +0xb4c: movaps  %xmm0,0x80(%rsp)
     +0xb54: movaps  %xmm0,0x90(%rsp)
     +0xb5c: movaps  %xmm0,0xa0(%rsp)
     +0xb64: movaps  %xmm0,0xb0(%rsp)
     +0xb6c: movaps  %xmm0,0xc0(%rsp)
     +0xb74: movaps  %xmm0,0xd0(%rsp)
     +0xb7c: movaps  %xmm0,0x10(%rsp)
     +0xb81: movaps  %xmm0,0x20(%rsp)
     +0xb86: movaps  %xmm0,0x30(%rsp)
     +0xb8b: movaps  %xmm0,0x40(%rsp)
     +0xb90: lea     0x10(%rsp),%rax
     +0xb95: movdqa  0x120(%rsp),%xmm2
     +0xb9e: movdqa  0x130(%rsp),%xmm1
     +0xba7: movdqa  0x140(%rsp),%xmm0
     +0xbb0: pxor    0x160(%rsp),%xmm2
     +0xbb9: pxor    0x170(%rsp),%xmm1
     +0xbc2: pxor    0x180(%rsp),%xmm0
     +0xbcb: movdqa  0x150(%rsp),%xmm3
     +0xbd4: pxor    0x190(%rsp),%xmm3
     +0xbdd: movdqa  %xmm0,%xmm4
     +0xbe1: por     %xmm2,%xmm4
     +0xbe5: pxor    %xmm2,%xmm0
     +0xbe9: movdqa  %xmm1,%xmm2
     +0xbed: por     %xmm3,%xmm2
     +0xbf1: por     %xmm4,%xmm2
     +0xbf5: pshufd  $0xee,%xmm2,%xmm4
     +0xbfa: por     %xmm2,%xmm4
     +0xbfe: pshufd  $0x55,%xmm4,%xmm2
     +0xc03: por     %xmm4,%xmm2
     +0xc07: movdqa  %xmm2,%xmm4
     +0xc0b: psrld   $0x10,%xmm4
     +0xc10: por     %xmm2,%xmm4
     +0xc14: movdqa  %xmm4,%xmm2
     +0xc18: psrlw   $0x8,%xmm2
     +0xc1d: por     %xmm4,%xmm2
     +0xc21: movd    %xmm2,%eax
     +0xc25: pxor    %xmm1,%xmm3
     +0xc29: pxor    %xmm0,%xmm3
     +0xc2d: pshufd  $0xee,%xmm3,%xmm0
     +0xc32: pxor    %xmm3,%xmm0
     +0xc36: pshufd  $0x55,%xmm0,%xmm1
     +0xc3b: pxor    %xmm0,%xmm1
     +0xc3f: movdqa  %xmm1,%xmm0
     +0xc43: psrld   $0x10,%xmm0
     +0xc48: pxor    %xmm1,%xmm0
     +0xc4c: movdqa  %xmm0,%xmm1
     +0xc50: psrlw   $0x8,%xmm1
     +0xc55: pxor    %xmm0,%xmm1
     +0xc59: movd    %xmm1,%ecx
     +0xc5d: movzbl  %al,%eax
     +0xc60: neg     %rax
     +0xc63: shr     $0x20,%rax
     +0xc67: xor     %cl,%al
     +0xc69: xor     %cl,%al
     +0xc6b: or      0xf4(%rsp),%r14d
     +0xc73: or      %r12d,%r14d
     +0xc76: or      %ebx,%r13d
     +0xc79: or      %r14d,%r13d
     +0xc7c: or      %al,%r13b
     +0xc7f: or      0xe8(%rsp),%r13b
     +0xc87: test    %r13b,%r13b
     +0xc8a: je      <mldsa44_pk_from_sk+0xca2>
     +0xc8c: mov     $0x520,%edx
     +0xc91: mov     %r15,%rdi
     +0xc94: xor     %esi,%esi
     +0xc96: call    <memset>
     +0xc9b: mov     $0xfffffff9,%ebx
     +0xca0: jmp     <mldsa44_pk_from_sk+0xca4>
     +0xca2: xor     %ebx,%ebx
     +0xca4: lea     0x5c0(%rsp),%r14
     +0xcac: mov     $0x680,%edx
     +0xcb1: mov     %r14,%rdi
     +0xcb4: xor     %esi,%esi
     +0xcb6: call    <memset>
     +0xcbb: lea     0x1c0(%rsp),%r14
     +0xcc3: mov     $0x400,%edx
     +0xcc8: mov     %r14,%rdi
     +0xccb: xor     %esi,%esi
     +0xccd: call    <memset>
     +0xcd2: lea     0xc40(%rsp),%r14
     +0xcda: mov     $0x1000,%edx
     +0xcdf: mov     %r14,%rdi
     +0xce2: xor     %esi,%esi
     +0xce4: call    <memset>
     +0xce9: pxor    %xmm0,%xmm0
     +0xced: movdqa  %xmm0,0x1b0(%rsp)
     +0xcf6: movdqa  %xmm0,0x1a0(%rsp)
     +0xcff: lea     0x1a0(%rsp),%rax
     +0xd07: movdqa  %xmm0,0x150(%rsp)
     +0xd10: movdqa  %xmm0,0x140(%rsp)
     +0xd19: movdqa  %xmm0,0x130(%rsp)
     +0xd22: movdqa  %xmm0,0x120(%rsp)
     +0xd2b: lea     0x120(%rsp),%rax
     +0xd33: movdqa  %xmm0,0x190(%rsp)
     +0xd3c: movdqa  %xmm0,0x180(%rsp)
     +0xd45: movdqa  %xmm0,0x170(%rsp)
     +0xd4e: movdqa  %xmm0,0x160(%rsp)
     +0xd57: lea     0x160(%rsp),%rax
     +0xd5f: movdqa  %xmm0,0x110(%rsp)
     +0xd68: movdqa  %xmm0,0x100(%rsp)
     +0xd71: lea     0x100(%rsp),%rax
     +0xd79: mov     %ebx,%eax
     +0xd7b: lea     -0x28(%rbp),%rsp
     +0xd7f: pop     %rbx
     +0xd80: pop     %r12
     +0xd82: pop     %r13
     +0xd84: pop     %r14
     +0xd86: pop     %r15
     +0xd88: pop     %rbp
     +0xd89: xor     %ecx,%ecx
     +0xd8b: xor     %edi,%edi
     +0xd8d: xor     %edx,%edx
     +0xd8f: xor     %esi,%esi
     +0xd91: xor     %r8d,%r8d
     +0xd94: ret     
 ***)

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_pk_from_sk";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The secret key at sk is the 2560 bytes skb; if it passes the *)
(* checks, mld_pk_from_sk_valid, the public key at pk becomes                *)
(* mld_pk_from_sk_pk and the result is 0, and otherwise the public key is    *)
(* zeroed and the result is MLD_ERR_INVALID_KEY (-7 as a 32-bit integer).    *)
(* The expansion of the matrix from rho is assumed to terminate. The         *)
(* function saves RBP, the frame pointer, and five more registers below the  *)
(* return address, lowers RSP by up to 31 bytes to align it to 32 bytes, and *)
(* then reserves its frame, below which the call of mld_compute_pack_t0_t144 *)
(* uses 4901 bytes, with its return address: 12252 bytes of stack below the  *)
(* return address in all.                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !pk sk skb pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
        nonoverlapping (pk,1312) (word_sub stackpointer (word 12252),12252) /\
        ALLPAIRS nonoverlapping
         [(pk,1312); (word_sub stackpointer (word 12252),12252)]
         [(sk,2560); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        nonoverlapping (pk,1312) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa44_pk_from_sk) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pk; sk] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  (!j. j < 2560
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           skb j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                  (if mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2 96
                        skb
                   then word 0 else word 4294967289) /\
                  (!j. j < 1312
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           if mld_pk_from_sk_valid 4 4 2
                                mld_polyeta_unpack_2 96 skb
                           then mld_pk_from_sk_pk 4 mld_polyeta_unpack_2 96
                                 skb j
                           else word 0))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,1312);
                memory :> bytes(word_sub stackpointer (word 12252),12252)])`;;

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the result of the checks and *)
(* the stack, with all accesses within the arguments, the stack, the return  *)
(* address and the constants of the callees, and the writes within the       *)
(* public key and the stack.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e pk sk skb pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
        nonoverlapping (pk,1312) (word_sub stackpointer (word 12252),12252) /\
        ALLPAIRS nonoverlapping
         [(pk,1312); (word_sub stackpointer (word 12252),12252)]
         [(sk,2560); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        nonoverlapping (pk,1312) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa44_pk_from_sk) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pk; sk] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  (!j. j < 2560
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           skb j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                  (if mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2 96
                        skb
                   then word 0 else word 4294967289) /\
                  (!j. j < 1312
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           if mld_pk_from_sk_valid 4 4 2
                                mld_polyeta_unpack_2 96 skb
                           then mld_pk_from_sk_pk 4 mld_polyeta_unpack_2 96
                                 skb j
                           else word 0) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events pk sk (mld_sk_rho skb)
                            (mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2
                              96 skb)
                            mf mc pc (word_sub stackpointer (word 12252))
                            returnaddress /\
                     memaccess_inbounds e2
                      [sk,2560; pk,1312;
                       word_sub stackpointer (word 12252),12252;
                       stackpointer,8; word(pc + got_memset),8;
                       word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_ntt_consts),256;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word(pc + mld_compute_pack_t0_t144_consts),64;
                       word(pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32]
                      [pk,1312; word_sub stackpointer (word 12252),12252]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,1312);
                memory :> bytes(word_sub stackpointer (word 12252),12252)])`;;

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e pk sk skb pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
        nonoverlapping (pk,1312) (word_sub stackpointer (word 12252),12252) /\
        ALLPAIRS nonoverlapping
         [(pk,1312); (word_sub stackpointer (word 12252),12252)]
         [(sk,2560); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        nonoverlapping (pk,1312) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa44_pk_from_sk) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pk; sk] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  (!j. j < 2560
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           skb j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events pk sk (mld_sk_rho skb)
                            (mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2
                              96 skb)
                            mf mc pc (word_sub stackpointer (word 12252))
                            returnaddress /\
                     memaccess_inbounds e2
                      [sk,2560; pk,1312;
                       word_sub stackpointer (word 12252),12252;
                       stackpointer,8; word(pc + got_memset),8;
                       word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_ntt_consts),256;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word(pc + mld_compute_pack_t0_t144_consts),64;
                       word(pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32]
                      [pk,1312; word_sub stackpointer (word 12252),12252]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,1312);
                memory :> bytes(word_sub stackpointer (word 12252),12252)])`;;

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
