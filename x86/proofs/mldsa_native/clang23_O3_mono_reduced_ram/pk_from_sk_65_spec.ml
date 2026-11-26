(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the statement. This is the code for       *)
(* mldsa65_pk_from_sk (mld_sign_pk_from_sk in sign.c) from mldsa-native's    *)
(* portable C implementation compiled by clang 23 with -O3 and               *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which copies rho, the *)
(* key and tr from the secret key, unpacks s1 and s2 (inlined loops for eta  *)
(* = 4) and checks their norms (s1 with mldsa65_polyvecl_chknorm, each       *)
(* polynomial of s2 in an inlined loop, in constant time), transforms s1     *)
(* with calls of mldsa_poly_ntt, recomputes t1 into the public key and t0    *)
(* into a buffer with mld_compute_pack_t0_t165, compares t0 with that in the *)
(* secret key, hashes the public key with an inlined SHAKE256 and compares   *)
(* the hash with tr, all in constant time, and then zeroes the public key if *)
(* a check failed, and its buffers, with memset, which it calls through the  *)
(* PLT, so that the direction flag must be clear, as the ABI requires on     *)
(* entry. It is verified in the whole image (see libmldsa.ml) against        *)
(* mld_pk_from_sk_pk and mld_pk_from_sk_valid of                             *)
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
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/compute_pack_t0_t1_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa65_pk_from_sk:
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
      +0x2f: sub     $0x3c0,%rsp
      +0x36: mov     %rsi,%r15
      +0x39: mov     %rdi,%rbx
      +0x3c: movups  (%rsi),%xmm0
      +0x3f: movups  0x10(%rsi),%xmm1
      +0x43: movaps  %xmm1,0xf0(%rsp)
      +0x4b: movaps  %xmm0,0xe0(%rsp)
      +0x53: movups  0x20(%rsi),%xmm0
      +0x57: movups  0x30(%rsi),%xmm1
      +0x5b: movaps  %xmm0,0x1a0(%rsp)
      +0x63: movaps  %xmm1,0x1b0(%rsp)
      +0x6b: movdqu  0x40(%rsi),%xmm0
      +0x70: movdqu  0x50(%rsi),%xmm1
      +0x75: movdqu  0x60(%rsi),%xmm2
      +0x7a: movdqu  0x70(%rsi),%xmm3
      +0x7f: movdqa  %xmm0,0x160(%rsp)
      +0x88: movdqa  %xmm1,0x170(%rsp)
      +0x91: movdqa  %xmm2,0x180(%rsp)
      +0x9a: movdqa  %xmm3,0x190(%rsp)
      +0xa3: xor     %eax,%eax
      +0xa5: movdqa  0x10653(%rip),%xmm5
      +0xad: pxor    %xmm0,%xmm0
      +0xb1: movdqa  0x10657(%rip),%xmm6
      +0xb9: nopl    0x0(%rax)
      +0xc0: movzwl  0x80(%r15,%rax,1),%ecx
      +0xc9: movd    %ecx,%xmm1
      +0xcd: movzwl  0x82(%r15,%rax,1),%ecx
      +0xd6: movd    %ecx,%xmm2
      +0xda: movdqa  %xmm1,%xmm3
      +0xde: psrlw   $0x4,%xmm3
      +0xe3: movdqa  %xmm2,%xmm4
      +0xe7: psrlw   $0x4,%xmm4
      +0xec: punpcklbw %xmm3,%xmm1
      +0xf0: pand    %xmm5,%xmm1
      +0xf4: punpcklbw %xmm0,%xmm1
      +0xf8: punpcklwd %xmm0,%xmm1
      +0xfc: movdqa  %xmm6,%xmm3
     +0x100: psubd   %xmm1,%xmm3
     +0x104: movdqa  %xmm3,0x5c0(%rsp,%rax,8)
     +0x10d: punpcklbw %xmm4,%xmm2
     +0x111: pand    %xmm5,%xmm2
     +0x115: punpcklbw %xmm0,%xmm2
     +0x119: punpcklwd %xmm0,%xmm2
     +0x11d: movdqa  %xmm6,%xmm1
     +0x121: psubd   %xmm2,%xmm1
     +0x125: movdqa  %xmm1,0x5d0(%rsp,%rax,8)
     +0x12e: add     $0x4,%rax
     +0x132: cmp     $0x80,%rax
     +0x138: jne     <mldsa65_pk_from_sk+0xc0>
     +0x13a: mov     $0x80,%eax
     +0x13f: pxor    %xmm0,%xmm0
     +0x143: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x150: movzwl  0x80(%r15,%rax,1),%ecx
     +0x159: movd    %ecx,%xmm1
     +0x15d: movzwl  0x82(%r15,%rax,1),%ecx
     +0x166: movd    %ecx,%xmm2
     +0x16a: movdqa  %xmm1,%xmm3
     +0x16e: psrlw   $0x4,%xmm3
     +0x173: movdqa  %xmm2,%xmm4
     +0x177: psrlw   $0x4,%xmm4
     +0x17c: punpcklbw %xmm3,%xmm1
     +0x180: pand    %xmm5,%xmm1
     +0x184: punpcklbw %xmm0,%xmm1
     +0x188: punpcklwd %xmm0,%xmm1
     +0x18c: movdqa  %xmm6,%xmm3
     +0x190: psubd   %xmm1,%xmm3
     +0x194: movdqa  %xmm3,0x5c0(%rsp,%rax,8)
     +0x19d: punpcklbw %xmm4,%xmm2
     +0x1a1: pand    %xmm5,%xmm2
     +0x1a5: punpcklbw %xmm0,%xmm2
     +0x1a9: punpcklwd %xmm0,%xmm2
     +0x1ad: movdqa  %xmm6,%xmm1
     +0x1b1: psubd   %xmm2,%xmm1
     +0x1b5: movdqa  %xmm1,0x5d0(%rsp,%rax,8)
     +0x1be: add     $0x4,%rax
     +0x1c2: cmp     $0x100,%rax
     +0x1c8: jne     <mldsa65_pk_from_sk+0x150>
     +0x1ca: mov     $0x100,%eax
     +0x1cf: pxor    %xmm0,%xmm0
     +0x1d3: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x1e0: movzwl  0x80(%r15,%rax,1),%ecx
     +0x1e9: movd    %ecx,%xmm1
     +0x1ed: movzwl  0x82(%r15,%rax,1),%ecx
     +0x1f6: movd    %ecx,%xmm2
     +0x1fa: movdqa  %xmm1,%xmm3
     +0x1fe: psrlw   $0x4,%xmm3
     +0x203: movdqa  %xmm2,%xmm4
     +0x207: psrlw   $0x4,%xmm4
     +0x20c: punpcklbw %xmm3,%xmm1
     +0x210: pand    %xmm5,%xmm1
     +0x214: punpcklbw %xmm0,%xmm1
     +0x218: punpcklwd %xmm0,%xmm1
     +0x21c: movdqa  %xmm6,%xmm3
     +0x220: psubd   %xmm1,%xmm3
     +0x224: movdqa  %xmm3,0x5c0(%rsp,%rax,8)
     +0x22d: punpcklbw %xmm4,%xmm2
     +0x231: pand    %xmm5,%xmm2
     +0x235: punpcklbw %xmm0,%xmm2
     +0x239: punpcklwd %xmm0,%xmm2
     +0x23d: movdqa  %xmm6,%xmm1
     +0x241: psubd   %xmm2,%xmm1
     +0x245: movdqa  %xmm1,0x5d0(%rsp,%rax,8)
     +0x24e: add     $0x4,%rax
     +0x252: cmp     $0x180,%rax
     +0x258: jne     <mldsa65_pk_from_sk+0x1e0>
     +0x25a: mov     $0x180,%eax
     +0x25f: pxor    %xmm0,%xmm0
     +0x263: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x270: movzwl  0x80(%r15,%rax,1),%ecx
     +0x279: movd    %ecx,%xmm1
     +0x27d: movzwl  0x82(%r15,%rax,1),%ecx
     +0x286: movd    %ecx,%xmm2
     +0x28a: movdqa  %xmm1,%xmm3
     +0x28e: psrlw   $0x4,%xmm3
     +0x293: movdqa  %xmm2,%xmm4
     +0x297: psrlw   $0x4,%xmm4
     +0x29c: punpcklbw %xmm3,%xmm1
     +0x2a0: pand    %xmm5,%xmm1
     +0x2a4: punpcklbw %xmm0,%xmm1
     +0x2a8: punpcklwd %xmm0,%xmm1
     +0x2ac: movdqa  %xmm6,%xmm3
     +0x2b0: psubd   %xmm1,%xmm3
     +0x2b4: movdqa  %xmm3,0x5c0(%rsp,%rax,8)
     +0x2bd: punpcklbw %xmm4,%xmm2
     +0x2c1: pand    %xmm5,%xmm2
     +0x2c5: punpcklbw %xmm0,%xmm2
     +0x2c9: punpcklwd %xmm0,%xmm2
     +0x2cd: movdqa  %xmm6,%xmm1
     +0x2d1: psubd   %xmm2,%xmm1
     +0x2d5: movdqa  %xmm1,0x5d0(%rsp,%rax,8)
     +0x2de: add     $0x4,%rax
     +0x2e2: cmp     $0x200,%rax
     +0x2e8: jne     <mldsa65_pk_from_sk+0x270>
     +0x2ea: mov     $0x200,%eax
     +0x2ef: pxor    %xmm0,%xmm0
     +0x2f3: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x300: movzwl  0x80(%r15,%rax,1),%ecx
     +0x309: movd    %ecx,%xmm1
     +0x30d: movzwl  0x82(%r15,%rax,1),%ecx
     +0x316: movd    %ecx,%xmm2
     +0x31a: movdqa  %xmm1,%xmm3
     +0x31e: psrlw   $0x4,%xmm3
     +0x323: movdqa  %xmm2,%xmm4
     +0x327: psrlw   $0x4,%xmm4
     +0x32c: punpcklbw %xmm3,%xmm1
     +0x330: pand    %xmm5,%xmm1
     +0x334: punpcklbw %xmm0,%xmm1
     +0x338: punpcklwd %xmm0,%xmm1
     +0x33c: movdqa  %xmm6,%xmm3
     +0x340: psubd   %xmm1,%xmm3
     +0x344: movdqa  %xmm3,0x5c0(%rsp,%rax,8)
     +0x34d: punpcklbw %xmm4,%xmm2
     +0x351: pand    %xmm5,%xmm2
     +0x355: punpcklbw %xmm0,%xmm2
     +0x359: punpcklwd %xmm0,%xmm2
     +0x35d: movdqa  %xmm6,%xmm1
     +0x361: psubd   %xmm2,%xmm1
     +0x365: movdqa  %xmm1,0x5d0(%rsp,%rax,8)
     +0x36e: add     $0x4,%rax
     +0x372: cmp     $0x280,%rax
     +0x378: jne     <mldsa65_pk_from_sk+0x300>
     +0x37a: lea     0x5c0(%rsp),%rdi
     +0x382: mov     $0x5,%esi
     +0x387: call    <mldsa65_polyvecl_chknorm>
     +0x38c: movdqa  0x1037c(%rip),%xmm6
     +0x394: movdqa  0x10364(%rip),%xmm5
     +0x39c: mov     %eax,0xd4(%rsp)
     +0x3a3: xor     %eax,%eax
     +0x3a5: pxor    %xmm0,%xmm0
     +0x3a9: nopl    0x0(%rax)
     +0x3b0: movzwl  0x300(%r15,%rax,1),%ecx
     +0x3b9: movd    %ecx,%xmm1
     +0x3bd: movzwl  0x302(%r15,%rax,1),%ecx
     +0x3c6: movd    %ecx,%xmm2
     +0x3ca: movdqa  %xmm1,%xmm3
     +0x3ce: psrlw   $0x4,%xmm3
     +0x3d3: movdqa  %xmm2,%xmm4
     +0x3d7: psrlw   $0x4,%xmm4
     +0x3dc: punpcklbw %xmm3,%xmm1
     +0x3e0: pand    %xmm5,%xmm1
     +0x3e4: punpcklbw %xmm0,%xmm1
     +0x3e8: punpcklwd %xmm0,%xmm1
     +0x3ec: movdqa  %xmm6,%xmm3
     +0x3f0: psubd   %xmm1,%xmm3
     +0x3f4: movdqa  %xmm3,0x1c0(%rsp,%rax,8)
     +0x3fd: punpcklbw %xmm4,%xmm2
     +0x401: pand    %xmm5,%xmm2
     +0x405: punpcklbw %xmm0,%xmm2
     +0x409: punpcklwd %xmm0,%xmm2
     +0x40d: movdqa  %xmm6,%xmm1
     +0x411: psubd   %xmm2,%xmm1
     +0x415: movdqa  %xmm1,0x1d0(%rsp,%rax,8)
     +0x41e: add     $0x4,%rax
     +0x422: cmp     $0x80,%rax
     +0x428: jne     <mldsa65_pk_from_sk+0x3b0>
     +0x42a: xor     %edi,%edi
     +0x42c: xor     %eax,%eax
     +0x42e: xchg    %ax,%ax
     +0x430: movslq  0x1c0(%rsp,%rax,4),%rcx
     +0x438: mov     %ecx,%edx
     +0x43a: neg     %edx
     +0x43c: mov     %rcx,%rsi
     +0x43f: shr     $0x1f,%rsi
     +0x443: xor     %ecx,%edx
     +0x445: and     %esi,%edx
     +0x447: xor     %ecx,%edx
     +0x449: mov     $0x4,%ecx
     +0x44e: sub     %edx,%ecx
     +0x450: movslq  %ecx,%rcx
     +0x453: shr     $0x1f,%rcx
     +0x457: or      %ecx,%edi
     +0x459: inc     %rax
     +0x45c: cmp     $0x100,%rax
     +0x462: jne     <mldsa65_pk_from_sk+0x430>
     +0x464: xor     %eax,%eax
     +0x466: pxor    %xmm0,%xmm0
     +0x46a: nopw    0x0(%rax,%rax,1)
     +0x470: movzwl  0x380(%r15,%rax,1),%ecx
     +0x479: movd    %ecx,%xmm1
     +0x47d: movzwl  0x382(%r15,%rax,1),%ecx
     +0x486: movd    %ecx,%xmm2
     +0x48a: movdqa  %xmm1,%xmm3
     +0x48e: psrlw   $0x4,%xmm3
     +0x493: movdqa  %xmm2,%xmm4
     +0x497: psrlw   $0x4,%xmm4
     +0x49c: punpcklbw %xmm3,%xmm1
     +0x4a0: pand    %xmm5,%xmm1
     +0x4a4: punpcklbw %xmm0,%xmm1
     +0x4a8: punpcklwd %xmm0,%xmm1
     +0x4ac: movdqa  %xmm6,%xmm3
     +0x4b0: psubd   %xmm1,%xmm3
     +0x4b4: movdqa  %xmm3,0x1c0(%rsp,%rax,8)
     +0x4bd: punpcklbw %xmm4,%xmm2
     +0x4c1: pand    %xmm5,%xmm2
     +0x4c5: punpcklbw %xmm0,%xmm2
     +0x4c9: punpcklwd %xmm0,%xmm2
     +0x4cd: movdqa  %xmm6,%xmm1
     +0x4d1: psubd   %xmm2,%xmm1
     +0x4d5: movdqa  %xmm1,0x1d0(%rsp,%rax,8)
     +0x4de: add     $0x4,%rax
     +0x4e2: cmp     $0x80,%rax
     +0x4e8: jne     <mldsa65_pk_from_sk+0x470>
     +0x4ea: xor     %r8d,%r8d
     +0x4ed: xor     %eax,%eax
     +0x4ef: nop     
     +0x4f0: movslq  0x1c0(%rsp,%rax,4),%rcx
     +0x4f8: mov     %ecx,%edx
     +0x4fa: neg     %edx
     +0x4fc: mov     %rcx,%rsi
     +0x4ff: shr     $0x1f,%rsi
     +0x503: xor     %ecx,%edx
     +0x505: and     %esi,%edx
     +0x507: xor     %ecx,%edx
     +0x509: mov     $0x4,%ecx
     +0x50e: sub     %edx,%ecx
     +0x510: movslq  %ecx,%rcx
     +0x513: shr     $0x1f,%rcx
     +0x517: or      %ecx,%r8d
     +0x51a: inc     %rax
     +0x51d: cmp     $0x100,%rax
     +0x523: jne     <mldsa65_pk_from_sk+0x4f0>
     +0x525: xor     %eax,%eax
     +0x527: pxor    %xmm0,%xmm0
     +0x52b: nopl    0x0(%rax,%rax,1)
     +0x530: movzwl  0x400(%r15,%rax,1),%ecx
     +0x539: movd    %ecx,%xmm1
     +0x53d: movzwl  0x402(%r15,%rax,1),%ecx
     +0x546: movd    %ecx,%xmm2
     +0x54a: movdqa  %xmm1,%xmm3
     +0x54e: psrlw   $0x4,%xmm3
     +0x553: movdqa  %xmm2,%xmm4
     +0x557: psrlw   $0x4,%xmm4
     +0x55c: punpcklbw %xmm3,%xmm1
     +0x560: pand    %xmm5,%xmm1
     +0x564: punpcklbw %xmm0,%xmm1
     +0x568: punpcklwd %xmm0,%xmm1
     +0x56c: movdqa  %xmm6,%xmm3
     +0x570: psubd   %xmm1,%xmm3
     +0x574: movdqa  %xmm3,0x1c0(%rsp,%rax,8)
     +0x57d: punpcklbw %xmm4,%xmm2
     +0x581: pand    %xmm5,%xmm2
     +0x585: punpcklbw %xmm0,%xmm2
     +0x589: punpcklwd %xmm0,%xmm2
     +0x58d: movdqa  %xmm6,%xmm1
     +0x591: psubd   %xmm2,%xmm1
     +0x595: movdqa  %xmm1,0x1d0(%rsp,%rax,8)
     +0x59e: add     $0x4,%rax
     +0x5a2: cmp     $0x80,%rax
     +0x5a8: jne     <mldsa65_pk_from_sk+0x530>
     +0x5aa: xor     %r12d,%r12d
     +0x5ad: xor     %eax,%eax
     +0x5af: nop     
     +0x5b0: movslq  0x1c0(%rsp,%rax,4),%rcx
     +0x5b8: mov     %ecx,%edx
     +0x5ba: neg     %edx
     +0x5bc: mov     %rcx,%rsi
     +0x5bf: shr     $0x1f,%rsi
     +0x5c3: xor     %ecx,%edx
     +0x5c5: and     %esi,%edx
     +0x5c7: xor     %ecx,%edx
     +0x5c9: mov     $0x4,%ecx
     +0x5ce: sub     %edx,%ecx
     +0x5d0: movslq  %ecx,%rcx
     +0x5d3: shr     $0x1f,%rcx
     +0x5d7: or      %ecx,%r12d
     +0x5da: inc     %rax
     +0x5dd: cmp     $0x100,%rax
     +0x5e3: jne     <mldsa65_pk_from_sk+0x5b0>
     +0x5e5: mov     %rbx,0xd8(%rsp)
     +0x5ed: xor     %eax,%eax
     +0x5ef: pxor    %xmm0,%xmm0
     +0x5f3: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x600: movzwl  0x480(%r15,%rax,1),%ecx
     +0x609: movd    %ecx,%xmm1
     +0x60d: movzwl  0x482(%r15,%rax,1),%ecx
     +0x616: movd    %ecx,%xmm2
     +0x61a: movdqa  %xmm1,%xmm3
     +0x61e: psrlw   $0x4,%xmm3
     +0x623: movdqa  %xmm2,%xmm4
     +0x627: psrlw   $0x4,%xmm4
     +0x62c: punpcklbw %xmm3,%xmm1
     +0x630: pand    %xmm5,%xmm1
     +0x634: punpcklbw %xmm0,%xmm1
     +0x638: punpcklwd %xmm0,%xmm1
     +0x63c: movdqa  %xmm6,%xmm3
     +0x640: psubd   %xmm1,%xmm3
     +0x644: movdqa  %xmm3,0x1c0(%rsp,%rax,8)
     +0x64d: punpcklbw %xmm4,%xmm2
     +0x651: pand    %xmm5,%xmm2
     +0x655: punpcklbw %xmm0,%xmm2
     +0x659: punpcklwd %xmm0,%xmm2
     +0x65d: movdqa  %xmm6,%xmm1
     +0x661: psubd   %xmm2,%xmm1
     +0x665: movdqa  %xmm1,0x1d0(%rsp,%rax,8)
     +0x66e: add     $0x4,%rax
     +0x672: cmp     $0x80,%rax
     +0x678: jne     <mldsa65_pk_from_sk+0x600>
     +0x67a: xor     %ebx,%ebx
     +0x67c: xor     %eax,%eax
     +0x67e: xchg    %ax,%ax
     +0x680: movslq  0x1c0(%rsp,%rax,4),%rcx
     +0x688: mov     %ecx,%edx
     +0x68a: neg     %edx
     +0x68c: mov     %rcx,%rsi
     +0x68f: shr     $0x1f,%rsi
     +0x693: xor     %ecx,%edx
     +0x695: and     %esi,%edx
     +0x697: xor     %ecx,%edx
     +0x699: mov     $0x4,%ecx
     +0x69e: sub     %edx,%ecx
     +0x6a0: movslq  %ecx,%rcx
     +0x6a3: shr     $0x1f,%rcx
     +0x6a7: or      %ecx,%ebx
     +0x6a9: inc     %rax
     +0x6ac: cmp     $0x100,%rax
     +0x6b2: jne     <mldsa65_pk_from_sk+0x680>
     +0x6b4: xor     %eax,%eax
     +0x6b6: pxor    %xmm0,%xmm0
     +0x6ba: nopw    0x0(%rax,%rax,1)
     +0x6c0: movzwl  0x500(%r15,%rax,1),%ecx
     +0x6c9: movd    %ecx,%xmm1
     +0x6cd: movzwl  0x502(%r15,%rax,1),%ecx
     +0x6d6: movd    %ecx,%xmm2
     +0x6da: movdqa  %xmm1,%xmm3
     +0x6de: psrlw   $0x4,%xmm3
     +0x6e3: movdqa  %xmm2,%xmm4
     +0x6e7: psrlw   $0x4,%xmm4
     +0x6ec: punpcklbw %xmm3,%xmm1
     +0x6f0: pand    %xmm5,%xmm1
     +0x6f4: punpcklbw %xmm0,%xmm1
     +0x6f8: punpcklwd %xmm0,%xmm1
     +0x6fc: movdqa  %xmm6,%xmm3
     +0x700: psubd   %xmm1,%xmm3
     +0x704: movdqa  %xmm3,0x1c0(%rsp,%rax,8)
     +0x70d: punpcklbw %xmm4,%xmm2
     +0x711: pand    %xmm5,%xmm2
     +0x715: punpcklbw %xmm0,%xmm2
     +0x719: punpcklwd %xmm0,%xmm2
     +0x71d: movdqa  %xmm6,%xmm1
     +0x721: psubd   %xmm2,%xmm1
     +0x725: movdqa  %xmm1,0x1d0(%rsp,%rax,8)
     +0x72e: add     $0x4,%rax
     +0x732: cmp     $0x80,%rax
     +0x738: jne     <mldsa65_pk_from_sk+0x6c0>
     +0x73a: xor     %r13d,%r13d
     +0x73d: xor     %eax,%eax
     +0x73f: nop     
     +0x740: movslq  0x1c0(%rsp,%rax,4),%rcx
     +0x748: mov     %ecx,%edx
     +0x74a: neg     %edx
     +0x74c: mov     %rcx,%rsi
     +0x74f: shr     $0x1f,%rsi
     +0x753: xor     %ecx,%edx
     +0x755: and     %esi,%edx
     +0x757: xor     %ecx,%edx
     +0x759: mov     $0x4,%ecx
     +0x75e: sub     %edx,%ecx
     +0x760: movslq  %ecx,%rcx
     +0x763: shr     $0x1f,%rcx
     +0x767: or      %ecx,%r13d
     +0x76a: inc     %rax
     +0x76d: cmp     $0x100,%rax
     +0x773: jne     <mldsa65_pk_from_sk+0x740>
     +0x775: xor     %eax,%eax
     +0x777: pxor    %xmm0,%xmm0
     +0x77b: nopl    0x0(%rax,%rax,1)
     +0x780: movzwl  0x580(%r15,%rax,1),%ecx
     +0x789: movd    %ecx,%xmm1
     +0x78d: movzwl  0x582(%r15,%rax,1),%ecx
     +0x796: movd    %ecx,%xmm2
     +0x79a: movdqa  %xmm1,%xmm3
     +0x79e: psrlw   $0x4,%xmm3
     +0x7a3: movdqa  %xmm2,%xmm4
     +0x7a7: psrlw   $0x4,%xmm4
     +0x7ac: punpcklbw %xmm3,%xmm1
     +0x7b0: pand    %xmm5,%xmm1
     +0x7b4: punpcklbw %xmm0,%xmm1
     +0x7b8: punpcklwd %xmm0,%xmm1
     +0x7bc: movdqa  %xmm6,%xmm3
     +0x7c0: psubd   %xmm1,%xmm3
     +0x7c4: movdqa  %xmm3,0x1c0(%rsp,%rax,8)
     +0x7cd: punpcklbw %xmm4,%xmm2
     +0x7d1: pand    %xmm5,%xmm2
     +0x7d5: punpcklbw %xmm0,%xmm2
     +0x7d9: punpcklwd %xmm0,%xmm2
     +0x7dd: movdqa  %xmm6,%xmm1
     +0x7e1: psubd   %xmm2,%xmm1
     +0x7e5: movdqa  %xmm1,0x1d0(%rsp,%rax,8)
     +0x7ee: add     $0x4,%rax
     +0x7f2: cmp     $0x80,%rax
     +0x7f8: jne     <mldsa65_pk_from_sk+0x780>
     +0x7fa: mov     %r8,0x110(%rsp)
     +0x802: mov     %rdi,0x118(%rsp)
     +0x80a: xor     %r14d,%r14d
     +0x80d: xor     %eax,%eax
     +0x80f: nop     
     +0x810: movslq  0x1c0(%rsp,%rax,4),%rcx
     +0x818: mov     %ecx,%edx
     +0x81a: neg     %edx
     +0x81c: mov     %rcx,%rsi
     +0x81f: shr     $0x1f,%rsi
     +0x823: xor     %ecx,%edx
     +0x825: and     %esi,%edx
     +0x827: xor     %ecx,%edx
     +0x829: mov     $0x4,%ecx
     +0x82e: sub     %edx,%ecx
     +0x830: movslq  %ecx,%rcx
     +0x833: shr     $0x1f,%rcx
     +0x837: or      %ecx,%r14d
     +0x83a: inc     %rax
     +0x83d: cmp     $0x100,%rax
     +0x843: jne     <mldsa65_pk_from_sk+0x810>
     +0x845: lea     0x5c0(%rsp),%rdi
     +0x84d: call    <mldsa_poly_ntt>
     +0x852: lea     0x9c0(%rsp),%rdi
     +0x85a: call    <mldsa_poly_ntt>
     +0x85f: lea     0xdc0(%rsp),%rdi
     +0x867: call    <mldsa_poly_ntt>
     +0x86c: lea     0x11c0(%rsp),%rdi
     +0x874: call    <mldsa_poly_ntt>
     +0x879: lea     0x15c0(%rsp),%rdi
     +0x881: call    <mldsa_poly_ntt>
     +0x886: movdqa  0xe0(%rsp),%xmm0
     +0x88f: movdqa  0xf0(%rsp),%xmm1
     +0x898: mov     0xd8(%rsp),%rax
     +0x8a0: movdqu  %xmm1,0x10(%rax)
     +0x8a5: movdqu  %xmm0,(%rax)
     +0x8a9: lea     0x20(%rax),%rdi
     +0x8ad: lea     0x19c0(%rsp),%rsi
     +0x8b5: lea     0xe0(%rsp),%r8
     +0x8bd: lea     0x5c0(%rsp),%rdx
     +0x8c5: lea     0x300(%r15),%rcx
     +0x8cc: call    <mld_compute_pack_t0_t165>
     +0x8d1: pxor    %xmm2,%xmm2
     +0x8d5: xor     %eax,%eax
     +0x8d7: pxor    %xmm3,%xmm3
     +0x8db: pxor    %xmm1,%xmm1
     +0x8df: pxor    %xmm0,%xmm0
     +0x8e3: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x8f0: movdqu  0x600(%r15,%rax,1),%xmm4
     +0x8fa: movdqu  0x610(%r15,%rax,1),%xmm5
     +0x904: movdqa  %xmm2,%xmm6
     +0x908: movdqu  0x620(%r15,%rax,1),%xmm2
     +0x912: movdqa  %xmm3,%xmm7
     +0x916: movdqu  0x630(%r15,%rax,1),%xmm3
     +0x920: pxor    0x19c0(%rsp,%rax,1),%xmm4
     +0x929: pxor    0x19d0(%rsp,%rax,1),%xmm5
     +0x932: por     %xmm4,%xmm1
     +0x936: por     %xmm5,%xmm0
     +0x93a: pxor    %xmm4,%xmm6
     +0x93e: pxor    %xmm5,%xmm7
     +0x942: pxor    0x19e0(%rsp,%rax,1),%xmm2
     +0x94b: pxor    0x19f0(%rsp,%rax,1),%xmm3
     +0x954: por     %xmm2,%xmm1
     +0x958: por     %xmm3,%xmm0
     +0x95c: pxor    %xmm6,%xmm2
     +0x960: pxor    %xmm7,%xmm3
     +0x964: add     $0x40,%rax
     +0x968: cmp     $0x9c0,%rax
     +0x96e: jne     <mldsa65_pk_from_sk+0x8f0>
     +0x970: pxor    %xmm2,%xmm3
     +0x974: pshufd  $0xee,%xmm3,%xmm2
     +0x979: pxor    %xmm3,%xmm2
     +0x97d: pshufd  $0x55,%xmm2,%xmm3
     +0x982: pxor    %xmm2,%xmm3
     +0x986: movdqa  %xmm3,%xmm2
     +0x98a: psrld   $0x10,%xmm2
     +0x98f: pxor    %xmm3,%xmm2
     +0x993: movdqa  %xmm2,%xmm3
     +0x997: psrlw   $0x8,%xmm3
     +0x99c: pxor    %xmm2,%xmm3
     +0x9a0: movd    %xmm3,%ecx
     +0x9a4: mov     %ecx,0xd0(%rsp)
     +0x9ab: por     %xmm1,%xmm0
     +0x9af: pshufd  $0xee,%xmm0,%xmm1
     +0x9b4: por     %xmm0,%xmm1
     +0x9b8: pshufd  $0x55,%xmm1,%xmm0
     +0x9bd: por     %xmm1,%xmm0
     +0x9c1: movdqa  %xmm0,%xmm1
     +0x9c5: psrld   $0x10,%xmm1
     +0x9ca: por     %xmm0,%xmm1
     +0x9ce: movdqa  %xmm1,%xmm0
     +0x9d2: psrlw   $0x8,%xmm0
     +0x9d7: por     %xmm1,%xmm0
     +0x9db: movd    %xmm0,%eax
     +0x9df: movzbl  %al,%eax
     +0x9e2: neg     %rax
     +0x9e5: shr     $0x20,%rax
     +0x9e9: xor     %cl,%al
     +0x9eb: mov     %rax,0x108(%rsp)
     +0x9f3: pxor    %xmm0,%xmm0
     +0x9f7: movdqu  %xmm0,0xbc(%rsp)
     +0xa00: movdqa  %xmm0,0xb0(%rsp)
     +0xa09: movdqa  %xmm0,0xa0(%rsp)
     +0xa12: movdqa  %xmm0,0x90(%rsp)
     +0xa1b: movdqa  %xmm0,0x80(%rsp)
     +0xa24: movdqa  %xmm0,0x70(%rsp)
     +0xa2a: movdqa  %xmm0,0x60(%rsp)
     +0xa30: movdqa  %xmm0,0x50(%rsp)
     +0xa36: movdqa  %xmm0,0x40(%rsp)
     +0xa3c: movdqa  %xmm0,0x30(%rsp)
     +0xa42: movdqa  %xmm0,0x20(%rsp)
     +0xa48: movdqa  %xmm0,0x10(%rsp)
     +0xa4e: movdqa  %xmm0,(%rsp)
     +0xa53: mov     0xd8(%rsp),%r15
     +0xa5b: movups  (%r15),%xmm0
     +0xa5f: movups  0x10(%r15),%xmm1
     +0xa64: movaps  %xmm0,(%rsp)
     +0xa68: movaps  %xmm1,0x10(%rsp)
     +0xa6d: movups  0x20(%r15),%xmm0
     +0xa72: movups  0x30(%r15),%xmm1
     +0xa77: movaps  %xmm0,0x20(%rsp)
     +0xa7c: movaps  %xmm1,0x30(%rsp)
     +0xa81: movups  0x40(%r15),%xmm0
     +0xa86: movups  0x50(%r15),%xmm1
     +0xa8b: xorps   0x40(%rsp),%xmm0
     +0xa90: xorps   0x50(%rsp),%xmm1
     +0xa95: movaps  %xmm0,0x40(%rsp)
     +0xa9a: movaps  %xmm1,0x50(%rsp)
     +0xa9f: movups  0x60(%r15),%xmm0
     +0xaa4: movups  0x70(%r15),%xmm1
     +0xaa9: xorps   0x60(%rsp),%xmm0
     +0xaae: xorps   0x70(%rsp),%xmm1
     +0xab3: movaps  %xmm0,0x60(%rsp)
     +0xab8: movaps  %xmm1,0x70(%rsp)
     +0xabd: mov     0x80(%r15),%rax
     +0xac4: xor     %rax,0x80(%rsp)
     +0xacc: mov     %rsp,%rdi
     +0xacf: call    <mldsa_keccakf1600_permute>
     +0xad4: movups  0x88(%r15),%xmm0
     +0xadc: movups  0x98(%r15),%xmm1
     +0xae4: xorps   (%rsp),%xmm0
     +0xae8: xorps   0x10(%rsp),%xmm1
     +0xaed: movaps  %xmm0,(%rsp)
     +0xaf1: movaps  %xmm1,0x10(%rsp)
     +0xaf6: movups  0xa8(%r15),%xmm0
     +0xafe: movups  0xb8(%r15),%xmm1
     +0xb06: xorps   0x20(%rsp),%xmm0
     +0xb0b: xorps   0x30(%rsp),%xmm1
     +0xb10: movaps  %xmm0,0x20(%rsp)
     +0xb15: movaps  %xmm1,0x30(%rsp)
     +0xb1a: movups  0xc8(%r15),%xmm0
     +0xb22: movups  0xd8(%r15),%xmm1
     +0xb2a: xorps   0x40(%rsp),%xmm0
     +0xb2f: xorps   0x50(%rsp),%xmm1
     +0xb34: movaps  %xmm0,0x40(%rsp)
     +0xb39: movaps  %xmm1,0x50(%rsp)
     +0xb3e: movups  0xe8(%r15),%xmm0
     +0xb46: movups  0xf8(%r15),%xmm1
     +0xb4e: xorps   0x60(%rsp),%xmm0
     +0xb53: xorps   0x70(%rsp),%xmm1
     +0xb58: movaps  %xmm0,0x60(%rsp)
     +0xb5d: movaps  %xmm1,0x70(%rsp)
     +0xb62: mov     0x108(%r15),%rax
     +0xb69: xor     %rax,0x80(%rsp)
     +0xb71: mov     %rsp,%rdi
     +0xb74: call    <mldsa_keccakf1600_permute>
     +0xb79: movups  0x110(%r15),%xmm0
     +0xb81: movups  0x120(%r15),%xmm1
     +0xb89: xorps   (%rsp),%xmm0
     +0xb8d: xorps   0x10(%rsp),%xmm1
     +0xb92: movaps  %xmm0,(%rsp)
     +0xb96: movaps  %xmm1,0x10(%rsp)
     +0xb9b: movups  0x130(%r15),%xmm0
     +0xba3: movups  0x140(%r15),%xmm1
     +0xbab: xorps   0x20(%rsp),%xmm0
     +0xbb0: xorps   0x30(%rsp),%xmm1
     +0xbb5: movaps  %xmm0,0x20(%rsp)
     +0xbba: movaps  %xmm1,0x30(%rsp)
     +0xbbf: movups  0x150(%r15),%xmm0
     +0xbc7: movups  0x160(%r15),%xmm1
     +0xbcf: xorps   0x40(%rsp),%xmm0
     +0xbd4: xorps   0x50(%rsp),%xmm1
     +0xbd9: movaps  %xmm0,0x40(%rsp)
     +0xbde: movaps  %xmm1,0x50(%rsp)
     +0xbe3: movups  0x170(%r15),%xmm0
     +0xbeb: movups  0x180(%r15),%xmm1
     +0xbf3: xorps   0x60(%rsp),%xmm0
     +0xbf8: xorps   0x70(%rsp),%xmm1
     +0xbfd: movaps  %xmm0,0x60(%rsp)
     +0xc02: movaps  %xmm1,0x70(%rsp)
     +0xc07: mov     0x190(%r15),%rax
     +0xc0e: xor     %rax,0x80(%rsp)
     +0xc16: mov     %rsp,%rdi
     +0xc19: call    <mldsa_keccakf1600_permute>
     +0xc1e: movups  0x198(%r15),%xmm0
     +0xc26: movups  0x1a8(%r15),%xmm1
     +0xc2e: xorps   (%rsp),%xmm0
     +0xc32: xorps   0x10(%rsp),%xmm1
     +0xc37: movaps  %xmm0,(%rsp)
     +0xc3b: movaps  %xmm1,0x10(%rsp)
     +0xc40: movups  0x1b8(%r15),%xmm0
     +0xc48: movups  0x1c8(%r15),%xmm1
     +0xc50: xorps   0x20(%rsp),%xmm0
     +0xc55: xorps   0x30(%rsp),%xmm1
     +0xc5a: movaps  %xmm0,0x20(%rsp)
     +0xc5f: movaps  %xmm1,0x30(%rsp)
     +0xc64: movups  0x1d8(%r15),%xmm0
     +0xc6c: movups  0x1e8(%r15),%xmm1
     +0xc74: xorps   0x40(%rsp),%xmm0
     +0xc79: xorps   0x50(%rsp),%xmm1
     +0xc7e: movaps  %xmm0,0x40(%rsp)
     +0xc83: movaps  %xmm1,0x50(%rsp)
     +0xc88: movups  0x1f8(%r15),%xmm0
     +0xc90: movups  0x208(%r15),%xmm1
     +0xc98: xorps   0x60(%rsp),%xmm0
     +0xc9d: xorps   0x70(%rsp),%xmm1
     +0xca2: movaps  %xmm0,0x60(%rsp)
     +0xca7: movaps  %xmm1,0x70(%rsp)
     +0xcac: mov     0x218(%r15),%rax
     +0xcb3: xor     %rax,0x80(%rsp)
     +0xcbb: mov     %rsp,%rdi
     +0xcbe: call    <mldsa_keccakf1600_permute>
     +0xcc3: movups  0x220(%r15),%xmm0
     +0xccb: movups  0x230(%r15),%xmm1
     +0xcd3: xorps   (%rsp),%xmm0
     +0xcd7: xorps   0x10(%rsp),%xmm1
     +0xcdc: movaps  %xmm0,(%rsp)
     +0xce0: movaps  %xmm1,0x10(%rsp)
     +0xce5: movups  0x240(%r15),%xmm0
     +0xced: movups  0x250(%r15),%xmm1
     +0xcf5: xorps   0x20(%rsp),%xmm0
     +0xcfa: xorps   0x30(%rsp),%xmm1
     +0xcff: movaps  %xmm0,0x20(%rsp)
     +0xd04: movaps  %xmm1,0x30(%rsp)
     +0xd09: movups  0x260(%r15),%xmm0
     +0xd11: movups  0x270(%r15),%xmm1
     +0xd19: xorps   0x40(%rsp),%xmm0
     +0xd1e: xorps   0x50(%rsp),%xmm1
     +0xd23: movaps  %xmm0,0x40(%rsp)
     +0xd28: movaps  %xmm1,0x50(%rsp)
     +0xd2d: movups  0x280(%r15),%xmm0
     +0xd35: movups  0x290(%r15),%xmm1
     +0xd3d: xorps   0x60(%rsp),%xmm0
     +0xd42: xorps   0x70(%rsp),%xmm1
     +0xd47: movaps  %xmm0,0x60(%rsp)
     +0xd4c: movaps  %xmm1,0x70(%rsp)
     +0xd51: mov     0x2a0(%r15),%rax
     +0xd58: xor     %rax,0x80(%rsp)
     +0xd60: mov     %rsp,%rdi
     +0xd63: call    <mldsa_keccakf1600_permute>
     +0xd68: movups  0x2a8(%r15),%xmm0
     +0xd70: movups  0x2b8(%r15),%xmm1
     +0xd78: xorps   (%rsp),%xmm0
     +0xd7c: xorps   0x10(%rsp),%xmm1
     +0xd81: movaps  %xmm0,(%rsp)
     +0xd85: movaps  %xmm1,0x10(%rsp)
     +0xd8a: movups  0x2c8(%r15),%xmm0
     +0xd92: movups  0x2d8(%r15),%xmm1
     +0xd9a: xorps   0x20(%rsp),%xmm0
     +0xd9f: xorps   0x30(%rsp),%xmm1
     +0xda4: movaps  %xmm0,0x20(%rsp)
     +0xda9: movaps  %xmm1,0x30(%rsp)
     +0xdae: movups  0x2e8(%r15),%xmm0
     +0xdb6: movups  0x2f8(%r15),%xmm1
     +0xdbe: xorps   0x40(%rsp),%xmm0
     +0xdc3: xorps   0x50(%rsp),%xmm1
     +0xdc8: movaps  %xmm0,0x40(%rsp)
     +0xdcd: movaps  %xmm1,0x50(%rsp)
     +0xdd2: movups  0x308(%r15),%xmm0
     +0xdda: movups  0x318(%r15),%xmm1
     +0xde2: xorps   0x60(%rsp),%xmm0
     +0xde7: xorps   0x70(%rsp),%xmm1
     +0xdec: movaps  %xmm0,0x60(%rsp)
     +0xdf1: movaps  %xmm1,0x70(%rsp)
     +0xdf6: mov     0x328(%r15),%rax
     +0xdfd: xor     %rax,0x80(%rsp)
     +0xe05: mov     %rsp,%rdi
     +0xe08: call    <mldsa_keccakf1600_permute>
     +0xe0d: movups  0x330(%r15),%xmm0
     +0xe15: movups  0x340(%r15),%xmm1
     +0xe1d: xorps   (%rsp),%xmm0
     +0xe21: xorps   0x10(%rsp),%xmm1
     +0xe26: movaps  %xmm0,(%rsp)
     +0xe2a: movaps  %xmm1,0x10(%rsp)
     +0xe2f: movups  0x350(%r15),%xmm0
     +0xe37: movups  0x360(%r15),%xmm1
     +0xe3f: xorps   0x20(%rsp),%xmm0
     +0xe44: xorps   0x30(%rsp),%xmm1
     +0xe49: movaps  %xmm0,0x20(%rsp)
     +0xe4e: movaps  %xmm1,0x30(%rsp)
     +0xe53: movups  0x370(%r15),%xmm0
     +0xe5b: movups  0x380(%r15),%xmm1
     +0xe63: xorps   0x40(%rsp),%xmm0
     +0xe68: xorps   0x50(%rsp),%xmm1
     +0xe6d: movaps  %xmm0,0x40(%rsp)
     +0xe72: movaps  %xmm1,0x50(%rsp)
     +0xe77: movups  0x390(%r15),%xmm0
     +0xe7f: movups  0x3a0(%r15),%xmm1
     +0xe87: xorps   0x60(%rsp),%xmm0
     +0xe8c: xorps   0x70(%rsp),%xmm1
     +0xe91: movaps  %xmm0,0x60(%rsp)
     +0xe96: movaps  %xmm1,0x70(%rsp)
     +0xe9b: mov     0x3b0(%r15),%rax
     +0xea2: xor     %rax,0x80(%rsp)
     +0xeaa: mov     %rsp,%rdi
     +0xead: call    <mldsa_keccakf1600_permute>
     +0xeb2: movups  0x3b8(%r15),%xmm0
     +0xeba: movups  0x3c8(%r15),%xmm1
     +0xec2: xorps   (%rsp),%xmm0
     +0xec6: xorps   0x10(%rsp),%xmm1
     +0xecb: movaps  %xmm0,(%rsp)
     +0xecf: movaps  %xmm1,0x10(%rsp)
     +0xed4: movups  0x3d8(%r15),%xmm0
     +0xedc: movups  0x3e8(%r15),%xmm1
     +0xee4: xorps   0x20(%rsp),%xmm0
     +0xee9: xorps   0x30(%rsp),%xmm1
     +0xeee: movaps  %xmm0,0x20(%rsp)
     +0xef3: movaps  %xmm1,0x30(%rsp)
     +0xef8: movups  0x3f8(%r15),%xmm0
     +0xf00: movups  0x408(%r15),%xmm1
     +0xf08: xorps   0x40(%rsp),%xmm0
     +0xf0d: xorps   0x50(%rsp),%xmm1
     +0xf12: movaps  %xmm0,0x40(%rsp)
     +0xf17: movaps  %xmm1,0x50(%rsp)
     +0xf1c: movups  0x418(%r15),%xmm0
     +0xf24: movups  0x428(%r15),%xmm1
     +0xf2c: xorps   0x60(%rsp),%xmm0
     +0xf31: xorps   0x70(%rsp),%xmm1
     +0xf36: movaps  %xmm0,0x60(%rsp)
     +0xf3b: movaps  %xmm1,0x70(%rsp)
     +0xf40: mov     0x438(%r15),%rax
     +0xf47: xor     %rax,0x80(%rsp)
     +0xf4f: mov     %rsp,%rdi
     +0xf52: call    <mldsa_keccakf1600_permute>
     +0xf57: movups  0x440(%r15),%xmm0
     +0xf5f: movups  0x450(%r15),%xmm1
     +0xf67: xorps   (%rsp),%xmm0
     +0xf6b: xorps   0x10(%rsp),%xmm1
     +0xf70: movaps  %xmm0,(%rsp)
     +0xf74: movaps  %xmm1,0x10(%rsp)
     +0xf79: movups  0x460(%r15),%xmm0
     +0xf81: movups  0x470(%r15),%xmm1
     +0xf89: xorps   0x20(%rsp),%xmm0
     +0xf8e: xorps   0x30(%rsp),%xmm1
     +0xf93: movaps  %xmm0,0x20(%rsp)
     +0xf98: movaps  %xmm1,0x30(%rsp)
     +0xf9d: movups  0x480(%r15),%xmm0
     +0xfa5: movups  0x490(%r15),%xmm1
     +0xfad: xorps   0x40(%rsp),%xmm0
     +0xfb2: xorps   0x50(%rsp),%xmm1
     +0xfb7: movaps  %xmm0,0x40(%rsp)
     +0xfbc: movaps  %xmm1,0x50(%rsp)
     +0xfc1: movups  0x4a0(%r15),%xmm0
     +0xfc9: movups  0x4b0(%r15),%xmm1
     +0xfd1: xorps   0x60(%rsp),%xmm0
     +0xfd6: xorps   0x70(%rsp),%xmm1
     +0xfdb: movaps  %xmm0,0x60(%rsp)
     +0xfe0: movaps  %xmm1,0x70(%rsp)
     +0xfe5: mov     0x4c0(%r15),%rax
     +0xfec: xor     %rax,0x80(%rsp)
     +0xff4: mov     %rsp,%rdi
     +0xff7: call    <mldsa_keccakf1600_permute>
     +0xffc: movups  0x4c8(%r15),%xmm0
    +0x1004: movups  0x4d8(%r15),%xmm1
    +0x100c: xorps   (%rsp),%xmm0
    +0x1010: xorps   0x10(%rsp),%xmm1
    +0x1015: movaps  %xmm0,(%rsp)
    +0x1019: movaps  %xmm1,0x10(%rsp)
    +0x101e: movups  0x4e8(%r15),%xmm0
    +0x1026: movups  0x4f8(%r15),%xmm1
    +0x102e: xorps   0x20(%rsp),%xmm0
    +0x1033: xorps   0x30(%rsp),%xmm1
    +0x1038: movaps  %xmm0,0x20(%rsp)
    +0x103d: movaps  %xmm1,0x30(%rsp)
    +0x1042: movups  0x508(%r15),%xmm0
    +0x104a: movups  0x518(%r15),%xmm1
    +0x1052: xorps   0x40(%rsp),%xmm0
    +0x1057: xorps   0x50(%rsp),%xmm1
    +0x105c: movaps  %xmm0,0x40(%rsp)
    +0x1061: movaps  %xmm1,0x50(%rsp)
    +0x1066: movups  0x528(%r15),%xmm0
    +0x106e: movups  0x538(%r15),%xmm1
    +0x1076: xorps   0x60(%rsp),%xmm0
    +0x107b: xorps   0x70(%rsp),%xmm1
    +0x1080: movaps  %xmm0,0x60(%rsp)
    +0x1085: movaps  %xmm1,0x70(%rsp)
    +0x108a: mov     0x548(%r15),%rax
    +0x1091: xor     %rax,0x80(%rsp)
    +0x1099: mov     %rsp,%rdi
    +0x109c: call    <mldsa_keccakf1600_permute>
    +0x10a1: movups  0x550(%r15),%xmm0
    +0x10a9: movups  0x560(%r15),%xmm1
    +0x10b1: xorps   (%rsp),%xmm0
    +0x10b5: xorps   0x10(%rsp),%xmm1
    +0x10ba: movaps  %xmm0,(%rsp)
    +0x10be: movaps  %xmm1,0x10(%rsp)
    +0x10c3: movups  0x570(%r15),%xmm0
    +0x10cb: movups  0x580(%r15),%xmm1
    +0x10d3: xorps   0x20(%rsp),%xmm0
    +0x10d8: xorps   0x30(%rsp),%xmm1
    +0x10dd: movaps  %xmm0,0x20(%rsp)
    +0x10e2: movaps  %xmm1,0x30(%rsp)
    +0x10e7: movups  0x590(%r15),%xmm0
    +0x10ef: movups  0x5a0(%r15),%xmm1
    +0x10f7: xorps   0x40(%rsp),%xmm0
    +0x10fc: xorps   0x50(%rsp),%xmm1
    +0x1101: movaps  %xmm0,0x40(%rsp)
    +0x1106: movaps  %xmm1,0x50(%rsp)
    +0x110b: movups  0x5b0(%r15),%xmm0
    +0x1113: movups  0x5c0(%r15),%xmm1
    +0x111b: xorps   0x60(%rsp),%xmm0
    +0x1120: xorps   0x70(%rsp),%xmm1
    +0x1125: movaps  %xmm0,0x60(%rsp)
    +0x112a: movaps  %xmm1,0x70(%rsp)
    +0x112f: mov     0x5d0(%r15),%rax
    +0x1136: xor     %rax,0x80(%rsp)
    +0x113e: mov     %rsp,%rdi
    +0x1141: call    <mldsa_keccakf1600_permute>
    +0x1146: movups  0x5d8(%r15),%xmm0
    +0x114e: movups  0x5e8(%r15),%xmm1
    +0x1156: xorps   (%rsp),%xmm0
    +0x115a: xorps   0x10(%rsp),%xmm1
    +0x115f: movaps  %xmm0,(%rsp)
    +0x1163: movaps  %xmm1,0x10(%rsp)
    +0x1168: movups  0x5f8(%r15),%xmm0
    +0x1170: movups  0x608(%r15),%xmm1
    +0x1178: xorps   0x20(%rsp),%xmm0
    +0x117d: xorps   0x30(%rsp),%xmm1
    +0x1182: movaps  %xmm0,0x20(%rsp)
    +0x1187: movaps  %xmm1,0x30(%rsp)
    +0x118c: movups  0x618(%r15),%xmm0
    +0x1194: movups  0x628(%r15),%xmm1
    +0x119c: xorps   0x40(%rsp),%xmm0
    +0x11a1: xorps   0x50(%rsp),%xmm1
    +0x11a6: movaps  %xmm0,0x40(%rsp)
    +0x11ab: movaps  %xmm1,0x50(%rsp)
    +0x11b0: movups  0x638(%r15),%xmm0
    +0x11b8: movups  0x648(%r15),%xmm1
    +0x11c0: xorps   0x60(%rsp),%xmm0
    +0x11c5: xorps   0x70(%rsp),%xmm1
    +0x11ca: movaps  %xmm0,0x60(%rsp)
    +0x11cf: movaps  %xmm1,0x70(%rsp)
    +0x11d4: mov     0x658(%r15),%rax
    +0x11db: xor     %rax,0x80(%rsp)
    +0x11e3: mov     %rsp,%rdi
    +0x11e6: call    <mldsa_keccakf1600_permute>
    +0x11eb: movups  0x660(%r15),%xmm0
    +0x11f3: movups  0x670(%r15),%xmm1
    +0x11fb: xorps   (%rsp),%xmm0
    +0x11ff: xorps   0x10(%rsp),%xmm1
    +0x1204: movaps  %xmm0,(%rsp)
    +0x1208: movaps  %xmm1,0x10(%rsp)
    +0x120d: movups  0x680(%r15),%xmm0
    +0x1215: movups  0x690(%r15),%xmm1
    +0x121d: xorps   0x20(%rsp),%xmm0
    +0x1222: xorps   0x30(%rsp),%xmm1
    +0x1227: movaps  %xmm0,0x20(%rsp)
    +0x122c: movaps  %xmm1,0x30(%rsp)
    +0x1231: movups  0x6a0(%r15),%xmm0
    +0x1239: movups  0x6b0(%r15),%xmm1
    +0x1241: xorps   0x40(%rsp),%xmm0
    +0x1246: xorps   0x50(%rsp),%xmm1
    +0x124b: movaps  %xmm0,0x40(%rsp)
    +0x1250: movaps  %xmm1,0x50(%rsp)
    +0x1255: movups  0x6c0(%r15),%xmm0
    +0x125d: movups  0x6d0(%r15),%xmm1
    +0x1265: xorps   0x60(%rsp),%xmm0
    +0x126a: xorps   0x70(%rsp),%xmm1
    +0x126f: movaps  %xmm0,0x60(%rsp)
    +0x1274: movaps  %xmm1,0x70(%rsp)
    +0x1279: mov     0x6e0(%r15),%rax
    +0x1280: xor     %rax,0x80(%rsp)
    +0x1288: mov     %rsp,%rdi
    +0x128b: call    <mldsa_keccakf1600_permute>
    +0x1290: movups  0x6e8(%r15),%xmm0
    +0x1298: movups  0x6f8(%r15),%xmm1
    +0x12a0: xorps   (%rsp),%xmm0
    +0x12a4: xorps   0x10(%rsp),%xmm1
    +0x12a9: movaps  %xmm0,(%rsp)
    +0x12ad: movaps  %xmm1,0x10(%rsp)
    +0x12b2: movups  0x708(%r15),%xmm0
    +0x12ba: movups  0x718(%r15),%xmm1
    +0x12c2: xorps   0x20(%rsp),%xmm0
    +0x12c7: xorps   0x30(%rsp),%xmm1
    +0x12cc: movaps  %xmm0,0x20(%rsp)
    +0x12d1: movaps  %xmm1,0x30(%rsp)
    +0x12d6: movups  0x728(%r15),%xmm0
    +0x12de: movups  0x738(%r15),%xmm1
    +0x12e6: xorps   0x40(%rsp),%xmm0
    +0x12eb: xorps   0x50(%rsp),%xmm1
    +0x12f0: movaps  %xmm0,0x40(%rsp)
    +0x12f5: movaps  %xmm1,0x50(%rsp)
    +0x12fa: movups  0x748(%r15),%xmm0
    +0x1302: movups  0x758(%r15),%xmm1
    +0x130a: xorps   0x60(%rsp),%xmm0
    +0x130f: xorps   0x70(%rsp),%xmm1
    +0x1314: movaps  %xmm0,0x60(%rsp)
    +0x1319: movaps  %xmm1,0x70(%rsp)
    +0x131e: mov     0x768(%r15),%rax
    +0x1325: xor     %rax,0x80(%rsp)
    +0x132d: mov     %rsp,%rdi
    +0x1330: call    <mldsa_keccakf1600_permute>
    +0x1335: movups  0x770(%r15),%xmm0
    +0x133d: xorps   (%rsp),%xmm0
    +0x1341: movaps  %xmm0,(%rsp)
    +0x1345: movups  0x780(%r15),%xmm0
    +0x134d: xorps   0x10(%rsp),%xmm0
    +0x1352: movaps  %xmm0,0x10(%rsp)
    +0x1357: movups  0x790(%r15),%xmm0
    +0x135f: xorps   0x20(%rsp),%xmm0
    +0x1364: movaps  %xmm0,0x20(%rsp)
    +0x1369: xorb    $0x1f,0x30(%rsp)
    +0x136e: xorb    $0x80,0x87(%rsp)
    +0x1376: movl    $0x88,0xc8(%rsp)
    +0x1381: mov     %rsp,%rdi
    +0x1384: call    <mldsa_keccakf1600_permute>
    +0x1389: movaps  (%rsp),%xmm0
    +0x138d: movaps  0x10(%rsp),%xmm1
    +0x1392: movaps  0x20(%rsp),%xmm2
    +0x1397: movaps  0x30(%rsp),%xmm3
    +0x139c: movaps  %xmm3,0x150(%rsp)
    +0x13a4: movaps  %xmm2,0x140(%rsp)
    +0x13ac: movaps  %xmm1,0x130(%rsp)
    +0x13b4: movaps  %xmm0,0x120(%rsp)
    +0x13bc: xorps   %xmm0,%xmm0
    +0x13bf: movaps  %xmm0,0x40(%rsp)
    +0x13c4: movaps  %xmm0,0x50(%rsp)
    +0x13c9: movaps  %xmm0,0x60(%rsp)
    +0x13ce: movaps  %xmm0,0x70(%rsp)
    +0x13d3: movaps  %xmm0,0x80(%rsp)
    +0x13db: movaps  %xmm0,0x90(%rsp)
    +0x13e3: movaps  %xmm0,0xa0(%rsp)
    +0x13eb: movaps  %xmm0,0xb0(%rsp)
    +0x13f3: movaps  %xmm0,0xc0(%rsp)
    +0x13fb: movaps  %xmm0,(%rsp)
    +0x13ff: movaps  %xmm0,0x10(%rsp)
    +0x1404: movaps  %xmm0,0x20(%rsp)
    +0x1409: movaps  %xmm0,0x30(%rsp)
    +0x140e: mov     %rsp,%rax
    +0x1411: movdqa  0x120(%rsp),%xmm3
    +0x141a: movdqa  0x130(%rsp),%xmm2
    +0x1423: movdqa  0x140(%rsp),%xmm1
    +0x142c: movdqa  0x150(%rsp),%xmm0
    +0x1435: pxor    0x160(%rsp),%xmm3
    +0x143e: pxor    0x170(%rsp),%xmm2
    +0x1447: pxor    0x180(%rsp),%xmm1
    +0x1450: pxor    0x190(%rsp),%xmm0
    +0x1459: mov     0x108(%rsp),%rdx
    +0x1461: xor     0xd0(%rsp),%dl
    +0x1468: movdqa  %xmm1,%xmm4
    +0x146c: por     %xmm3,%xmm4
    +0x1470: pxor    %xmm3,%xmm1
    +0x1474: movdqa  %xmm2,%xmm3
    +0x1478: por     %xmm0,%xmm3
    +0x147c: por     %xmm4,%xmm3
    +0x1480: pshufd  $0xee,%xmm3,%xmm4
    +0x1485: por     %xmm3,%xmm4
    +0x1489: pshufd  $0x55,%xmm4,%xmm3
    +0x148e: por     %xmm4,%xmm3
    +0x1492: movdqa  %xmm3,%xmm4
    +0x1496: psrld   $0x10,%xmm4
    +0x149b: por     %xmm3,%xmm4
    +0x149f: movdqa  %xmm4,%xmm3
    +0x14a3: psrlw   $0x8,%xmm3
    +0x14a8: por     %xmm4,%xmm3
    +0x14ac: movd    %xmm3,%eax
    +0x14b0: pxor    %xmm2,%xmm0
    +0x14b4: pxor    %xmm1,%xmm0
    +0x14b8: pshufd  $0xee,%xmm0,%xmm1
    +0x14bd: pxor    %xmm0,%xmm1
    +0x14c1: pshufd  $0x55,%xmm1,%xmm0
    +0x14c6: pxor    %xmm1,%xmm0
    +0x14ca: movdqa  %xmm0,%xmm1
    +0x14ce: psrld   $0x10,%xmm1
    +0x14d3: pxor    %xmm0,%xmm1
    +0x14d7: movdqa  %xmm1,%xmm0
    +0x14db: psrlw   $0x8,%xmm0
    +0x14e0: pxor    %xmm1,%xmm0
    +0x14e4: movd    %xmm0,%ecx
    +0x14e8: movzbl  %al,%eax
    +0x14eb: neg     %rax
    +0x14ee: shr     $0x20,%rax
    +0x14f2: xor     %cl,%al
    +0x14f4: xor     %cl,%al
    +0x14f6: mov     0x118(%rsp),%rcx
    +0x14fe: or      0xd4(%rsp),%ecx
    +0x1505: or      0x110(%rsp),%ecx
    +0x150c: or      %ebx,%r12d
    +0x150f: or      %r13d,%r12d
    +0x1512: or      %ecx,%r12d
    +0x1515: or      %r14d,%r12d
    +0x1518: or      %al,%r12b
    +0x151b: or      %dl,%r12b
    +0x151e: test    %r12b,%r12b
    +0x1521: je      <mldsa65_pk_from_sk+0x1539>
    +0x1523: mov     $0x7a0,%edx
    +0x1528: mov     %r15,%rdi
    +0x152b: xor     %esi,%esi
    +0x152d: call    <memset>
    +0x1532: mov     $0xfffffff9,%ebx
    +0x1537: jmp     <mldsa65_pk_from_sk+0x153b>
    +0x1539: xor     %ebx,%ebx
    +0x153b: lea     0x19c0(%rsp),%r14
    +0x1543: mov     $0x9c0,%edx
    +0x1548: mov     %r14,%rdi
    +0x154b: xor     %esi,%esi
    +0x154d: call    <memset>
    +0x1552: lea     0x1c0(%rsp),%r14
    +0x155a: mov     $0x400,%edx
    +0x155f: mov     %r14,%rdi
    +0x1562: xor     %esi,%esi
    +0x1564: call    <memset>
    +0x1569: lea     0x5c0(%rsp),%r14
    +0x1571: mov     $0x1400,%edx
    +0x1576: mov     %r14,%rdi
    +0x1579: xor     %esi,%esi
    +0x157b: call    <memset>
    +0x1580: pxor    %xmm0,%xmm0
    +0x1584: movdqa  %xmm0,0x1b0(%rsp)
    +0x158d: movdqa  %xmm0,0x1a0(%rsp)
    +0x1596: lea     0x1a0(%rsp),%rax
    +0x159e: movdqa  %xmm0,0x150(%rsp)
    +0x15a7: movdqa  %xmm0,0x140(%rsp)
    +0x15b0: movdqa  %xmm0,0x130(%rsp)
    +0x15b9: movdqa  %xmm0,0x120(%rsp)
    +0x15c2: lea     0x120(%rsp),%rax
    +0x15ca: movdqa  %xmm0,0x190(%rsp)
    +0x15d3: movdqa  %xmm0,0x180(%rsp)
    +0x15dc: movdqa  %xmm0,0x170(%rsp)
    +0x15e5: movdqa  %xmm0,0x160(%rsp)
    +0x15ee: lea     0x160(%rsp),%rax
    +0x15f6: movdqa  %xmm0,0xf0(%rsp)
    +0x15ff: movdqa  %xmm0,0xe0(%rsp)
    +0x1608: lea     0xe0(%rsp),%rax
    +0x1610: mov     %ebx,%eax
    +0x1612: lea     -0x28(%rbp),%rsp
    +0x1616: pop     %rbx
    +0x1617: pop     %r12
    +0x1619: pop     %r13
    +0x161b: pop     %r14
    +0x161d: pop     %r15
    +0x161f: pop     %rbp
    +0x1620: xor     %ecx,%ecx
    +0x1622: xor     %edi,%edi
    +0x1624: xor     %edx,%edx
    +0x1626: xor     %esi,%esi
    +0x1628: xor     %r8d,%r8d
    +0x162b: ret     
 ***)

let MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa65_pk_from_sk";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The secret key at sk is the 4032 bytes skb; if it passes the *)
(* checks, mld_pk_from_sk_valid, the public key at pk becomes                *)
(* mld_pk_from_sk_pk and the result is 0, and otherwise the public key is    *)
(* zeroed and the result is MLD_ERR_INVALID_KEY (-7 as a 32-bit integer).    *)
(* The expansion of the matrix from rho is assumed to terminate. The         *)
(* function saves RBP, the frame pointer, and five more registers below the  *)
(* return address, lowers RSP by up to 31 bytes to align it to 32 bytes, and *)
(* then reserves its frame, below which the call of mld_compute_pack_t0_t165 *)
(* uses 4901 bytes, with its return address: 14108 bytes of stack below the  *)
(* return address in all.                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !pk sk skb pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
        nonoverlapping (pk,1952) (word_sub stackpointer (word 14108),14108) /\
        ALLPAIRS nonoverlapping
         [(pk,1952); (word_sub stackpointer (word 14108),14108)]
         [(sk,4032); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        nonoverlapping (pk,1952) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_pk_from_sk) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pk; sk] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  (!j. j < 4032
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           skb j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                  (if mld_pk_from_sk_valid 6 5 4 mld_polyeta_unpack_4 128
                        skb
                   then word 0 else word 4294967289) /\
                  (!j. j < 1952
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           if mld_pk_from_sk_valid 6 5 4
                                mld_polyeta_unpack_4 128 skb
                           then mld_pk_from_sk_pk 5 mld_polyeta_unpack_4 128
                                 skb j
                           else word 0))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,1952);
                memory :> bytes(word_sub stackpointer (word 14108),14108)])`;;

let MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the result of the checks and *)
(* the stack, with all accesses within the arguments, the stack, the return  *)
(* address and the constants of the callees, and the writes within the       *)
(* public key and the stack.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e pk sk skb pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
        nonoverlapping (pk,1952) (word_sub stackpointer (word 14108),14108) /\
        ALLPAIRS nonoverlapping
         [(pk,1952); (word_sub stackpointer (word 14108),14108)]
         [(sk,4032); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        nonoverlapping (pk,1952) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_pk_from_sk) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pk; sk] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  (!j. j < 4032
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           skb j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                  (if mld_pk_from_sk_valid 6 5 4 mld_polyeta_unpack_4 128
                        skb
                   then word 0 else word 4294967289) /\
                  (!j. j < 1952
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           if mld_pk_from_sk_valid 6 5 4
                                mld_polyeta_unpack_4 128 skb
                           then mld_pk_from_sk_pk 5 mld_polyeta_unpack_4 128
                                 skb j
                           else word 0) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events pk sk (mld_sk_rho skb)
                            (mld_pk_from_sk_valid 6 5 4 mld_polyeta_unpack_4
                              128 skb)
                            mf mc pc (word_sub stackpointer (word 14108))
                            returnaddress /\
                     memaccess_inbounds e2
                      [sk,4032; pk,1952;
                       word_sub stackpointer (word 14108),14108;
                       stackpointer,8; word(pc + got_memset),8;
                       word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_ntt_consts),256;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word(pc + mld_compute_pack_t0_t165_consts),768;
                       word(pc + mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32;
                       word(pc + mldsa65_keypair_internal_consts),96;
                       word(pc + mldsa65_pk_from_sk_consts),32]
                      [pk,1952; word_sub stackpointer (word 14108),14108]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,1952);
                memory :> bytes(word_sub stackpointer (word 14108),14108)])`;;

let MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e pk sk skb pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
        nonoverlapping (pk,1952) (word_sub stackpointer (word 14108),14108) /\
        ALLPAIRS nonoverlapping
         [(pk,1952); (word_sub stackpointer (word 14108),14108)]
         [(sk,4032); (word pc,libmldsa_size);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
        nonoverlapping (pk,1952) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_pk_from_sk) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [pk; sk] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  (!j. j < 4032
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           skb j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events pk sk (mld_sk_rho skb)
                            (mld_pk_from_sk_valid 6 5 4 mld_polyeta_unpack_4
                              128 skb)
                            mf mc pc (word_sub stackpointer (word 14108))
                            returnaddress /\
                     memaccess_inbounds e2
                      [sk,4032; pk,1952;
                       word_sub stackpointer (word 14108),14108;
                       stackpointer,8; word(pc + got_memset),8;
                       word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_ntt_consts),256;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word(pc + mld_compute_pack_t0_t165_consts),768;
                       word(pc + mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32;
                       word(pc + mldsa65_keypair_internal_consts),96;
                       word(pc + mldsa65_pk_from_sk_consts),32]
                      [pk,1952; word_sub stackpointer (word 14108),14108]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(pk,1952);
                memory :> bytes(word_sub stackpointer (word 14108),14108)])`;;

let MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
