(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing: the statement. This is the code for mldsa87_signature_internal   *)
(* (mld_sign_signature_internal in sign.c, with                              *)
(* mld_attempt_signature_generation and mld_compute_pack_z inlined) from     *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3    *)
(* and MLD_CONFIG_REDUCE_RAM as one translation unit (see                    *)
(* mldsa_native/README.md), which aligns its stack frame to 32 bytes,        *)
(* unpacks the secret key, computes mu (or takes it from m if ext is         *)
(* nonzero) and rho'', and makes up to 16382 attempts: each samples y,       *)
(* computes w = A y and its packed w1, c~ and the challenge, then z,         *)
(* checking and packing each polynomial, and for each row checks w0 - c s2   *)
(* and c t0, and finally packs c~ and the hints, rejecting at the first      *)
(* check that fails. It returns 0 with the signature of the first attempt    *)
(* that succeeds, or -4 (MLD_ERR_SIGN_ATTEMPTS_EXHAUSTED) with the signature *)
(* zeroed, and zeroes its buffers. Clang has inlined most of its callees; it *)
(* still calls mld_H87, mldsa87_poly_challenge, mldsa_poly_uniform,          *)
(* mldsa_poly_ntt, mldsa_poly_invntt_tomont and mldsa_keccakf1600_permute,   *)
(* and memcpy and memset through the PLT, so the direction flag must be      *)
(* clear, as the ABI requires on entry. It is verified in the whole image    *)
(* (see libmldsa.ml) against mld_sign_ok and mld_sign_sig of                 *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and the   *)
(* contracts memset_full_contract and memcpy_full_contract of                *)
(* utils/mldsa_native_libc.ml for the C library functions, assuming that the *)
(* expansion of the matrix and the sampling of the challenge in each attempt *)
(* terminate, and shown to be constant time and memory safe, with the events *)
(* depending only on public values and those that the C code declassifies    *)
(* (mld_sign_declass).                                                       *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/H_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_challenge_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa87_signature_internal:
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
      +0x2f: sub     $0x1000,%rsp
      +0x36: movq    $0x0,(%rsp)
      +0x3e: sub     $0xa60,%rsp
      +0x45: mov     %r9,%rbx
      +0x48: mov     %rsi,%r9
      +0x4b: mov     %rdi,0x20(%rsp)
      +0x50: mov     0x10(%rbp),%rax
      +0x54: lea     0x2a0(%rsp),%r15
      +0x5c: lea     0x2c0(%rsp),%r12
      +0x64: movups  (%rax),%xmm0
      +0x67: movups  0x10(%rax),%xmm1
      +0x6b: movaps  %xmm1,0x250(%rsp)
      +0x73: movaps  %xmm0,0x240(%rsp)
      +0x7b: movups  0x20(%rax),%xmm0
      +0x7f: movups  0x30(%rax),%xmm1
      +0x83: movaps  %xmm0,0x2a0(%rsp)
      +0x8b: movaps  %xmm1,0x2b0(%rsp)
      +0x93: movups  0x40(%rax),%xmm0
      +0x97: movups  0x50(%rax),%xmm1
      +0x9b: movdqu  0x60(%rax),%xmm2
      +0xa0: movdqu  0x70(%rax),%xmm3
      +0xa5: movdqa  %xmm2,0x280(%rsp)
      +0xae: movaps  %xmm1,0x270(%rsp)
      +0xb6: movaps  %xmm0,0x260(%rsp)
      +0xbe: movdqa  %xmm3,0x290(%rsp)
      +0xc7: lea     0x80(%rax),%rsi
      +0xce: mov     %rsi,0x80(%rsp)
      +0xd6: lea     0x320(%rax),%rsi
      +0xdd: mov     %rsi,0x40(%rsp)
      +0xe2: add     $0x620,%rax
      +0xe8: mov     %rax,0x60(%rsp)
      +0xed: cmpl    $0x0,0x18(%rbp)
      +0xf1: je      <mldsa87_signature_internal+0x123>
      +0xf3: movups  (%r9),%xmm0
      +0xf7: movups  0x10(%r9),%xmm1
      +0xfc: movdqu  0x20(%r9),%xmm2
     +0x102: movdqu  0x30(%r9),%xmm3
     +0x108: movdqa  %xmm3,0x30(%r12)
     +0x10f: movdqa  %xmm2,0x20(%r12)
     +0x116: movaps  %xmm1,0x10(%r12)
     +0x11c: movaps  %xmm0,(%r12)
     +0x121: jmp     <mldsa87_signature_internal+0x13c>
     +0x123: lea     0x260(%rsp),%rsi
     +0x12b: mov     %rdx,(%rsp)
     +0x12f: mov     $0x40,%edx
     +0x134: mov     %r12,%rdi
     +0x137: call    <mld_H87>
     +0x13c: movq    $0x40,(%rsp)
     +0x144: mov     $0x20,%edx
     +0x149: mov     $0x20,%r8d
     +0x14f: lea     0x300(%rsp),%rdi
     +0x157: mov     %r15,%rsi
     +0x15a: mov     %rbx,%rcx
     +0x15d: mov     %r12,%r9
     +0x160: call    <mld_H87>
     +0x165: movdqa  0x240(%rsp),%xmm0
     +0x16e: movdqa  0x250(%rsp),%xmm1
     +0x177: movdqa  %xmm1,0x1350(%rsp)
     +0x180: movdqa  %xmm0,0x1340(%rsp)
     +0x189: mov     0x20(%rsp),%rax
     +0x18e: lea     0x11c0(%rax),%rcx
     +0x195: mov     %rcx,0x28(%rsp)
     +0x19a: pxor    %xmm4,%xmm4
     +0x19e: add     $0x43,%rax
     +0x1a2: mov     %rax,0x190(%rsp)
     +0x1aa: xor     %ecx,%ecx
     +0x1ac: nopl    0x0(%rax)
     +0x1b0: lea     0x0(,%rcx,8),%eax
     +0x1b7: mov     %rcx,0x198(%rsp)
     +0x1bf: sub     %ecx,%eax
     +0x1c1: lea     0x300(%rsp),%rcx
     +0x1c9: mov     %rcx,0xa0(%rsp)
     +0x1d1: mov     %ax,0xa8(%rsp)
     +0x1d9: lea     0x1340(%rsp),%rax
     +0x1e1: movaps  (%rax),%xmm0
     +0x1e4: movaps  0x10(%rax),%xmm1
     +0x1e8: movaps  %xmm1,0xd0(%rsp)
     +0x1f0: movaps  %xmm0,0xc0(%rsp)
     +0x1f8: xor     %r15d,%r15d
     +0x1fb: jmp     <mldsa87_signature_internal+0x20d>
     +0x1fd: nopl    (%rax)
     +0x200: inc     %r15d
     +0x203: cmp     $0x7,%r15d
     +0x207: je      <mldsa87_signature_internal+0x13a0>
     +0x20d: mov     0xa0(%rsp),%rax
     +0x215: movzwl  0xa8(%rsp),%ecx
     +0x21d: mov     %r15d,0x38(%rsp)
     +0x222: add     %r15w,%cx
     +0x226: movups  (%rax),%xmm0
     +0x229: movups  0x10(%rax),%xmm1
     +0x22d: movups  0x20(%rax),%xmm2
     +0x231: movups  0x30(%rax),%xmm3
     +0x235: movaps  %xmm0,0x1360(%rsp)
     +0x23d: movaps  %xmm1,0x1370(%rsp)
     +0x245: movaps  %xmm2,0x1380(%rsp)
     +0x24d: movaps  %xmm3,0x1390(%rsp)
     +0x255: mov     %cx,0x13a0(%rsp)
     +0x25d: movdqa  %xmm4,0xb40(%rsp)
     +0x266: movdqa  %xmm4,0xb50(%rsp)
     +0x26f: movdqa  %xmm4,0xb60(%rsp)
     +0x278: movdqa  %xmm4,0xb70(%rsp)
     +0x281: movdqa  %xmm4,0xb80(%rsp)
     +0x28a: movdqa  %xmm4,0xb90(%rsp)
     +0x293: movdqa  %xmm4,0xba0(%rsp)
     +0x29c: movdqa  %xmm4,0xbb0(%rsp)
     +0x2a5: movdqa  %xmm4,0xbc0(%rsp)
     +0x2ae: movdqa  %xmm4,0xbd0(%rsp)
     +0x2b7: movdqa  %xmm4,0xbe0(%rsp)
     +0x2c0: movdqa  %xmm4,0xbf0(%rsp)
     +0x2c9: movdqu  %xmm4,0xbfc(%rsp)
     +0x2d2: movdqa  0x1360(%rsp),%xmm0
     +0x2db: movdqa  0xb50(%rsp),%xmm1
     +0x2e4: movdqa  0xb60(%rsp),%xmm2
     +0x2ed: movdqa  0xb70(%rsp),%xmm3
     +0x2f6: pxor    0x1370(%rsp),%xmm1
     +0x2ff: movdqa  0xb80(%rsp),%xmm4
     +0x308: movdqa  %xmm0,0xb40(%rsp)
     +0x311: pxor    0x1380(%rsp),%xmm2
     +0x31a: movdqa  %xmm1,0xb50(%rsp)
     +0x323: pxor    0x1390(%rsp),%xmm3
     +0x32c: movdqa  %xmm2,0xb60(%rsp)
     +0x335: movdqa  %xmm3,0xb70(%rsp)
     +0x33e: pxor    0x13a0(%rsp),%xmm4
     +0x347: movd    %xmm4,%eax
     +0x34b: mov     %ax,0xb80(%rsp)
     +0x353: xorb    $0x1f,0xb82(%rsp)
     +0x35b: xorb    $0x80,0xbc7(%rsp)
     +0x363: movl    $0x88,0xc08(%rsp)
     +0x36e: mov     $0x88,%r15d
     +0x374: mov     $0x2a8,%r12d
     +0x37a: xor     %r13d,%r13d
     +0x37d: jmp     <mldsa87_signature_internal+0x3bb>
     +0x37f: nop     
     +0x380: mov     $0x88,%ebx
     +0x385: sub     %r15d,%ebx
     +0x388: cmp     %rbx,%r12
     +0x38b: cmovb   %r12,%rbx
     +0x38f: mov     %r15d,%eax
     +0x392: lea     (%rsp,%rax,1),%rsi
     +0x396: add     $0xb40,%rsi
     +0x39d: lea     (%rsp,%r13,1),%rdi
     +0x3a1: add     $0x740,%rdi
     +0x3a8: mov     %rbx,%rdx
     +0x3ab: call    <memcpy>
     +0x3b0: add     %ebx,%r15d
     +0x3b3: add     %rbx,%r13
     +0x3b6: sub     %rbx,%r12
     +0x3b9: je      <mldsa87_signature_internal+0x3f0>
     +0x3bb: cmp     $0x88,%r15d
     +0x3c2: jne     <mldsa87_signature_internal+0x380>
     +0x3c4: lea     0xb40(%rsp),%r14
     +0x3cc: mov     %r14,%rdi
     +0x3cf: call    <mldsa_keccakf1600_permute>
     +0x3d4: cmp     $0x88,%r12
     +0x3db: mov     $0x88,%ebx
     +0x3e0: cmovb   %r12,%rbx
     +0x3e4: xor     %r15d,%r15d
     +0x3e7: mov     %r14,%rsi
     +0x3ea: jmp     <mldsa87_signature_internal+0x39d>
     +0x3ec: nopl    0x0(%rax)
     +0x3f0: lea     0x744(%rsp),%rax
     +0x3f8: xor     %ecx,%ecx
     +0x3fa: lea     0xf40(%rsp),%r14
     +0x402: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x410: movzwl  -0x4(%rax),%edx
     +0x414: movzbl  -0x2(%rax),%esi
     +0x418: mov     %esi,%edi
     +0x41a: and     $0xf,%edi
     +0x41d: shl     $0x10,%edi
     +0x420: or      %edx,%edi
     +0x422: shr     $0x4,%esi
     +0x425: movzbl  -0x1(%rax),%edx
     +0x429: movzbl  (%rax),%r8d
     +0x42d: mov     $0x80000,%r9d
     +0x433: sub     %edi,%r9d
     +0x436: mov     %r9d,0x340(%rsp,%rcx,8)
     +0x43e: shl     $0xc,%r8d
     +0x442: shl     $0x4,%edx
     +0x445: or      %esi,%edx
     +0x447: or      %r8d,%edx
     +0x44a: mov     $0x80000,%esi
     +0x44f: sub     %edx,%esi
     +0x451: mov     %esi,0x344(%rsp,%rcx,8)
     +0x458: inc     %rcx
     +0x45b: add     $0x5,%rax
     +0x45f: cmp     $0x80,%rcx
     +0x466: jne     <mldsa87_signature_internal+0x410>
     +0x468: pxor    %xmm0,%xmm0
     +0x46c: movdqa  %xmm0,0xc00(%rsp)
     +0x475: movdqa  %xmm0,0xbf0(%rsp)
     +0x47e: movdqa  %xmm0,0xbe0(%rsp)
     +0x487: movdqa  %xmm0,0xbd0(%rsp)
     +0x490: movdqa  %xmm0,0xbc0(%rsp)
     +0x499: movdqa  %xmm0,0xbb0(%rsp)
     +0x4a2: movdqa  %xmm0,0xba0(%rsp)
     +0x4ab: movdqa  %xmm0,0xb90(%rsp)
     +0x4b4: movdqa  %xmm0,0xb80(%rsp)
     +0x4bd: movdqa  %xmm0,0xb70(%rsp)
     +0x4c6: movdqa  %xmm0,0xb60(%rsp)
     +0x4cf: movdqa  %xmm0,0xb50(%rsp)
     +0x4d8: movdqa  %xmm0,0xb40(%rsp)
     +0x4e1: lea     0xb40(%rsp),%rax
     +0x4e9: mov     $0x2a8,%edx
     +0x4ee: lea     0x740(%rsp),%rbx
     +0x4f6: mov     %rbx,%rdi
     +0x4f9: xor     %esi,%esi
     +0x4fb: call    <memset>
     +0x500: pxor    %xmm0,%xmm0
     +0x504: movdqa  %xmm0,0x1390(%rsp)
     +0x50d: movdqa  %xmm0,0x1380(%rsp)
     +0x516: movdqa  %xmm0,0x1370(%rsp)
     +0x51f: movdqa  %xmm0,0x1360(%rsp)
     +0x528: movw    $0x0,0x13a0(%rsp)
     +0x532: lea     0x1360(%rsp),%rax
     +0x53a: lea     0x340(%rsp),%rdi
     +0x542: call    <mldsa_poly_ntt>
     +0x547: mov     0x38(%rsp),%r15d
     +0x54c: test    %r15d,%r15d
     +0x54f: movabs  $0x380200100000000,%rbx
     +0x559: je      <mldsa87_signature_internal+0xe80>
     +0x55f: mov     %r15b,0xe0(%rsp)
     +0x567: movb    $0x0,0xe1(%rsp)
     +0x56f: mov     %r14,%rdi
     +0x572: lea     0xc0(%rsp),%rsi
     +0x57a: call    <mldsa_poly_uniform>
     +0x57f: mov     $0x1,%eax
     +0x584: data16  data16 cs nopw 0x0(%rax,%rax,1)
     +0x590: movslq  0xf3c(%rsp,%rax,4),%rcx
     +0x598: movslq  0x33c(%rsp,%rax,4),%rdx
     +0x5a0: imul    %rcx,%rdx
     +0x5a4: mov     %rdx,%rcx
     +0x5a7: imul    %rbx,%rcx
     +0x5ab: sar     $0x20,%rcx
     +0x5af: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x5b6: add     %rdx,%rcx
     +0x5b9: shr     $0x20,%rcx
     +0x5bd: mov     %ecx,0xf3c(%rsp,%rax,4)
     +0x5c4: movslq  0xf40(%rsp,%rax,4),%rcx
     +0x5cc: movslq  0x340(%rsp,%rax,4),%rdx
     +0x5d4: imul    %rcx,%rdx
     +0x5d8: mov     %rdx,%rcx
     +0x5db: imul    %rbx,%rcx
     +0x5df: sar     $0x20,%rcx
     +0x5e3: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x5ea: add     %rdx,%rcx
     +0x5ed: shr     $0x20,%rcx
     +0x5f1: mov     %ecx,0xf40(%rsp,%rax,4)
     +0x5f8: add     $0x2,%rax
     +0x5fc: cmp     $0x101,%rax
     +0x602: jne     <mldsa87_signature_internal+0x590>
     +0x604: mov     $0xc,%eax
     +0x609: nopl    0x0(%rax)
     +0x610: movdqa  0xf10(%rsp,%rax,4),%xmm0
     +0x619: movdqa  0xf20(%rsp,%rax,4),%xmm1
     +0x622: movdqa  0xf30(%rsp,%rax,4),%xmm2
     +0x62b: movdqa  0xf40(%rsp,%rax,4),%xmm3
     +0x634: paddd   0x19f0(%rsp,%rax,4),%xmm0
     +0x63d: paddd   0x1a00(%rsp,%rax,4),%xmm1
     +0x646: movdqa  %xmm0,0x19f0(%rsp,%rax,4)
     +0x64f: movdqa  %xmm1,0x1a00(%rsp,%rax,4)
     +0x658: paddd   0x1a10(%rsp,%rax,4),%xmm2
     +0x661: paddd   0x1a20(%rsp,%rax,4),%xmm3
     +0x66a: movdqa  %xmm2,0x1a10(%rsp,%rax,4)
     +0x673: movdqa  %xmm3,0x1a20(%rsp,%rax,4)
     +0x67c: add     $0x10,%rax
     +0x680: cmp     $0x10c,%rax
     +0x686: jne     <mldsa87_signature_internal+0x610>
     +0x688: mov     %r15b,0xe0(%rsp)
     +0x690: movb    $0x1,0xe1(%rsp)
     +0x698: mov     %r14,%rdi
     +0x69b: lea     0xc0(%rsp),%rsi
     +0x6a3: call    <mldsa_poly_uniform>
     +0x6a8: mov     $0x1,%eax
     +0x6ad: nopl    (%rax)
     +0x6b0: movslq  0xf3c(%rsp,%rax,4),%rcx
     +0x6b8: movslq  0x33c(%rsp,%rax,4),%rdx
     +0x6c0: imul    %rcx,%rdx
     +0x6c4: mov     %rdx,%rcx
     +0x6c7: imul    %rbx,%rcx
     +0x6cb: sar     $0x20,%rcx
     +0x6cf: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x6d6: add     %rdx,%rcx
     +0x6d9: shr     $0x20,%rcx
     +0x6dd: mov     %ecx,0xf3c(%rsp,%rax,4)
     +0x6e4: movslq  0xf40(%rsp,%rax,4),%rcx
     +0x6ec: movslq  0x340(%rsp,%rax,4),%rdx
     +0x6f4: imul    %rcx,%rdx
     +0x6f8: mov     %rdx,%rcx
     +0x6fb: imul    %rbx,%rcx
     +0x6ff: sar     $0x20,%rcx
     +0x703: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x70a: add     %rdx,%rcx
     +0x70d: shr     $0x20,%rcx
     +0x711: mov     %ecx,0xf40(%rsp,%rax,4)
     +0x718: add     $0x2,%rax
     +0x71c: cmp     $0x101,%rax
     +0x722: jne     <mldsa87_signature_internal+0x6b0>
     +0x724: mov     $0xc,%eax
     +0x729: nopl    0x0(%rax)
     +0x730: movdqa  0xf10(%rsp,%rax,4),%xmm0
     +0x739: movdqa  0xf20(%rsp,%rax,4),%xmm1
     +0x742: movdqa  0xf30(%rsp,%rax,4),%xmm2
     +0x74b: movdqa  0xf40(%rsp,%rax,4),%xmm3
     +0x754: paddd   0x1df0(%rsp,%rax,4),%xmm0
     +0x75d: paddd   0x1e00(%rsp,%rax,4),%xmm1
     +0x766: movdqa  %xmm0,0x1df0(%rsp,%rax,4)
     +0x76f: movdqa  %xmm1,0x1e00(%rsp,%rax,4)
     +0x778: paddd   0x1e10(%rsp,%rax,4),%xmm2
     +0x781: paddd   0x1e20(%rsp,%rax,4),%xmm3
     +0x78a: movdqa  %xmm2,0x1e10(%rsp,%rax,4)
     +0x793: movdqa  %xmm3,0x1e20(%rsp,%rax,4)
     +0x79c: add     $0x10,%rax
     +0x7a0: cmp     $0x10c,%rax
     +0x7a6: jne     <mldsa87_signature_internal+0x730>
     +0x7a8: mov     %r15b,0xe0(%rsp)
     +0x7b0: movb    $0x2,0xe1(%rsp)
     +0x7b8: mov     %r14,%rdi
     +0x7bb: lea     0xc0(%rsp),%rsi
     +0x7c3: call    <mldsa_poly_uniform>
     +0x7c8: mov     $0x1,%eax
     +0x7cd: nopl    (%rax)
     +0x7d0: movslq  0xf3c(%rsp,%rax,4),%rcx
     +0x7d8: movslq  0x33c(%rsp,%rax,4),%rdx
     +0x7e0: imul    %rcx,%rdx
     +0x7e4: mov     %rdx,%rcx
     +0x7e7: imul    %rbx,%rcx
     +0x7eb: sar     $0x20,%rcx
     +0x7ef: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x7f6: add     %rdx,%rcx
     +0x7f9: shr     $0x20,%rcx
     +0x7fd: mov     %ecx,0xf3c(%rsp,%rax,4)
     +0x804: movslq  0xf40(%rsp,%rax,4),%rcx
     +0x80c: movslq  0x340(%rsp,%rax,4),%rdx
     +0x814: imul    %rcx,%rdx
     +0x818: mov     %rdx,%rcx
     +0x81b: imul    %rbx,%rcx
     +0x81f: sar     $0x20,%rcx
     +0x823: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x82a: add     %rdx,%rcx
     +0x82d: shr     $0x20,%rcx
     +0x831: mov     %ecx,0xf40(%rsp,%rax,4)
     +0x838: add     $0x2,%rax
     +0x83c: cmp     $0x101,%rax
     +0x842: jne     <mldsa87_signature_internal+0x7d0>
     +0x844: xor     %eax,%eax
     +0x846: cs      nopw 0x0(%rax,%rax,1)
     +0x850: movdqa  0xf40(%rsp,%rax,4),%xmm0
     +0x859: movdqa  0xf50(%rsp,%rax,4),%xmm1
     +0x862: movdqa  0xf60(%rsp,%rax,4),%xmm2
     +0x86b: movdqa  0xf70(%rsp,%rax,4),%xmm3
     +0x874: paddd   0x2220(%rsp,%rax,4),%xmm0
     +0x87d: paddd   0x2230(%rsp,%rax,4),%xmm1
     +0x886: movdqa  %xmm0,0x2220(%rsp,%rax,4)
     +0x88f: movdqa  %xmm1,0x2230(%rsp,%rax,4)
     +0x898: paddd   0x2240(%rsp,%rax,4),%xmm2
     +0x8a1: paddd   0x2250(%rsp,%rax,4),%xmm3
     +0x8aa: movdqa  %xmm2,0x2240(%rsp,%rax,4)
     +0x8b3: movdqa  %xmm3,0x2250(%rsp,%rax,4)
     +0x8bc: add     $0x10,%rax
     +0x8c0: cmp     $0x100,%rax
     +0x8c6: jne     <mldsa87_signature_internal+0x850>
     +0x8c8: mov     %r15b,0xe0(%rsp)
     +0x8d0: movb    $0x3,0xe1(%rsp)
     +0x8d8: mov     %r14,%rdi
     +0x8db: lea     0xc0(%rsp),%rsi
     +0x8e3: call    <mldsa_poly_uniform>
     +0x8e8: mov     $0x1,%eax
     +0x8ed: nopl    (%rax)
     +0x8f0: movslq  0xf3c(%rsp,%rax,4),%rcx
     +0x8f8: movslq  0x33c(%rsp,%rax,4),%rdx
     +0x900: imul    %rcx,%rdx
     +0x904: mov     %rdx,%rcx
     +0x907: imul    %rbx,%rcx
     +0x90b: sar     $0x20,%rcx
     +0x90f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x916: add     %rdx,%rcx
     +0x919: shr     $0x20,%rcx
     +0x91d: mov     %ecx,0xf3c(%rsp,%rax,4)
     +0x924: movslq  0xf40(%rsp,%rax,4),%rcx
     +0x92c: movslq  0x340(%rsp,%rax,4),%rdx
     +0x934: imul    %rcx,%rdx
     +0x938: mov     %rdx,%rcx
     +0x93b: imul    %rbx,%rcx
     +0x93f: sar     $0x20,%rcx
     +0x943: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x94a: add     %rdx,%rcx
     +0x94d: shr     $0x20,%rcx
     +0x951: mov     %ecx,0xf40(%rsp,%rax,4)
     +0x958: add     $0x2,%rax
     +0x95c: cmp     $0x101,%rax
     +0x962: jne     <mldsa87_signature_internal+0x8f0>
     +0x964: xor     %eax,%eax
     +0x966: cs      nopw 0x0(%rax,%rax,1)
     +0x970: movdqa  0xf40(%rsp,%rax,4),%xmm0
     +0x979: movdqa  0xf50(%rsp,%rax,4),%xmm1
     +0x982: movdqa  0xf60(%rsp,%rax,4),%xmm2
     +0x98b: movdqa  0xf70(%rsp,%rax,4),%xmm3
     +0x994: paddd   0x2620(%rsp,%rax,4),%xmm0
     +0x99d: paddd   0x2630(%rsp,%rax,4),%xmm1
     +0x9a6: movdqa  %xmm0,0x2620(%rsp,%rax,4)
     +0x9af: movdqa  %xmm1,0x2630(%rsp,%rax,4)
     +0x9b8: paddd   0x2640(%rsp,%rax,4),%xmm2
     +0x9c1: paddd   0x2650(%rsp,%rax,4),%xmm3
     +0x9ca: movdqa  %xmm2,0x2640(%rsp,%rax,4)
     +0x9d3: movdqa  %xmm3,0x2650(%rsp,%rax,4)
     +0x9dc: add     $0x10,%rax
     +0x9e0: cmp     $0x100,%rax
     +0x9e6: jne     <mldsa87_signature_internal+0x970>
     +0x9e8: mov     %r15b,0xe0(%rsp)
     +0x9f0: movb    $0x4,0xe1(%rsp)
     +0x9f8: mov     %r14,%rdi
     +0x9fb: lea     0xc0(%rsp),%rsi
     +0xa03: call    <mldsa_poly_uniform>
     +0xa08: mov     $0x1,%eax
     +0xa0d: nopl    (%rax)
     +0xa10: movslq  0xf3c(%rsp,%rax,4),%rcx
     +0xa18: movslq  0x33c(%rsp,%rax,4),%rdx
     +0xa20: imul    %rcx,%rdx
     +0xa24: mov     %rdx,%rcx
     +0xa27: imul    %rbx,%rcx
     +0xa2b: sar     $0x20,%rcx
     +0xa2f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xa36: add     %rdx,%rcx
     +0xa39: shr     $0x20,%rcx
     +0xa3d: mov     %ecx,0xf3c(%rsp,%rax,4)
     +0xa44: movslq  0xf40(%rsp,%rax,4),%rcx
     +0xa4c: movslq  0x340(%rsp,%rax,4),%rdx
     +0xa54: imul    %rcx,%rdx
     +0xa58: mov     %rdx,%rcx
     +0xa5b: imul    %rbx,%rcx
     +0xa5f: sar     $0x20,%rcx
     +0xa63: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xa6a: add     %rdx,%rcx
     +0xa6d: shr     $0x20,%rcx
     +0xa71: mov     %ecx,0xf40(%rsp,%rax,4)
     +0xa78: add     $0x2,%rax
     +0xa7c: cmp     $0x101,%rax
     +0xa82: jne     <mldsa87_signature_internal+0xa10>
     +0xa84: xor     %eax,%eax
     +0xa86: cs      nopw 0x0(%rax,%rax,1)
     +0xa90: movdqa  0xf40(%rsp,%rax,4),%xmm0
     +0xa99: movdqa  0xf50(%rsp,%rax,4),%xmm1
     +0xaa2: movdqa  0xf60(%rsp,%rax,4),%xmm2
     +0xaab: movdqa  0xf70(%rsp,%rax,4),%xmm3
     +0xab4: paddd   0x2a20(%rsp,%rax,4),%xmm0
     +0xabd: paddd   0x2a30(%rsp,%rax,4),%xmm1
     +0xac6: movdqa  %xmm0,0x2a20(%rsp,%rax,4)
     +0xacf: movdqa  %xmm1,0x2a30(%rsp,%rax,4)
     +0xad8: paddd   0x2a40(%rsp,%rax,4),%xmm2
     +0xae1: paddd   0x2a50(%rsp,%rax,4),%xmm3
     +0xaea: movdqa  %xmm2,0x2a40(%rsp,%rax,4)
     +0xaf3: movdqa  %xmm3,0x2a50(%rsp,%rax,4)
     +0xafc: add     $0x10,%rax
     +0xb00: cmp     $0x100,%rax
     +0xb06: jne     <mldsa87_signature_internal+0xa90>
     +0xb08: mov     %r15b,0xe0(%rsp)
     +0xb10: movb    $0x5,0xe1(%rsp)
     +0xb18: mov     %r14,%rdi
     +0xb1b: lea     0xc0(%rsp),%rsi
     +0xb23: call    <mldsa_poly_uniform>
     +0xb28: mov     $0x1,%eax
     +0xb2d: nopl    (%rax)
     +0xb30: movslq  0xf3c(%rsp,%rax,4),%rcx
     +0xb38: movslq  0x33c(%rsp,%rax,4),%rdx
     +0xb40: imul    %rcx,%rdx
     +0xb44: mov     %rdx,%rcx
     +0xb47: imul    %rbx,%rcx
     +0xb4b: sar     $0x20,%rcx
     +0xb4f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xb56: add     %rdx,%rcx
     +0xb59: shr     $0x20,%rcx
     +0xb5d: mov     %ecx,0xf3c(%rsp,%rax,4)
     +0xb64: movslq  0xf40(%rsp,%rax,4),%rcx
     +0xb6c: movslq  0x340(%rsp,%rax,4),%rdx
     +0xb74: imul    %rcx,%rdx
     +0xb78: mov     %rdx,%rcx
     +0xb7b: imul    %rbx,%rcx
     +0xb7f: sar     $0x20,%rcx
     +0xb83: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xb8a: add     %rdx,%rcx
     +0xb8d: shr     $0x20,%rcx
     +0xb91: mov     %ecx,0xf40(%rsp,%rax,4)
     +0xb98: add     $0x2,%rax
     +0xb9c: cmp     $0x101,%rax
     +0xba2: jne     <mldsa87_signature_internal+0xb30>
     +0xba4: xor     %eax,%eax
     +0xba6: cs      nopw 0x0(%rax,%rax,1)
     +0xbb0: movdqa  0xf40(%rsp,%rax,4),%xmm0
     +0xbb9: movdqa  0xf50(%rsp,%rax,4),%xmm1
     +0xbc2: movdqa  0xf60(%rsp,%rax,4),%xmm2
     +0xbcb: movdqa  0xf70(%rsp,%rax,4),%xmm3
     +0xbd4: paddd   0x2e20(%rsp,%rax,4),%xmm0
     +0xbdd: paddd   0x2e30(%rsp,%rax,4),%xmm1
     +0xbe6: movdqa  %xmm0,0x2e20(%rsp,%rax,4)
     +0xbef: movdqa  %xmm1,0x2e30(%rsp,%rax,4)
     +0xbf8: paddd   0x2e40(%rsp,%rax,4),%xmm2
     +0xc01: paddd   0x2e50(%rsp,%rax,4),%xmm3
     +0xc0a: movdqa  %xmm2,0x2e40(%rsp,%rax,4)
     +0xc13: movdqa  %xmm3,0x2e50(%rsp,%rax,4)
     +0xc1c: add     $0x10,%rax
     +0xc20: cmp     $0x100,%rax
     +0xc26: jne     <mldsa87_signature_internal+0xbb0>
     +0xc28: mov     %r15b,0xe0(%rsp)
     +0xc30: movb    $0x6,0xe1(%rsp)
     +0xc38: mov     %r14,%rdi
     +0xc3b: lea     0xc0(%rsp),%rsi
     +0xc43: call    <mldsa_poly_uniform>
     +0xc48: mov     $0x1,%eax
     +0xc4d: nopl    (%rax)
     +0xc50: movslq  0xf3c(%rsp,%rax,4),%rcx
     +0xc58: movslq  0x33c(%rsp,%rax,4),%rdx
     +0xc60: imul    %rcx,%rdx
     +0xc64: mov     %rdx,%rcx
     +0xc67: imul    %rbx,%rcx
     +0xc6b: sar     $0x20,%rcx
     +0xc6f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xc76: add     %rdx,%rcx
     +0xc79: shr     $0x20,%rcx
     +0xc7d: mov     %ecx,0xf3c(%rsp,%rax,4)
     +0xc84: movslq  0xf40(%rsp,%rax,4),%rcx
     +0xc8c: movslq  0x340(%rsp,%rax,4),%rdx
     +0xc94: imul    %rcx,%rdx
     +0xc98: mov     %rdx,%rcx
     +0xc9b: imul    %rbx,%rcx
     +0xc9f: sar     $0x20,%rcx
     +0xca3: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xcaa: add     %rdx,%rcx
     +0xcad: shr     $0x20,%rcx
     +0xcb1: mov     %ecx,0xf40(%rsp,%rax,4)
     +0xcb8: add     $0x2,%rax
     +0xcbc: cmp     $0x101,%rax
     +0xcc2: jne     <mldsa87_signature_internal+0xc50>
     +0xcc4: xor     %eax,%eax
     +0xcc6: cs      nopw 0x0(%rax,%rax,1)
     +0xcd0: movdqa  0xf40(%rsp,%rax,4),%xmm0
     +0xcd9: movdqa  0xf50(%rsp,%rax,4),%xmm1
     +0xce2: movdqa  0xf60(%rsp,%rax,4),%xmm2
     +0xceb: movdqa  0xf70(%rsp,%rax,4),%xmm3
     +0xcf4: paddd   0x3220(%rsp,%rax,4),%xmm0
     +0xcfd: paddd   0x3230(%rsp,%rax,4),%xmm1
     +0xd06: movdqa  %xmm0,0x3220(%rsp,%rax,4)
     +0xd0f: movdqa  %xmm1,0x3230(%rsp,%rax,4)
     +0xd18: paddd   0x3240(%rsp,%rax,4),%xmm2
     +0xd21: paddd   0x3250(%rsp,%rax,4),%xmm3
     +0xd2a: movdqa  %xmm2,0x3240(%rsp,%rax,4)
     +0xd33: movdqa  %xmm3,0x3250(%rsp,%rax,4)
     +0xd3c: add     $0x10,%rax
     +0xd40: cmp     $0x100,%rax
     +0xd46: jne     <mldsa87_signature_internal+0xcd0>
     +0xd48: mov     %r15b,0xe0(%rsp)
     +0xd50: movb    $0x7,0xe1(%rsp)
     +0xd58: mov     %r14,%rdi
     +0xd5b: lea     0xc0(%rsp),%rsi
     +0xd63: call    <mldsa_poly_uniform>
     +0xd68: xor     %eax,%eax
     +0xd6a: nopw    0x0(%rax,%rax,1)
     +0xd70: movslq  0xf40(%rsp,%rax,4),%rcx
     +0xd78: movslq  0x340(%rsp,%rax,4),%rdx
     +0xd80: imul    %rcx,%rdx
     +0xd84: mov     %rdx,%rcx
     +0xd87: imul    %rbx,%rcx
     +0xd8b: sar     $0x20,%rcx
     +0xd8f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xd96: add     %rdx,%rcx
     +0xd99: shr     $0x20,%rcx
     +0xd9d: mov     %ecx,0xf40(%rsp,%rax,4)
     +0xda4: movslq  0xf44(%rsp,%rax,4),%rcx
     +0xdac: movslq  0x344(%rsp,%rax,4),%rdx
     +0xdb4: imul    %rcx,%rdx
     +0xdb8: mov     %rdx,%rcx
     +0xdbb: imul    %rbx,%rcx
     +0xdbf: sar     $0x20,%rcx
     +0xdc3: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xdca: add     %rdx,%rcx
     +0xdcd: shr     $0x20,%rcx
     +0xdd1: mov     %ecx,0xf44(%rsp,%rax,4)
     +0xdd8: add     $0x2,%rax
     +0xddc: cmp     $0x100,%rax
     +0xde2: jne     <mldsa87_signature_internal+0xd70>
     +0xde4: xor     %eax,%eax
     +0xde6: pxor    %xmm4,%xmm4
     +0xdea: movdqa  0xbd7e(%rip),%xmm5
     +0xdf2: movdqa  0xbd86(%rip),%xmm6
     +0xdfa: nopw    0x0(%rax,%rax,1)
     +0xe00: movdqa  0xf40(%rsp,%rax,4),%xmm0
     +0xe09: movdqa  0xf50(%rsp,%rax,4),%xmm1
     +0xe12: movdqa  0xf60(%rsp,%rax,4),%xmm2
     +0xe1b: movdqa  0xf70(%rsp,%rax,4),%xmm3
     +0xe24: paddd   0x3620(%rsp,%rax,4),%xmm0
     +0xe2d: paddd   0x3630(%rsp,%rax,4),%xmm1
     +0xe36: movdqa  %xmm0,0x3620(%rsp,%rax,4)
     +0xe3f: movdqa  %xmm1,0x3630(%rsp,%rax,4)
     +0xe48: paddd   0x3640(%rsp,%rax,4),%xmm2
     +0xe51: paddd   0x3650(%rsp,%rax,4),%xmm3
     +0xe5a: movdqa  %xmm2,0x3640(%rsp,%rax,4)
     +0xe63: movdqa  %xmm3,0x3650(%rsp,%rax,4)
     +0xe6c: add     $0x10,%rax
     +0xe70: cmp     $0x100,%rax
     +0xe76: jne     <mldsa87_signature_internal+0xe00>
     +0xe78: jmp     <mldsa87_signature_internal+0x200>
     +0xe7d: nopl    (%rax)
     +0xe80: movw    $0x0,0xe0(%rsp)
     +0xe8a: lea     0x1a20(%rsp),%rdi
     +0xe92: lea     0xc0(%rsp),%rsi
     +0xe9a: call    <mldsa_poly_uniform>
     +0xe9f: xor     %eax,%eax
     +0xea1: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0xeb0: movslq  0x1a20(%rsp,%rax,4),%rcx
     +0xeb8: movslq  0x340(%rsp,%rax,4),%rdx
     +0xec0: imul    %rcx,%rdx
     +0xec4: mov     %rdx,%rcx
     +0xec7: imul    %rbx,%rcx
     +0xecb: sar     $0x20,%rcx
     +0xecf: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xed6: add     %rdx,%rcx
     +0xed9: shr     $0x20,%rcx
     +0xedd: mov     %ecx,0x1a20(%rsp,%rax,4)
     +0xee4: movslq  0x1a24(%rsp,%rax,4),%rcx
     +0xeec: movslq  0x344(%rsp,%rax,4),%rdx
     +0xef4: imul    %rcx,%rdx
     +0xef8: mov     %rdx,%rcx
     +0xefb: imul    %rbx,%rcx
     +0xeff: sar     $0x20,%rcx
     +0xf03: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xf0a: add     %rdx,%rcx
     +0xf0d: shr     $0x20,%rcx
     +0xf11: mov     %ecx,0x1a24(%rsp,%rax,4)
     +0xf18: add     $0x2,%rax
     +0xf1c: cmp     $0x100,%rax
     +0xf22: jne     <mldsa87_signature_internal+0xeb0>
     +0xf24: movw    $0x100,0xe0(%rsp)
     +0xf2e: lea     0x1e20(%rsp),%rdi
     +0xf36: lea     0xc0(%rsp),%rsi
     +0xf3e: call    <mldsa_poly_uniform>
     +0xf43: xor     %eax,%eax
     +0xf45: data16  cs nopw 0x0(%rax,%rax,1)
     +0xf50: movslq  0x1e20(%rsp,%rax,4),%rcx
     +0xf58: movslq  0x340(%rsp,%rax,4),%rdx
     +0xf60: imul    %rcx,%rdx
     +0xf64: mov     %rdx,%rcx
     +0xf67: imul    %rbx,%rcx
     +0xf6b: sar     $0x20,%rcx
     +0xf6f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xf76: add     %rdx,%rcx
     +0xf79: shr     $0x20,%rcx
     +0xf7d: mov     %ecx,0x1e20(%rsp,%rax,4)
     +0xf84: movslq  0x1e24(%rsp,%rax,4),%rcx
     +0xf8c: movslq  0x344(%rsp,%rax,4),%rdx
     +0xf94: imul    %rcx,%rdx
     +0xf98: mov     %rdx,%rcx
     +0xf9b: imul    %rbx,%rcx
     +0xf9f: sar     $0x20,%rcx
     +0xfa3: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xfaa: add     %rdx,%rcx
     +0xfad: shr     $0x20,%rcx
     +0xfb1: mov     %ecx,0x1e24(%rsp,%rax,4)
     +0xfb8: add     $0x2,%rax
     +0xfbc: cmp     $0x100,%rax
     +0xfc2: jne     <mldsa87_signature_internal+0xf50>
     +0xfc4: movw    $0x200,0xe0(%rsp)
     +0xfce: lea     0x2220(%rsp),%rdi
     +0xfd6: lea     0xc0(%rsp),%rsi
     +0xfde: call    <mldsa_poly_uniform>
     +0xfe3: xor     %eax,%eax
     +0xfe5: data16  cs nopw 0x0(%rax,%rax,1)
     +0xff0: movslq  0x2220(%rsp,%rax,4),%rcx
     +0xff8: movslq  0x340(%rsp,%rax,4),%rdx
    +0x1000: imul    %rcx,%rdx
    +0x1004: mov     %rdx,%rcx
    +0x1007: imul    %rbx,%rcx
    +0x100b: sar     $0x20,%rcx
    +0x100f: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x1016: add     %rdx,%rcx
    +0x1019: shr     $0x20,%rcx
    +0x101d: mov     %ecx,0x2220(%rsp,%rax,4)
    +0x1024: movslq  0x2224(%rsp,%rax,4),%rcx
    +0x102c: movslq  0x344(%rsp,%rax,4),%rdx
    +0x1034: imul    %rcx,%rdx
    +0x1038: mov     %rdx,%rcx
    +0x103b: imul    %rbx,%rcx
    +0x103f: sar     $0x20,%rcx
    +0x1043: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x104a: add     %rdx,%rcx
    +0x104d: shr     $0x20,%rcx
    +0x1051: mov     %ecx,0x2224(%rsp,%rax,4)
    +0x1058: add     $0x2,%rax
    +0x105c: cmp     $0x100,%rax
    +0x1062: jne     <mldsa87_signature_internal+0xff0>
    +0x1064: movw    $0x300,0xe0(%rsp)
    +0x106e: lea     0x2620(%rsp),%rdi
    +0x1076: lea     0xc0(%rsp),%rsi
    +0x107e: call    <mldsa_poly_uniform>
    +0x1083: xor     %eax,%eax
    +0x1085: data16  cs nopw 0x0(%rax,%rax,1)
    +0x1090: movslq  0x2620(%rsp,%rax,4),%rcx
    +0x1098: movslq  0x340(%rsp,%rax,4),%rdx
    +0x10a0: imul    %rcx,%rdx
    +0x10a4: mov     %rdx,%rcx
    +0x10a7: imul    %rbx,%rcx
    +0x10ab: sar     $0x20,%rcx
    +0x10af: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x10b6: add     %rdx,%rcx
    +0x10b9: shr     $0x20,%rcx
    +0x10bd: mov     %ecx,0x2620(%rsp,%rax,4)
    +0x10c4: movslq  0x2624(%rsp,%rax,4),%rcx
    +0x10cc: movslq  0x344(%rsp,%rax,4),%rdx
    +0x10d4: imul    %rcx,%rdx
    +0x10d8: mov     %rdx,%rcx
    +0x10db: imul    %rbx,%rcx
    +0x10df: sar     $0x20,%rcx
    +0x10e3: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x10ea: add     %rdx,%rcx
    +0x10ed: shr     $0x20,%rcx
    +0x10f1: mov     %ecx,0x2624(%rsp,%rax,4)
    +0x10f8: add     $0x2,%rax
    +0x10fc: cmp     $0x100,%rax
    +0x1102: jne     <mldsa87_signature_internal+0x1090>
    +0x1104: movw    $0x400,0xe0(%rsp)
    +0x110e: lea     0x2a20(%rsp),%rdi
    +0x1116: lea     0xc0(%rsp),%rsi
    +0x111e: call    <mldsa_poly_uniform>
    +0x1123: xor     %eax,%eax
    +0x1125: data16  cs nopw 0x0(%rax,%rax,1)
    +0x1130: movslq  0x2a20(%rsp,%rax,4),%rcx
    +0x1138: movslq  0x340(%rsp,%rax,4),%rdx
    +0x1140: imul    %rcx,%rdx
    +0x1144: mov     %rdx,%rcx
    +0x1147: imul    %rbx,%rcx
    +0x114b: sar     $0x20,%rcx
    +0x114f: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x1156: add     %rdx,%rcx
    +0x1159: shr     $0x20,%rcx
    +0x115d: mov     %ecx,0x2a20(%rsp,%rax,4)
    +0x1164: movslq  0x2a24(%rsp,%rax,4),%rcx
    +0x116c: movslq  0x344(%rsp,%rax,4),%rdx
    +0x1174: imul    %rcx,%rdx
    +0x1178: mov     %rdx,%rcx
    +0x117b: imul    %rbx,%rcx
    +0x117f: sar     $0x20,%rcx
    +0x1183: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x118a: add     %rdx,%rcx
    +0x118d: shr     $0x20,%rcx
    +0x1191: mov     %ecx,0x2a24(%rsp,%rax,4)
    +0x1198: add     $0x2,%rax
    +0x119c: cmp     $0x100,%rax
    +0x11a2: jne     <mldsa87_signature_internal+0x1130>
    +0x11a4: movw    $0x500,0xe0(%rsp)
    +0x11ae: lea     0x2e20(%rsp),%rdi
    +0x11b6: lea     0xc0(%rsp),%rsi
    +0x11be: call    <mldsa_poly_uniform>
    +0x11c3: xor     %eax,%eax
    +0x11c5: data16  cs nopw 0x0(%rax,%rax,1)
    +0x11d0: movslq  0x2e20(%rsp,%rax,4),%rcx
    +0x11d8: movslq  0x340(%rsp,%rax,4),%rdx
    +0x11e0: imul    %rcx,%rdx
    +0x11e4: mov     %rdx,%rcx
    +0x11e7: imul    %rbx,%rcx
    +0x11eb: sar     $0x20,%rcx
    +0x11ef: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x11f6: add     %rdx,%rcx
    +0x11f9: shr     $0x20,%rcx
    +0x11fd: mov     %ecx,0x2e20(%rsp,%rax,4)
    +0x1204: movslq  0x2e24(%rsp,%rax,4),%rcx
    +0x120c: movslq  0x344(%rsp,%rax,4),%rdx
    +0x1214: imul    %rcx,%rdx
    +0x1218: mov     %rdx,%rcx
    +0x121b: imul    %rbx,%rcx
    +0x121f: sar     $0x20,%rcx
    +0x1223: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x122a: add     %rdx,%rcx
    +0x122d: shr     $0x20,%rcx
    +0x1231: mov     %ecx,0x2e24(%rsp,%rax,4)
    +0x1238: add     $0x2,%rax
    +0x123c: cmp     $0x100,%rax
    +0x1242: jne     <mldsa87_signature_internal+0x11d0>
    +0x1244: movw    $0x600,0xe0(%rsp)
    +0x124e: lea     0x3220(%rsp),%rdi
    +0x1256: lea     0xc0(%rsp),%rsi
    +0x125e: call    <mldsa_poly_uniform>
    +0x1263: xor     %eax,%eax
    +0x1265: data16  cs nopw 0x0(%rax,%rax,1)
    +0x1270: movslq  0x3220(%rsp,%rax,4),%rcx
    +0x1278: movslq  0x340(%rsp,%rax,4),%rdx
    +0x1280: imul    %rcx,%rdx
    +0x1284: mov     %rdx,%rcx
    +0x1287: imul    %rbx,%rcx
    +0x128b: sar     $0x20,%rcx
    +0x128f: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x1296: add     %rdx,%rcx
    +0x1299: shr     $0x20,%rcx
    +0x129d: mov     %ecx,0x3220(%rsp,%rax,4)
    +0x12a4: movslq  0x3224(%rsp,%rax,4),%rcx
    +0x12ac: movslq  0x344(%rsp,%rax,4),%rdx
    +0x12b4: imul    %rcx,%rdx
    +0x12b8: mov     %rdx,%rcx
    +0x12bb: imul    %rbx,%rcx
    +0x12bf: sar     $0x20,%rcx
    +0x12c3: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x12ca: add     %rdx,%rcx
    +0x12cd: shr     $0x20,%rcx
    +0x12d1: mov     %ecx,0x3224(%rsp,%rax,4)
    +0x12d8: add     $0x2,%rax
    +0x12dc: cmp     $0x100,%rax
    +0x12e2: jne     <mldsa87_signature_internal+0x1270>
    +0x12e4: movw    $0x700,0xe0(%rsp)
    +0x12ee: lea     0x3620(%rsp),%rdi
    +0x12f6: lea     0xc0(%rsp),%rsi
    +0x12fe: call    <mldsa_poly_uniform>
    +0x1303: xor     %eax,%eax
    +0x1305: pxor    %xmm4,%xmm4
    +0x1309: movdqa  0xb85f(%rip),%xmm5
    +0x1311: movdqa  0xb867(%rip),%xmm6
    +0x1319: nopl    0x0(%rax)
    +0x1320: movslq  0x3620(%rsp,%rax,4),%rcx
    +0x1328: movslq  0x340(%rsp,%rax,4),%rdx
    +0x1330: imul    %rcx,%rdx
    +0x1334: mov     %rdx,%rcx
    +0x1337: imul    %rbx,%rcx
    +0x133b: sar     $0x20,%rcx
    +0x133f: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x1346: add     %rdx,%rcx
    +0x1349: shr     $0x20,%rcx
    +0x134d: mov     %ecx,0x3620(%rsp,%rax,4)
    +0x1354: movslq  0x3624(%rsp,%rax,4),%rcx
    +0x135c: movslq  0x344(%rsp,%rax,4),%rdx
    +0x1364: imul    %rcx,%rdx
    +0x1368: mov     %rdx,%rcx
    +0x136b: imul    %rbx,%rcx
    +0x136f: sar     $0x20,%rcx
    +0x1373: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x137a: add     %rdx,%rcx
    +0x137d: shr     $0x20,%rcx
    +0x1381: mov     %ecx,0x3624(%rsp,%rax,4)
    +0x1388: add     $0x2,%rax
    +0x138c: cmp     $0x100,%rax
    +0x1392: jne     <mldsa87_signature_internal+0x1320>
    +0x1394: jmp     <mldsa87_signature_internal+0x200>
    +0x1399: nopl    0x0(%rax)
    +0x13a0: movdqa  %xmm4,0xf0(%rsp)
    +0x13a9: movdqa  %xmm4,0xe0(%rsp)
    +0x13b2: movdqa  %xmm4,0xd0(%rsp)
    +0x13bb: movdqa  %xmm4,0xc0(%rsp)
    +0x13c4: lea     0xc0(%rsp),%rax
    +0x13cc: mov     $0x4,%eax
    +0x13d1: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x13e0: movdqa  0x1a10(%rsp,%rax,4),%xmm0
    +0x13e9: movdqa  0x1a20(%rsp,%rax,4),%xmm1
    +0x13f2: movdqa  %xmm0,%xmm2
    +0x13f6: paddd   %xmm5,%xmm2
    +0x13fa: movdqa  %xmm1,%xmm3
    +0x13fe: paddd   %xmm5,%xmm3
    +0x1402: psrad   $0x17,%xmm2
    +0x1407: psrad   $0x17,%xmm3
    +0x140c: pshufd  $0xf5,%xmm2,%xmm4
    +0x1411: pmuludq %xmm6,%xmm2
    +0x1415: pshufd  $0xe8,%xmm2,%xmm2
    +0x141a: pmuludq %xmm6,%xmm4
    +0x141e: pshufd  $0xe8,%xmm4,%xmm4
    +0x1423: punpckldq %xmm4,%xmm2
    +0x1427: pshufd  $0xf5,%xmm3,%xmm4
    +0x142c: pmuludq %xmm6,%xmm3
    +0x1430: pshufd  $0xe8,%xmm3,%xmm3
    +0x1435: pmuludq %xmm6,%xmm4
    +0x1439: pshufd  $0xe8,%xmm4,%xmm4
    +0x143e: punpckldq %xmm4,%xmm3
    +0x1442: paddd   %xmm0,%xmm2
    +0x1446: paddd   %xmm1,%xmm3
    +0x144a: movdqa  %xmm2,0x1a10(%rsp,%rax,4)
    +0x1453: movdqa  %xmm3,0x1a20(%rsp,%rax,4)
    +0x145c: add     $0x8,%rax
    +0x1460: cmp     $0x104,%rax
    +0x1466: jne     <mldsa87_signature_internal+0x13e0>
    +0x146c: mov     $0x104,%eax
    +0x1471: lea     0x740(%rsp),%r14
    +0x1479: nopl    0x0(%rax)
    +0x1480: movdqa  0x1a10(%rsp,%rax,4),%xmm0
    +0x1489: movdqa  0x1a20(%rsp,%rax,4),%xmm1
    +0x1492: movdqa  %xmm0,%xmm2
    +0x1496: paddd   %xmm5,%xmm2
    +0x149a: movdqa  %xmm1,%xmm3
    +0x149e: paddd   %xmm5,%xmm3
    +0x14a2: psrad   $0x17,%xmm2
    +0x14a7: psrad   $0x17,%xmm3
    +0x14ac: pshufd  $0xf5,%xmm2,%xmm4
    +0x14b1: pmuludq %xmm6,%xmm2
    +0x14b5: pshufd  $0xe8,%xmm2,%xmm2
    +0x14ba: pmuludq %xmm6,%xmm4
    +0x14be: pshufd  $0xe8,%xmm4,%xmm4
    +0x14c3: punpckldq %xmm4,%xmm2
    +0x14c7: pshufd  $0xf5,%xmm3,%xmm4
    +0x14cc: pmuludq %xmm6,%xmm3
    +0x14d0: pshufd  $0xe8,%xmm3,%xmm3
    +0x14d5: pmuludq %xmm6,%xmm4
    +0x14d9: pshufd  $0xe8,%xmm4,%xmm4
    +0x14de: punpckldq %xmm4,%xmm3
    +0x14e2: paddd   %xmm0,%xmm2
    +0x14e6: paddd   %xmm1,%xmm3
    +0x14ea: movdqa  %xmm2,0x1a10(%rsp,%rax,4)
    +0x14f3: movdqa  %xmm3,0x1a20(%rsp,%rax,4)
    +0x14fc: add     $0x8,%rax
    +0x1500: cmp     $0x204,%rax
    +0x1506: jne     <mldsa87_signature_internal+0x1480>
    +0x150c: mov     $0x204,%eax
    +0x1511: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1520: movdqa  0x1a10(%rsp,%rax,4),%xmm0
    +0x1529: movdqa  0x1a20(%rsp,%rax,4),%xmm1
    +0x1532: movdqa  %xmm0,%xmm2
    +0x1536: paddd   %xmm5,%xmm2
    +0x153a: movdqa  %xmm1,%xmm3
    +0x153e: paddd   %xmm5,%xmm3
    +0x1542: psrad   $0x17,%xmm2
    +0x1547: psrad   $0x17,%xmm3
    +0x154c: pshufd  $0xf5,%xmm2,%xmm4
    +0x1551: pmuludq %xmm6,%xmm2
    +0x1555: pshufd  $0xe8,%xmm2,%xmm2
    +0x155a: pmuludq %xmm6,%xmm4
    +0x155e: pshufd  $0xe8,%xmm4,%xmm4
    +0x1563: punpckldq %xmm4,%xmm2
    +0x1567: pshufd  $0xf5,%xmm3,%xmm4
    +0x156c: pmuludq %xmm6,%xmm3
    +0x1570: pshufd  $0xe8,%xmm3,%xmm3
    +0x1575: pmuludq %xmm6,%xmm4
    +0x1579: pshufd  $0xe8,%xmm4,%xmm4
    +0x157e: punpckldq %xmm4,%xmm3
    +0x1582: paddd   %xmm0,%xmm2
    +0x1586: paddd   %xmm1,%xmm3
    +0x158a: movdqa  %xmm2,0x1a10(%rsp,%rax,4)
    +0x1593: movdqa  %xmm3,0x1a20(%rsp,%rax,4)
    +0x159c: add     $0x8,%rax
    +0x15a0: cmp     $0x304,%rax
    +0x15a6: jne     <mldsa87_signature_internal+0x1520>
    +0x15ac: mov     $0x304,%eax
    +0x15b1: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x15c0: movdqa  0x1a10(%rsp,%rax,4),%xmm0
    +0x15c9: movdqa  0x1a20(%rsp,%rax,4),%xmm1
    +0x15d2: movdqa  %xmm0,%xmm2
    +0x15d6: paddd   %xmm5,%xmm2
    +0x15da: movdqa  %xmm1,%xmm3
    +0x15de: paddd   %xmm5,%xmm3
    +0x15e2: psrad   $0x17,%xmm2
    +0x15e7: psrad   $0x17,%xmm3
    +0x15ec: pshufd  $0xf5,%xmm2,%xmm4
    +0x15f1: pmuludq %xmm6,%xmm2
    +0x15f5: pshufd  $0xe8,%xmm2,%xmm2
    +0x15fa: pmuludq %xmm6,%xmm4
    +0x15fe: pshufd  $0xe8,%xmm4,%xmm4
    +0x1603: punpckldq %xmm4,%xmm2
    +0x1607: pshufd  $0xf5,%xmm3,%xmm4
    +0x160c: pmuludq %xmm6,%xmm3
    +0x1610: pshufd  $0xe8,%xmm3,%xmm3
    +0x1615: pmuludq %xmm6,%xmm4
    +0x1619: pshufd  $0xe8,%xmm4,%xmm4
    +0x161e: punpckldq %xmm4,%xmm3
    +0x1622: paddd   %xmm0,%xmm2
    +0x1626: paddd   %xmm1,%xmm3
    +0x162a: movdqa  %xmm2,0x1a10(%rsp,%rax,4)
    +0x1633: movdqa  %xmm3,0x1a20(%rsp,%rax,4)
    +0x163c: add     $0x8,%rax
    +0x1640: cmp     $0x404,%rax
    +0x1646: jne     <mldsa87_signature_internal+0x15c0>
    +0x164c: mov     $0x404,%eax
    +0x1651: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1660: movdqa  0x1a10(%rsp,%rax,4),%xmm0
    +0x1669: movdqa  0x1a20(%rsp,%rax,4),%xmm1
    +0x1672: movdqa  %xmm0,%xmm2
    +0x1676: paddd   %xmm5,%xmm2
    +0x167a: movdqa  %xmm1,%xmm3
    +0x167e: paddd   %xmm5,%xmm3
    +0x1682: psrad   $0x17,%xmm2
    +0x1687: psrad   $0x17,%xmm3
    +0x168c: pshufd  $0xf5,%xmm2,%xmm4
    +0x1691: pmuludq %xmm6,%xmm2
    +0x1695: pshufd  $0xe8,%xmm2,%xmm2
    +0x169a: pmuludq %xmm6,%xmm4
    +0x169e: pshufd  $0xe8,%xmm4,%xmm4
    +0x16a3: punpckldq %xmm4,%xmm2
    +0x16a7: pshufd  $0xf5,%xmm3,%xmm4
    +0x16ac: pmuludq %xmm6,%xmm3
    +0x16b0: pshufd  $0xe8,%xmm3,%xmm3
    +0x16b5: pmuludq %xmm6,%xmm4
    +0x16b9: pshufd  $0xe8,%xmm4,%xmm4
    +0x16be: punpckldq %xmm4,%xmm3
    +0x16c2: paddd   %xmm0,%xmm2
    +0x16c6: paddd   %xmm1,%xmm3
    +0x16ca: movdqa  %xmm2,0x1a10(%rsp,%rax,4)
    +0x16d3: movdqa  %xmm3,0x1a20(%rsp,%rax,4)
    +0x16dc: add     $0x8,%rax
    +0x16e0: cmp     $0x504,%rax
    +0x16e6: jne     <mldsa87_signature_internal+0x1660>
    +0x16ec: mov     $0x504,%eax
    +0x16f1: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1700: movdqa  0x1a10(%rsp,%rax,4),%xmm0
    +0x1709: movdqa  0x1a20(%rsp,%rax,4),%xmm1
    +0x1712: movdqa  %xmm0,%xmm2
    +0x1716: paddd   %xmm5,%xmm2
    +0x171a: movdqa  %xmm1,%xmm3
    +0x171e: paddd   %xmm5,%xmm3
    +0x1722: psrad   $0x17,%xmm2
    +0x1727: psrad   $0x17,%xmm3
    +0x172c: pshufd  $0xf5,%xmm2,%xmm4
    +0x1731: pmuludq %xmm6,%xmm2
    +0x1735: pshufd  $0xe8,%xmm2,%xmm2
    +0x173a: pmuludq %xmm6,%xmm4
    +0x173e: pshufd  $0xe8,%xmm4,%xmm4
    +0x1743: punpckldq %xmm4,%xmm2
    +0x1747: pshufd  $0xf5,%xmm3,%xmm4
    +0x174c: pmuludq %xmm6,%xmm3
    +0x1750: pshufd  $0xe8,%xmm3,%xmm3
    +0x1755: pmuludq %xmm6,%xmm4
    +0x1759: pshufd  $0xe8,%xmm4,%xmm4
    +0x175e: punpckldq %xmm4,%xmm3
    +0x1762: paddd   %xmm0,%xmm2
    +0x1766: paddd   %xmm1,%xmm3
    +0x176a: movdqa  %xmm2,0x1a10(%rsp,%rax,4)
    +0x1773: movdqa  %xmm3,0x1a20(%rsp,%rax,4)
    +0x177c: add     $0x8,%rax
    +0x1780: cmp     $0x604,%rax
    +0x1786: jne     <mldsa87_signature_internal+0x1700>
    +0x178c: mov     $0x604,%eax
    +0x1791: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x17a0: movdqa  0x1a10(%rsp,%rax,4),%xmm0
    +0x17a9: movdqa  0x1a20(%rsp,%rax,4),%xmm1
    +0x17b2: movdqa  %xmm0,%xmm2
    +0x17b6: paddd   %xmm5,%xmm2
    +0x17ba: movdqa  %xmm1,%xmm3
    +0x17be: paddd   %xmm5,%xmm3
    +0x17c2: psrad   $0x17,%xmm2
    +0x17c7: psrad   $0x17,%xmm3
    +0x17cc: pshufd  $0xf5,%xmm2,%xmm4
    +0x17d1: pmuludq %xmm6,%xmm2
    +0x17d5: pshufd  $0xe8,%xmm2,%xmm2
    +0x17da: pmuludq %xmm6,%xmm4
    +0x17de: pshufd  $0xe8,%xmm4,%xmm4
    +0x17e3: punpckldq %xmm4,%xmm2
    +0x17e7: pshufd  $0xf5,%xmm3,%xmm4
    +0x17ec: pmuludq %xmm6,%xmm3
    +0x17f0: pshufd  $0xe8,%xmm3,%xmm3
    +0x17f5: pmuludq %xmm6,%xmm4
    +0x17f9: pshufd  $0xe8,%xmm4,%xmm4
    +0x17fe: punpckldq %xmm4,%xmm3
    +0x1802: paddd   %xmm0,%xmm2
    +0x1806: paddd   %xmm1,%xmm3
    +0x180a: movdqa  %xmm2,0x1a10(%rsp,%rax,4)
    +0x1813: movdqa  %xmm3,0x1a20(%rsp,%rax,4)
    +0x181c: add     $0x8,%rax
    +0x1820: cmp     $0x704,%rax
    +0x1826: jne     <mldsa87_signature_internal+0x17a0>
    +0x182c: mov     $0x704,%eax
    +0x1831: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1840: movdqa  0x1a10(%rsp,%rax,4),%xmm0
    +0x1849: movdqa  0x1a20(%rsp,%rax,4),%xmm1
    +0x1852: movdqa  %xmm0,%xmm2
    +0x1856: paddd   %xmm5,%xmm2
    +0x185a: movdqa  %xmm1,%xmm3
    +0x185e: paddd   %xmm5,%xmm3
    +0x1862: psrad   $0x17,%xmm2
    +0x1867: psrad   $0x17,%xmm3
    +0x186c: pshufd  $0xf5,%xmm2,%xmm4
    +0x1871: pmuludq %xmm6,%xmm2
    +0x1875: pshufd  $0xe8,%xmm2,%xmm2
    +0x187a: pmuludq %xmm6,%xmm4
    +0x187e: pshufd  $0xe8,%xmm4,%xmm4
    +0x1883: punpckldq %xmm4,%xmm2
    +0x1887: pshufd  $0xf5,%xmm3,%xmm4
    +0x188c: pmuludq %xmm6,%xmm3
    +0x1890: pshufd  $0xe8,%xmm3,%xmm3
    +0x1895: pmuludq %xmm6,%xmm4
    +0x1899: pshufd  $0xe8,%xmm4,%xmm4
    +0x189e: punpckldq %xmm4,%xmm3
    +0x18a2: paddd   %xmm0,%xmm2
    +0x18a6: paddd   %xmm1,%xmm3
    +0x18aa: movdqa  %xmm2,0x1a10(%rsp,%rax,4)
    +0x18b3: movdqa  %xmm3,0x1a20(%rsp,%rax,4)
    +0x18bc: add     $0x8,%rax
    +0x18c0: cmp     $0x804,%rax
    +0x18c6: jne     <mldsa87_signature_internal+0x1840>
    +0x18cc: lea     0x1a20(%rsp),%rdi
    +0x18d4: call    <mldsa_poly_invntt_tomont>
    +0x18d9: lea     0x1e20(%rsp),%rdi
    +0x18e1: call    <mldsa_poly_invntt_tomont>
    +0x18e6: lea     0x2220(%rsp),%rdi
    +0x18ee: call    <mldsa_poly_invntt_tomont>
    +0x18f3: lea     0x2620(%rsp),%rdi
    +0x18fb: call    <mldsa_poly_invntt_tomont>
    +0x1900: lea     0x2a20(%rsp),%rdi
    +0x1908: call    <mldsa_poly_invntt_tomont>
    +0x190d: lea     0x2e20(%rsp),%rdi
    +0x1915: call    <mldsa_poly_invntt_tomont>
    +0x191a: lea     0x3220(%rsp),%rdi
    +0x1922: call    <mldsa_poly_invntt_tomont>
    +0x1927: lea     0x3620(%rsp),%rdi
    +0x192f: call    <mldsa_poly_invntt_tomont>
    +0x1934: xor     %eax,%eax
    +0x1936: cs      nopw 0x0(%rax,%rax,1)
    +0x1940: movslq  0x1a20(%rsp,%rax,4),%rcx
    +0x1948: lea     0x7fe001(%rcx),%edx
    +0x194e: mov     %rcx,%rsi
    +0x1951: shr     $0x1f,%rsi
    +0x1955: xor     %ecx,%edx
    +0x1957: and     %esi,%edx
    +0x1959: xor     %ecx,%edx
    +0x195b: mov     %edx,0x1a20(%rsp,%rax,4)
    +0x1962: inc     %rax
    +0x1965: cmp     $0x100,%rax
    +0x196b: jne     <mldsa87_signature_internal+0x1940>
    +0x196d: mov     $0x100,%eax
    +0x1972: pxor    %xmm5,%xmm5
    +0x1976: movdqa  0xb4f2(%rip),%xmm6
    +0x197e: xchg    %ax,%ax
    +0x1980: movslq  0x1a20(%rsp,%rax,4),%rcx
    +0x1988: lea     0x7fe001(%rcx),%edx
    +0x198e: mov     %rcx,%rsi
    +0x1991: shr     $0x1f,%rsi
    +0x1995: xor     %ecx,%edx
    +0x1997: and     %esi,%edx
    +0x1999: xor     %ecx,%edx
    +0x199b: mov     %edx,0x1a20(%rsp,%rax,4)
    +0x19a2: inc     %rax
    +0x19a5: cmp     $0x200,%rax
    +0x19ab: jne     <mldsa87_signature_internal+0x1980>
    +0x19ad: mov     $0x200,%eax
    +0x19b2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x19c0: movslq  0x1a20(%rsp,%rax,4),%rcx
    +0x19c8: lea     0x7fe001(%rcx),%edx
    +0x19ce: mov     %rcx,%rsi
    +0x19d1: shr     $0x1f,%rsi
    +0x19d5: xor     %ecx,%edx
    +0x19d7: and     %esi,%edx
    +0x19d9: xor     %ecx,%edx
    +0x19db: mov     %edx,0x1a20(%rsp,%rax,4)
    +0x19e2: inc     %rax
    +0x19e5: cmp     $0x300,%rax
    +0x19eb: jne     <mldsa87_signature_internal+0x19c0>
    +0x19ed: mov     $0x300,%eax
    +0x19f2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1a00: movslq  0x1a20(%rsp,%rax,4),%rcx
    +0x1a08: lea     0x7fe001(%rcx),%edx
    +0x1a0e: mov     %rcx,%rsi
    +0x1a11: shr     $0x1f,%rsi
    +0x1a15: xor     %ecx,%edx
    +0x1a17: and     %esi,%edx
    +0x1a19: xor     %ecx,%edx
    +0x1a1b: mov     %edx,0x1a20(%rsp,%rax,4)
    +0x1a22: inc     %rax
    +0x1a25: cmp     $0x400,%rax
    +0x1a2b: jne     <mldsa87_signature_internal+0x1a00>
    +0x1a2d: mov     $0x400,%eax
    +0x1a32: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1a40: movslq  0x1a20(%rsp,%rax,4),%rcx
    +0x1a48: lea     0x7fe001(%rcx),%edx
    +0x1a4e: mov     %rcx,%rsi
    +0x1a51: shr     $0x1f,%rsi
    +0x1a55: xor     %ecx,%edx
    +0x1a57: and     %esi,%edx
    +0x1a59: xor     %ecx,%edx
    +0x1a5b: mov     %edx,0x1a20(%rsp,%rax,4)
    +0x1a62: inc     %rax
    +0x1a65: cmp     $0x500,%rax
    +0x1a6b: jne     <mldsa87_signature_internal+0x1a40>
    +0x1a6d: mov     $0x500,%eax
    +0x1a72: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1a80: movslq  0x1a20(%rsp,%rax,4),%rcx
    +0x1a88: lea     0x7fe001(%rcx),%edx
    +0x1a8e: mov     %rcx,%rsi
    +0x1a91: shr     $0x1f,%rsi
    +0x1a95: xor     %ecx,%edx
    +0x1a97: and     %esi,%edx
    +0x1a99: xor     %ecx,%edx
    +0x1a9b: mov     %edx,0x1a20(%rsp,%rax,4)
    +0x1aa2: inc     %rax
    +0x1aa5: cmp     $0x600,%rax
    +0x1aab: jne     <mldsa87_signature_internal+0x1a80>
    +0x1aad: mov     $0x600,%eax
    +0x1ab2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1ac0: movslq  0x1a20(%rsp,%rax,4),%rcx
    +0x1ac8: lea     0x7fe001(%rcx),%edx
    +0x1ace: mov     %rcx,%rsi
    +0x1ad1: shr     $0x1f,%rsi
    +0x1ad5: xor     %ecx,%edx
    +0x1ad7: and     %esi,%edx
    +0x1ad9: xor     %ecx,%edx
    +0x1adb: mov     %edx,0x1a20(%rsp,%rax,4)
    +0x1ae2: inc     %rax
    +0x1ae5: cmp     $0x700,%rax
    +0x1aeb: jne     <mldsa87_signature_internal+0x1ac0>
    +0x1aed: mov     $0x700,%eax
    +0x1af2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1b00: movslq  0x1a20(%rsp,%rax,4),%rcx
    +0x1b08: lea     0x7fe001(%rcx),%edx
    +0x1b0e: mov     %rcx,%rsi
    +0x1b11: shr     $0x1f,%rsi
    +0x1b15: xor     %ecx,%edx
    +0x1b17: and     %esi,%edx
    +0x1b19: xor     %ecx,%edx
    +0x1b1b: mov     %edx,0x1a20(%rsp,%rax,4)
    +0x1b22: inc     %rax
    +0x1b25: cmp     $0x800,%rax
    +0x1b2b: jne     <mldsa87_signature_internal+0x1b00>
    +0x1b2d: lea     0x1624(%rsp),%rax
    +0x1b35: lea     0x1a20(%rsp),%rcx
    +0x1b3d: xor     %edx,%edx
    +0x1b3f: nop     
    +0x1b40: xor     %esi,%esi
    +0x1b42: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1b50: mov     (%rcx,%rsi,4),%edi
    +0x1b53: lea     0x7f(%rdi),%r8d
    +0x1b57: sar     $0x7,%r8d
    +0x1b5b: mov     %r8d,%r9d
    +0x1b5e: shl     $0xa,%r8d
    +0x1b62: add     %r9d,%r8d
    +0x1b65: add     $0x200000,%r8d
    +0x1b6c: shr     $0x16,%r8d
    +0x1b70: and     $0xf,%r8d
    +0x1b74: mov     %r8d,0x340(%rsp,%rsi,4)
    +0x1b7c: imul    $0xfff80200,%r8d,%r8d
    +0x1b83: lea     (%r8,%rdi,1),%r9d
    +0x1b87: mov     %r9d,(%rcx,%rsi,4)
    +0x1b8b: add     %r8d,%edi
    +0x1b8e: add     $0xff801fff,%edi
    +0x1b94: mov     $0x3ff000,%r8d
    +0x1b9a: sub     %r9d,%r8d
    +0x1b9d: movslq  %r8d,%r8
    +0x1ba0: shr     $0x1f,%r8
    +0x1ba4: xor     %r9d,%edi
    +0x1ba7: and     %r8d,%edi
    +0x1baa: xor     %r9d,%edi
    +0x1bad: mov     %edi,(%rcx,%rsi,4)
    +0x1bb0: inc     %rsi
    +0x1bb3: cmp     $0x100,%rsi
    +0x1bba: jne     <mldsa87_signature_internal+0x1b50>
    +0x1bbc: xor     %esi,%esi
    +0x1bbe: xchg    %ax,%ax
    +0x1bc0: movaps  0x340(%rsp,%rsi,8),%xmm0
    +0x1bc8: movaps  0x350(%rsp,%rsi,8),%xmm1
    +0x1bd0: movaps  0x360(%rsp,%rsi,8),%xmm2
    +0x1bd8: movaps  0x370(%rsp,%rsi,8),%xmm3
    +0x1be0: movaps  %xmm0,%xmm4
    +0x1be3: shufps  $0x88,%xmm1,%xmm4
    +0x1be7: shufps  $0xdd,%xmm1,%xmm0
    +0x1beb: movaps  %xmm2,%xmm1
    +0x1bee: shufps  $0x88,%xmm3,%xmm1
    +0x1bf2: shufps  $0xdd,%xmm3,%xmm2
    +0x1bf6: pslld   $0x4,%xmm0
    +0x1bfb: por     %xmm4,%xmm0
    +0x1bff: pslld   $0x4,%xmm2
    +0x1c04: por     %xmm1,%xmm2
    +0x1c08: pand    %xmm6,%xmm0
    +0x1c0c: packuswb %xmm0,%xmm0
    +0x1c10: packuswb %xmm0,%xmm0
    +0x1c14: pand    %xmm6,%xmm2
    +0x1c18: packuswb %xmm2,%xmm2
    +0x1c1c: packuswb %xmm2,%xmm2
    +0x1c20: movd    %xmm0,-0x4(%rax,%rsi,1)
    +0x1c26: movd    %xmm2,(%rax,%rsi,1)
    +0x1c2b: add     $0x8,%rsi
    +0x1c2f: cmp     $0x80,%rsi
    +0x1c36: jne     <mldsa87_signature_internal+0x1bc0>
    +0x1c38: inc     %rdx
    +0x1c3b: add     $0x400,%rcx
    +0x1c42: sub     $0xffffffffffffff80,%rax
    +0x1c46: cmp     $0x8,%rdx
    +0x1c4a: jne     <mldsa87_signature_internal+0x1b40>
    +0x1c50: movdqu  %xmm5,0x7fc(%rsp)
    +0x1c59: movdqa  %xmm5,0x7f0(%rsp)
    +0x1c62: movdqa  %xmm5,0x7e0(%rsp)
    +0x1c6b: movdqa  %xmm5,0x7d0(%rsp)
    +0x1c74: movdqa  %xmm5,0x7c0(%rsp)
    +0x1c7d: movdqa  %xmm5,0x7b0(%rsp)
    +0x1c86: movdqa  %xmm5,0x7a0(%rsp)
    +0x1c8f: movdqa  %xmm5,0x790(%rsp)
    +0x1c98: movdqa  %xmm5,0x780(%rsp)
    +0x1ca1: movdqa  %xmm5,0x770(%rsp)
    +0x1caa: movdqa  %xmm5,0x760(%rsp)
    +0x1cb3: movaps  0x2c0(%rsp),%xmm0
    +0x1cbb: movaps  0x2d0(%rsp),%xmm1
    +0x1cc3: movaps  0x2e0(%rsp),%xmm2
    +0x1ccb: movaps  0x2f0(%rsp),%xmm3
    +0x1cd3: movaps  %xmm0,0x740(%rsp)
    +0x1cdb: movaps  %xmm1,0x750(%rsp)
    +0x1ce3: movaps  %xmm2,0x760(%rsp)
    +0x1ceb: movaps  %xmm3,0x770(%rsp)
    +0x1cf3: movl    $0x40,0x808(%rsp)
    +0x1cfe: movaps  0x780(%rsp),%xmm0
    +0x1d06: movaps  0x790(%rsp),%xmm1
    +0x1d0e: movdqa  0x7a0(%rsp),%xmm2
    +0x1d17: movdqa  0x7b0(%rsp),%xmm3
    +0x1d20: xorps   0x1620(%rsp),%xmm0
    +0x1d28: xorps   0x1630(%rsp),%xmm1
    +0x1d30: movaps  %xmm0,0x780(%rsp)
    +0x1d38: movaps  %xmm1,0x790(%rsp)
    +0x1d40: pxor    0x1640(%rsp),%xmm2
    +0x1d49: pxor    0x1650(%rsp),%xmm3
    +0x1d52: movdqa  %xmm2,0x7a0(%rsp)
    +0x1d5b: movdqa  %xmm3,0x7b0(%rsp)
    +0x1d64: mov     0x1660(%rsp),%rax
    +0x1d6c: xor     %rax,0x7c0(%rsp)
    +0x1d74: mov     %r14,%rdi
    +0x1d77: call    <mldsa_keccakf1600_permute>
    +0x1d7c: mov     $0x3b8,%ebx
    +0x1d81: mov     $0x330,%eax
    +0x1d86: lea     0x1668(%rsp),%r15
    +0x1d8e: xchg    %ax,%ax
    +0x1d90: movups  (%r15),%xmm0
    +0x1d94: movups  0x10(%r15),%xmm1
    +0x1d99: xorps   0x740(%rsp),%xmm0
    +0x1da1: xorps   0x750(%rsp),%xmm1
    +0x1da9: movaps  %xmm0,0x740(%rsp)
    +0x1db1: movaps  %xmm1,0x750(%rsp)
    +0x1db9: movups  0x20(%r15),%xmm0
    +0x1dbe: movups  0x30(%r15),%xmm1
    +0x1dc3: xorps   0x760(%rsp),%xmm0
    +0x1dcb: xorps   0x770(%rsp),%xmm1
    +0x1dd3: movaps  %xmm0,0x760(%rsp)
    +0x1ddb: movaps  %xmm1,0x770(%rsp)
    +0x1de3: movups  0x40(%r15),%xmm0
    +0x1de8: movups  0x50(%r15),%xmm1
    +0x1ded: xorps   0x780(%rsp),%xmm0
    +0x1df5: xorps   0x790(%rsp),%xmm1
    +0x1dfd: movaps  %xmm0,0x780(%rsp)
    +0x1e05: movaps  %xmm1,0x790(%rsp)
    +0x1e0d: movdqu  0x60(%r15),%xmm0
    +0x1e13: movdqu  0x70(%r15),%xmm1
    +0x1e19: pxor    0x7a0(%rsp),%xmm0
    +0x1e22: pxor    0x7b0(%rsp),%xmm1
    +0x1e2b: movdqa  %xmm0,0x7a0(%rsp)
    +0x1e34: movdqa  %xmm1,0x7b0(%rsp)
    +0x1e3d: mov     0x80(%r15),%rcx
    +0x1e44: xor     %rcx,0x7c0(%rsp)
    +0x1e4c: mov     %rbx,%r13
    +0x1e4f: mov     %rax,%r12
    +0x1e52: add     $0xffffffffffffff78,%rbx
    +0x1e59: add     $0x88,%r15
    +0x1e60: mov     %r14,%rdi
    +0x1e63: call    <mldsa_keccakf1600_permute>
    +0x1e68: lea     -0x88(%r12),%rax
    +0x1e70: cmp     $0x10f,%r13
    +0x1e77: jg      <mldsa87_signature_internal+0x1d90>
    +0x1e7d: test    %rbx,%rbx
    +0x1e80: movabs  $0x380200100000000,%r14
    +0x1e8a: je      <mldsa87_signature_internal+0x1f25>
    +0x1e90: cmp     $0x20,%rbx
    +0x1e94: jae     <mldsa87_signature_internal+0x1ea0>
    +0x1e96: xor     %eax,%eax
    +0x1e98: jmp     <mldsa87_signature_internal+0x1f10>
    +0x1e9a: nopw    0x0(%rax,%rax,1)
    +0x1ea0: mov     %ebx,%eax
    +0x1ea2: and     $0xe0,%eax
    +0x1ea7: mov     %r12d,%ecx
    +0x1eaa: and     $0xe0,%ecx
    +0x1eb0: xor     %edx,%edx
    +0x1eb2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1ec0: movdqu  (%r15,%rdx,1),%xmm0
    +0x1ec6: movdqu  0x10(%r15,%rdx,1),%xmm1
    +0x1ecd: pxor    0x740(%rsp,%rdx,1),%xmm0
    +0x1ed6: pxor    0x750(%rsp,%rdx,1),%xmm1
    +0x1edf: movdqa  %xmm0,0x740(%rsp,%rdx,1)
    +0x1ee8: movdqa  %xmm1,0x750(%rsp,%rdx,1)
    +0x1ef1: add     $0x20,%rdx
    +0x1ef5: cmp     %rdx,%rcx
    +0x1ef8: jne     <mldsa87_signature_internal+0x1ec0>
    +0x1efa: cmp     %rax,%rbx
    +0x1efd: je      <mldsa87_signature_internal+0x1f25>
    +0x1eff: test    $0x18,%bl
    +0x1f02: je      <mldsa87_signature_internal+0x3080>
    +0x1f08: nopl    0x0(%rax,%rax,1)
    +0x1f10: mov     (%r15,%rax,1),%rcx
    +0x1f14: xor     %rcx,0x740(%rsp,%rax,1)
    +0x1f1c: add     $0x8,%rax
    +0x1f20: cmp     %rax,%r12
    +0x1f23: jne     <mldsa87_signature_internal+0x1f10>
    +0x1f25: mov     %ebx,0x808(%rsp)
    +0x1f2c: xorb    $0x1f,0x740(%rsp,%rbx,1)
    +0x1f34: xorb    $0x80,0x7c7(%rsp)
    +0x1f3c: movl    $0x88,0x808(%rsp)
    +0x1f47: lea     0x740(%rsp),%rbx
    +0x1f4f: mov     %rbx,%rdi
    +0x1f52: call    <mldsa_keccakf1600_permute>
    +0x1f57: movdqa  0x740(%rsp),%xmm0
    +0x1f60: movdqa  0x750(%rsp),%xmm1
    +0x1f69: movdqa  0x760(%rsp),%xmm2
    +0x1f72: movdqa  0x770(%rsp),%xmm3
    +0x1f7b: movdqa  %xmm3,0x230(%rsp)
    +0x1f84: movdqa  %xmm2,0x220(%rsp)
    +0x1f8d: movdqa  %xmm1,0x210(%rsp)
    +0x1f96: movdqa  %xmm0,0x200(%rsp)
    +0x1f9f: pxor    %xmm0,%xmm0
    +0x1fa3: movdqa  %xmm0,0x780(%rsp)
    +0x1fac: movdqa  %xmm0,0x790(%rsp)
    +0x1fb5: movdqa  %xmm0,0x7a0(%rsp)
    +0x1fbe: movdqa  %xmm0,0x7b0(%rsp)
    +0x1fc7: movdqa  %xmm0,0x7c0(%rsp)
    +0x1fd0: movdqa  %xmm0,0x7d0(%rsp)
    +0x1fd9: movdqa  %xmm0,0x7e0(%rsp)
    +0x1fe2: movdqa  %xmm0,0x7f0(%rsp)
    +0x1feb: movdqa  %xmm0,0x800(%rsp)
    +0x1ff4: movdqa  %xmm0,0x740(%rsp)
    +0x1ffd: movdqa  %xmm0,0x750(%rsp)
    +0x2006: movdqa  %xmm0,0x760(%rsp)
    +0x200f: movdqa  %xmm0,0x770(%rsp)
    +0x2018: movdqa  %xmm0,0x800(%rsp)
    +0x2021: movdqa  %xmm0,0x7f0(%rsp)
    +0x202a: movdqa  %xmm0,0x7e0(%rsp)
    +0x2033: movdqa  %xmm0,0x7d0(%rsp)
    +0x203c: movdqa  %xmm0,0x7c0(%rsp)
    +0x2045: movdqa  %xmm0,0x7b0(%rsp)
    +0x204e: movdqa  %xmm0,0x7a0(%rsp)
    +0x2057: movdqa  %xmm0,0x790(%rsp)
    +0x2060: movdqa  %xmm0,0x780(%rsp)
    +0x2069: movdqa  %xmm0,0x770(%rsp)
    +0x2072: movdqa  %xmm0,0x760(%rsp)
    +0x207b: movdqa  %xmm0,0x750(%rsp)
    +0x2084: movdqa  %xmm0,0x740(%rsp)
    +0x208d: mov     %rbx,%rdi
    +0x2090: lea     0x200(%rsp),%rsi
    +0x2098: call    <mldsa87_poly_challenge>
    +0x209d: mov     %rbx,%rdi
    +0x20a0: call    <mldsa_poly_ntt>
    +0x20a5: mov     $0x2,%ecx
    +0x20aa: mov     0x190(%rsp),%r8
    +0x20b2: xor     %r12d,%r12d
    +0x20b5: data16  cs nopw 0x0(%rax,%rax,1)
    +0x20c0: mov     %r8,0x38(%rsp)
    +0x20c5: mov     0x80(%rsp),%rax
    +0x20cd: mov     %rcx,0x30(%rsp)
    +0x20d2: add     %rcx,%rax
    +0x20d5: xor     %ecx,%ecx
    +0x20d7: nopw    0x0(%rax,%rax,1)
    +0x20e0: movzbl  -0x2(%rax),%edx
    +0x20e4: and     $0x7,%edx
    +0x20e7: mov     %edx,0xb40(%rsp,%rcx,1)
    +0x20ee: movzbl  -0x2(%rax),%esi
    +0x20f2: shr     $0x3,%esi
    +0x20f5: and     $0x7,%esi
    +0x20f8: mov     %esi,0xb44(%rsp,%rcx,1)
    +0x20ff: movzbl  -0x2(%rax),%edi
    +0x2103: shr     $0x6,%edi
    +0x2106: movzbl  -0x1(%rax),%r8d
    +0x210b: and     $0x1,%r8d
    +0x210f: lea     (%rdi,%r8,4),%r8d
    +0x2113: mov     %r8d,0xb48(%rsp,%rcx,1)
    +0x211b: movzbl  -0x1(%rax),%edi
    +0x211f: shr     $1,%edi
    +0x2121: and     $0x7,%edi
    +0x2124: mov     %edi,0xb4c(%rsp,%rcx,1)
    +0x212b: movzbl  -0x1(%rax),%r9d
    +0x2130: shr     $0x4,%r9d
    +0x2134: and     $0x7,%r9d
    +0x2138: mov     %r9d,0xb50(%rsp,%rcx,1)
    +0x2140: movzbl  -0x1(%rax),%r10d
    +0x2145: shr     $0x7,%r10d
    +0x2149: movzbl  (%rax),%r11d
    +0x214d: and     $0x3,%r11d
    +0x2151: lea     (%r10,%r11,2),%r10d
    +0x2155: mov     %r10d,0xb54(%rsp,%rcx,1)
    +0x215d: movzbl  (%rax),%r11d
    +0x2161: shr     $0x2,%r11d
    +0x2165: and     $0x7,%r11d
    +0x2169: mov     %r11d,0xb58(%rsp,%rcx,1)
    +0x2171: movzbl  (%rax),%ebx
    +0x2174: shr     $0x5,%ebx
    +0x2177: mov     $0x2,%r15d
    +0x217d: sub     %edx,%r15d
    +0x2180: mov     %r15d,0xb40(%rsp,%rcx,1)
    +0x2188: mov     $0x2,%edx
    +0x218d: sub     %esi,%edx
    +0x218f: mov     %edx,0xb44(%rsp,%rcx,1)
    +0x2196: mov     $0x2,%edx
    +0x219b: sub     %r8d,%edx
    +0x219e: mov     %edx,0xb48(%rsp,%rcx,1)
    +0x21a5: mov     $0x2,%edx
    +0x21aa: sub     %edi,%edx
    +0x21ac: mov     %edx,0xb4c(%rsp,%rcx,1)
    +0x21b3: mov     $0x2,%edx
    +0x21b8: sub     %r9d,%edx
    +0x21bb: mov     %edx,0xb50(%rsp,%rcx,1)
    +0x21c2: mov     $0x2,%edx
    +0x21c7: sub     %r10d,%edx
    +0x21ca: mov     %edx,0xb54(%rsp,%rcx,1)
    +0x21d1: mov     $0x2,%edx
    +0x21d6: sub     %r11d,%edx
    +0x21d9: mov     %edx,0xb58(%rsp,%rcx,1)
    +0x21e0: mov     $0x2,%edx
    +0x21e5: sub     %ebx,%edx
    +0x21e7: mov     %edx,0xb5c(%rsp,%rcx,1)
    +0x21ee: add     $0x20,%rcx
    +0x21f2: add     $0x3,%rax
    +0x21f6: cmp     $0x400,%rcx
    +0x21fd: jne     <mldsa87_signature_internal+0x20e0>
    +0x2203: lea     0xb40(%rsp),%rdi
    +0x220b: call    <mldsa_poly_ntt>
    +0x2210: mov     $0x1,%eax
    +0x2215: data16  cs nopw 0x0(%rax,%rax,1)
    +0x2220: movslq  0xb3c(%rsp,%rax,4),%rcx
    +0x2228: movslq  0x73c(%rsp,%rax,4),%rdx
    +0x2230: imul    %rcx,%rdx
    +0x2234: mov     %rdx,%rcx
    +0x2237: imul    %r14,%rcx
    +0x223b: sar     $0x20,%rcx
    +0x223f: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x2246: add     %rdx,%rcx
    +0x2249: shr     $0x20,%rcx
    +0x224d: mov     %ecx,0xb3c(%rsp,%rax,4)
    +0x2254: movslq  0xb40(%rsp,%rax,4),%rcx
    +0x225c: movslq  0x740(%rsp,%rax,4),%rdx
    +0x2264: imul    %rcx,%rdx
    +0x2268: mov     %rdx,%rcx
    +0x226b: imul    %r14,%rcx
    +0x226f: sar     $0x20,%rcx
    +0x2273: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x227a: add     %rdx,%rcx
    +0x227d: shr     $0x20,%rcx
    +0x2281: mov     %ecx,0xb40(%rsp,%rax,4)
    +0x2288: add     $0x2,%rax
    +0x228c: cmp     $0x101,%rax
    +0x2292: jne     <mldsa87_signature_internal+0x2220>
    +0x2294: lea     0xb40(%rsp),%rdi
    +0x229c: call    <mldsa_poly_invntt_tomont>
    +0x22a1: mov     0xa0(%rsp),%rax
    +0x22a9: movzwl  0xa8(%rsp),%ecx
    +0x22b1: mov     %r12,0xb8(%rsp)
    +0x22b9: add     %r12w,%cx
    +0x22bd: movups  (%rax),%xmm0
    +0x22c0: movups  0x10(%rax),%xmm1
    +0x22c4: movups  0x20(%rax),%xmm2
    +0x22c8: movdqu  0x30(%rax),%xmm3
    +0x22cd: movaps  %xmm0,0x1a0(%rsp)
    +0x22d5: movaps  %xmm1,0x1b0(%rsp)
    +0x22dd: movaps  %xmm2,0x1c0(%rsp)
    +0x22e5: movdqa  %xmm3,0x1d0(%rsp)
    +0x22ee: mov     %cx,0x1e0(%rsp)
    +0x22f6: xorps   %xmm0,%xmm0
    +0x22f9: movaps  %xmm0,0xc0(%rsp)
    +0x2301: movaps  %xmm0,0xd0(%rsp)
    +0x2309: movaps  %xmm0,0xe0(%rsp)
    +0x2311: movaps  %xmm0,0xf0(%rsp)
    +0x2319: movaps  %xmm0,0x100(%rsp)
    +0x2321: movaps  %xmm0,0x110(%rsp)
    +0x2329: movaps  %xmm0,0x120(%rsp)
    +0x2331: movaps  %xmm0,0x130(%rsp)
    +0x2339: movaps  %xmm0,0x140(%rsp)
    +0x2341: movaps  %xmm0,0x150(%rsp)
    +0x2349: movaps  %xmm0,0x160(%rsp)
    +0x2351: movaps  %xmm0,0x170(%rsp)
    +0x2359: movups  %xmm0,0x17c(%rsp)
    +0x2361: movaps  0x1a0(%rsp),%xmm0
    +0x2369: movaps  0xd0(%rsp),%xmm1
    +0x2371: xorps   0x1b0(%rsp),%xmm1
    +0x2379: movaps  %xmm0,0xc0(%rsp)
    +0x2381: movaps  %xmm1,0xd0(%rsp)
    +0x2389: movdqa  0xe0(%rsp),%xmm0
    +0x2392: movdqa  0xf0(%rsp),%xmm1
    +0x239b: pxor    0x1c0(%rsp),%xmm0
    +0x23a4: movdqa  0x100(%rsp),%xmm2
    +0x23ad: pxor    0x1d0(%rsp),%xmm1
    +0x23b6: movdqa  %xmm0,0xe0(%rsp)
    +0x23bf: movdqa  %xmm1,0xf0(%rsp)
    +0x23c8: pxor    0x1e0(%rsp),%xmm2
    +0x23d1: movd    %xmm2,%eax
    +0x23d5: mov     %ax,0x100(%rsp)
    +0x23dd: xorb    $0x1f,0x102(%rsp)
    +0x23e5: xorb    $0x80,0x147(%rsp)
    +0x23ed: movl    $0x88,0x188(%rsp)
    +0x23f8: mov     $0x88,%r13d
    +0x23fe: mov     $0x2a8,%r15d
    +0x2404: xor     %r12d,%r12d
    +0x2407: jmp     <mldsa87_signature_internal+0x244b>
    +0x2409: nopl    0x0(%rax)
    +0x2410: mov     $0x88,%ebx
    +0x2415: sub     %r13d,%ebx
    +0x2418: cmp     %rbx,%r15
    +0x241b: cmovb   %r15,%rbx
    +0x241f: mov     %r13d,%eax
    +0x2422: lea     (%rsp,%rax,1),%rsi
    +0x2426: add     $0xc0,%rsi
    +0x242d: lea     (%rsp,%r12,1),%rdi
    +0x2431: add     $0x1360,%rdi
    +0x2438: mov     %rbx,%rdx
    +0x243b: call    <memcpy>
    +0x2440: add     %ebx,%r13d
    +0x2443: add     %rbx,%r12
    +0x2446: sub     %rbx,%r15
    +0x2449: je      <mldsa87_signature_internal+0x2480>
    +0x244b: cmp     $0x88,%r13d
    +0x2452: jne     <mldsa87_signature_internal+0x2410>
    +0x2454: lea     0xc0(%rsp),%r14
    +0x245c: mov     %r14,%rdi
    +0x245f: call    <mldsa_keccakf1600_permute>
    +0x2464: cmp     $0x88,%r15
    +0x246b: mov     $0x88,%ebx
    +0x2470: cmovb   %r15,%rbx
    +0x2474: xor     %r13d,%r13d
    +0x2477: mov     %r14,%rsi
    +0x247a: jmp     <mldsa87_signature_internal+0x242d>
    +0x247c: nopl    0x0(%rax)
    +0x2480: lea     0x1364(%rsp),%rax
    +0x2488: xor     %ecx,%ecx
    +0x248a: nopw    0x0(%rax,%rax,1)
    +0x2490: movzwl  -0x4(%rax),%edx
    +0x2494: movzbl  -0x2(%rax),%esi
    +0x2498: mov     %esi,%edi
    +0x249a: and     $0xf,%edi
    +0x249d: shl     $0x10,%edi
    +0x24a0: or      %edx,%edi
    +0x24a2: shr     $0x4,%esi
    +0x24a5: movzbl  -0x1(%rax),%edx
    +0x24a9: movzbl  (%rax),%r8d
    +0x24ad: mov     $0x80000,%r9d
    +0x24b3: sub     %edi,%r9d
    +0x24b6: mov     %r9d,0x340(%rsp,%rcx,8)
    +0x24be: shl     $0xc,%r8d
    +0x24c2: shl     $0x4,%edx
    +0x24c5: or      %esi,%edx
    +0x24c7: or      %r8d,%edx
    +0x24ca: mov     $0x80000,%esi
    +0x24cf: sub     %edx,%esi
    +0x24d1: mov     %esi,0x344(%rsp,%rcx,8)
    +0x24d8: inc     %rcx
    +0x24db: add     $0x5,%rax
    +0x24df: cmp     $0x80,%rcx
    +0x24e6: jne     <mldsa87_signature_internal+0x2490>
    +0x24e8: pxor    %xmm0,%xmm0
    +0x24ec: movdqa  %xmm0,0x180(%rsp)
    +0x24f5: movdqa  %xmm0,0x170(%rsp)
    +0x24fe: movdqa  %xmm0,0x160(%rsp)
    +0x2507: movdqa  %xmm0,0x150(%rsp)
    +0x2510: movdqa  %xmm0,0x140(%rsp)
    +0x2519: movdqa  %xmm0,0x130(%rsp)
    +0x2522: movdqa  %xmm0,0x120(%rsp)
    +0x252b: movdqa  %xmm0,0x110(%rsp)
    +0x2534: movdqa  %xmm0,0x100(%rsp)
    +0x253d: movdqa  %xmm0,0xf0(%rsp)
    +0x2546: movdqa  %xmm0,0xe0(%rsp)
    +0x254f: movdqa  %xmm0,0xd0(%rsp)
    +0x2558: movdqa  %xmm0,0xc0(%rsp)
    +0x2561: lea     0xc0(%rsp),%rax
    +0x2569: mov     $0x2a8,%edx
    +0x256e: lea     0x1360(%rsp),%rbx
    +0x2576: mov     %rbx,%rdi
    +0x2579: xor     %esi,%esi
    +0x257b: call    <memset>
    +0x2580: pxor    %xmm5,%xmm5
    +0x2584: movdqa  %xmm5,0x1d0(%rsp)
    +0x258d: movdqa  %xmm5,0x1c0(%rsp)
    +0x2596: movdqa  %xmm5,0x1b0(%rsp)
    +0x259f: movdqa  %xmm5,0x1a0(%rsp)
    +0x25a8: movw    $0x0,0x1e0(%rsp)
    +0x25b2: lea     0x1a0(%rsp),%rax
    +0x25ba: mov     $0xc,%eax
    +0x25bf: movabs  $0x380200100000000,%r14
    +0x25c9: mov     0xb8(%rsp),%r12
    +0x25d1: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x25e0: movdqa  0x310(%rsp,%rax,4),%xmm0
    +0x25e9: movdqa  0x320(%rsp,%rax,4),%xmm1
    +0x25f2: movdqa  0x330(%rsp,%rax,4),%xmm2
    +0x25fb: movdqa  0x340(%rsp,%rax,4),%xmm3
    +0x2604: paddd   0xb10(%rsp,%rax,4),%xmm0
    +0x260d: paddd   0xb20(%rsp,%rax,4),%xmm1
    +0x2616: movdqa  %xmm0,0xb10(%rsp,%rax,4)
    +0x261f: movdqa  %xmm1,0xb20(%rsp,%rax,4)
    +0x2628: paddd   0xb30(%rsp,%rax,4),%xmm2
    +0x2631: paddd   0xb40(%rsp,%rax,4),%xmm3
    +0x263a: movdqa  %xmm2,0xb30(%rsp,%rax,4)
    +0x2643: movdqa  %xmm3,0xb40(%rsp,%rax,4)
    +0x264c: add     $0x10,%rax
    +0x2650: cmp     $0x10c,%rax
    +0x2656: jne     <mldsa87_signature_internal+0x25e0>
    +0x2658: mov     $0x4,%eax
    +0x265d: movdqa  0xa50b(%rip),%xmm6
    +0x2665: movdqa  0xa513(%rip),%xmm7
    +0x266d: mov     0x38(%rsp),%r8
    +0x2672: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x2680: movdqa  0xb30(%rsp,%rax,4),%xmm0
    +0x2689: movdqa  0xb40(%rsp,%rax,4),%xmm1
    +0x2692: movdqa  %xmm0,%xmm2
    +0x2696: paddd   %xmm6,%xmm2
    +0x269a: movdqa  %xmm1,%xmm3
    +0x269e: paddd   %xmm6,%xmm3
    +0x26a2: psrad   $0x17,%xmm2
    +0x26a7: psrad   $0x17,%xmm3
    +0x26ac: pshufd  $0xf5,%xmm2,%xmm4
    +0x26b1: pmuludq %xmm7,%xmm2
    +0x26b5: pshufd  $0xe8,%xmm2,%xmm2
    +0x26ba: pmuludq %xmm7,%xmm4
    +0x26be: pshufd  $0xe8,%xmm4,%xmm4
    +0x26c3: punpckldq %xmm4,%xmm2
    +0x26c7: pshufd  $0xf5,%xmm3,%xmm4
    +0x26cc: pmuludq %xmm7,%xmm3
    +0x26d0: pshufd  $0xe8,%xmm3,%xmm3
    +0x26d5: pmuludq %xmm7,%xmm4
    +0x26d9: pshufd  $0xe8,%xmm4,%xmm4
    +0x26de: punpckldq %xmm4,%xmm3
    +0x26e2: paddd   %xmm0,%xmm2
    +0x26e6: paddd   %xmm1,%xmm3
    +0x26ea: movdqa  %xmm2,0xb30(%rsp,%rax,4)
    +0x26f3: movdqa  %xmm3,0xb40(%rsp,%rax,4)
    +0x26fc: add     $0x8,%rax
    +0x2700: cmp     $0x104,%rax
    +0x2706: jne     <mldsa87_signature_internal+0x2680>
    +0x270c: xor     %eax,%eax
    +0x270e: xor     %ecx,%ecx
    +0x2710: movslq  0xb40(%rsp,%rcx,4),%rdx
    +0x2718: mov     %edx,%esi
    +0x271a: neg     %esi
    +0x271c: mov     %rdx,%rdi
    +0x271f: shr     $0x1f,%rdi
    +0x2723: xor     %edx,%esi
    +0x2725: and     %edi,%esi
    +0x2727: xor     %edx,%esi
    +0x2729: mov     $0x7ff87,%edx
    +0x272e: sub     %esi,%edx
    +0x2730: movslq  %edx,%rdx
    +0x2733: shr     $0x1f,%rdx
    +0x2737: or      %edx,%eax
    +0x2739: inc     %rcx
    +0x273c: cmp     $0x100,%rcx
    +0x2743: jne     <mldsa87_signature_internal+0x2710>
    +0x2745: test    %eax,%eax
    +0x2747: jne     <mldsa87_signature_internal+0x30a0>
    +0x274d: mov     %r8,%rax
    +0x2750: xor     %ecx,%ecx
    +0x2752: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x2760: mov     $0x80000,%edx
    +0x2765: sub     0xb40(%rsp,%rcx,8),%edx
    +0x276c: mov     $0x80000,%esi
    +0x2771: sub     0xb44(%rsp,%rcx,8),%esi
    +0x2778: mov     %dx,-0x3(%rax)
    +0x277c: shr     $0x10,%edx
    +0x277f: mov     %esi,%edi
    +0x2781: shl     $0x4,%edi
    +0x2784: or      %edx,%edi
    +0x2786: mov     %dil,-0x1(%rax)
    +0x278a: shr     $0x4,%esi
    +0x278d: mov     %si,(%rax)
    +0x2790: inc     %rcx
    +0x2793: add     $0x5,%rax
    +0x2797: cmp     $0x80,%rcx
    +0x279e: jne     <mldsa87_signature_internal+0x2760>
    +0x27a0: movdqa  %xmm5,0x1360(%rsp)
    +0x27a9: lea     0x1360(%rsp),%rax
    +0x27b1: inc     %r12
    +0x27b4: mov     0x30(%rsp),%rcx
    +0x27b9: add     $0x60,%rcx
    +0x27bd: add     $0x280,%r8
    +0x27c4: cmp     $0x7,%r12
    +0x27c8: jne     <mldsa87_signature_internal+0x20c0>
    +0x27ce: movl    $0x0,0x30(%rsp)
    +0x27d6: mov     $0x2,%r14d
    +0x27dc: mov     $0xc,%r15d
    +0x27e2: lea     0x1a20(%rsp),%rbx
    +0x27ea: xor     %eax,%eax
    +0x27ec: nopl    0x0(%rax)
    +0x27f0: mov     %rax,0x38(%rsp)
    +0x27f5: mov     0x40(%rsp),%rax
    +0x27fa: add     %r14,%rax
    +0x27fd: xor     %ecx,%ecx
    +0x27ff: nop     
    +0x2800: movzbl  -0x2(%rax),%edx
    +0x2804: and     $0x7,%edx
    +0x2807: mov     %edx,0x340(%rsp,%rcx,1)
    +0x280e: movzbl  -0x2(%rax),%esi
    +0x2812: shr     $0x3,%esi
    +0x2815: and     $0x7,%esi
    +0x2818: mov     %esi,0x344(%rsp,%rcx,1)
    +0x281f: movzbl  -0x2(%rax),%edi
    +0x2823: shr     $0x6,%edi
    +0x2826: movzbl  -0x1(%rax),%r8d
    +0x282b: and     $0x1,%r8d
    +0x282f: lea     (%rdi,%r8,4),%r8d
    +0x2833: mov     %r8d,0x348(%rsp,%rcx,1)
    +0x283b: movzbl  -0x1(%rax),%edi
    +0x283f: shr     $1,%edi
    +0x2841: and     $0x7,%edi
    +0x2844: mov     %edi,0x34c(%rsp,%rcx,1)
    +0x284b: movzbl  -0x1(%rax),%r9d
    +0x2850: shr     $0x4,%r9d
    +0x2854: and     $0x7,%r9d
    +0x2858: mov     %r9d,0x350(%rsp,%rcx,1)
    +0x2860: movzbl  -0x1(%rax),%r10d
    +0x2865: shr     $0x7,%r10d
    +0x2869: movzbl  (%rax),%r11d
    +0x286d: and     $0x3,%r11d
    +0x2871: lea     (%r10,%r11,2),%r10d
    +0x2875: mov     %r10d,0x354(%rsp,%rcx,1)
    +0x287d: movzbl  (%rax),%r11d
    +0x2881: shr     $0x2,%r11d
    +0x2885: and     $0x7,%r11d
    +0x2889: mov     %r11d,0x358(%rsp,%rcx,1)
    +0x2891: movzbl  (%rax),%r12d
    +0x2895: shr     $0x5,%r12d
    +0x2899: mov     $0x2,%r13d
    +0x289f: sub     %edx,%r13d
    +0x28a2: mov     %r13d,0x340(%rsp,%rcx,1)
    +0x28aa: mov     $0x2,%edx
    +0x28af: sub     %esi,%edx
    +0x28b1: mov     %edx,0x344(%rsp,%rcx,1)
    +0x28b8: mov     $0x2,%edx
    +0x28bd: sub     %r8d,%edx
    +0x28c0: mov     %edx,0x348(%rsp,%rcx,1)
    +0x28c7: mov     $0x2,%edx
    +0x28cc: sub     %edi,%edx
    +0x28ce: mov     %edx,0x34c(%rsp,%rcx,1)
    +0x28d5: mov     $0x2,%edx
    +0x28da: sub     %r9d,%edx
    +0x28dd: mov     %edx,0x350(%rsp,%rcx,1)
    +0x28e4: mov     $0x2,%edx
    +0x28e9: sub     %r10d,%edx
    +0x28ec: mov     %edx,0x354(%rsp,%rcx,1)
    +0x28f3: mov     $0x2,%edx
    +0x28f8: sub     %r11d,%edx
    +0x28fb: mov     %edx,0x358(%rsp,%rcx,1)
    +0x2902: mov     $0x2,%edx
    +0x2907: sub     %r12d,%edx
    +0x290a: mov     %edx,0x35c(%rsp,%rcx,1)
    +0x2911: add     $0x20,%rcx
    +0x2915: add     $0x3,%rax
    +0x2919: cmp     $0x400,%rcx
    +0x2920: jne     <mldsa87_signature_internal+0x2800>
    +0x2926: lea     0x340(%rsp),%rdi
    +0x292e: call    <mldsa_poly_ntt>
    +0x2933: mov     $0x1,%eax
    +0x2938: movabs  $0x380200100000000,%rsi
    +0x2942: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x2950: movslq  0x33c(%rsp,%rax,4),%rcx
    +0x2958: movslq  0x73c(%rsp,%rax,4),%rdx
    +0x2960: imul    %rcx,%rdx
    +0x2964: mov     %rdx,%rcx
    +0x2967: imul    %rsi,%rcx
    +0x296b: sar     $0x20,%rcx
    +0x296f: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x2976: add     %rdx,%rcx
    +0x2979: shr     $0x20,%rcx
    +0x297d: mov     %ecx,0x33c(%rsp,%rax,4)
    +0x2984: movslq  0x340(%rsp,%rax,4),%rcx
    +0x298c: movslq  0x740(%rsp,%rax,4),%rdx
    +0x2994: imul    %rcx,%rdx
    +0x2998: mov     %rdx,%rcx
    +0x299b: imul    %rsi,%rcx
    +0x299f: sar     $0x20,%rcx
    +0x29a3: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x29aa: add     %rdx,%rcx
    +0x29ad: shr     $0x20,%rcx
    +0x29b1: mov     %ecx,0x340(%rsp,%rax,4)
    +0x29b8: add     $0x2,%rax
    +0x29bc: cmp     $0x101,%rax
    +0x29c2: jne     <mldsa87_signature_internal+0x2950>
    +0x29c4: lea     0x340(%rsp),%rdi
    +0x29cc: call    <mldsa_poly_invntt_tomont>
    +0x29d1: mov     $0xc,%eax
    +0x29d6: cs      nopw 0x0(%rax,%rax,1)
    +0x29e0: movdqa  -0x30(%rbx,%rax,4),%xmm0
    +0x29e6: movdqa  -0x20(%rbx,%rax,4),%xmm1
    +0x29ec: movdqa  -0x10(%rbx,%rax,4),%xmm2
    +0x29f2: movdqa  (%rbx,%rax,4),%xmm3
    +0x29f7: psubd   0x310(%rsp,%rax,4),%xmm0
    +0x2a00: psubd   0x320(%rsp,%rax,4),%xmm1
    +0x2a09: movdqa  %xmm0,-0x30(%rbx,%rax,4)
    +0x2a0f: movdqa  %xmm1,-0x20(%rbx,%rax,4)
    +0x2a15: psubd   0x330(%rsp,%rax,4),%xmm2
    +0x2a1e: psubd   0x340(%rsp,%rax,4),%xmm3
    +0x2a27: movdqa  %xmm2,-0x10(%rbx,%rax,4)
    +0x2a2d: movdqa  %xmm3,(%rbx,%rax,4)
    +0x2a32: add     $0x10,%rax
    +0x2a36: cmp     $0x10c,%rax
    +0x2a3c: jne     <mldsa87_signature_internal+0x29e0>
    +0x2a3e: mov     $0x4,%eax
    +0x2a43: movdqa  0xa125(%rip),%xmm5
    +0x2a4b: movdqa  0xa12d(%rip),%xmm6
    +0x2a53: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x2a60: movdqa  -0x10(%rbx,%rax,4),%xmm0
    +0x2a66: movdqa  (%rbx,%rax,4),%xmm1
    +0x2a6b: movdqa  %xmm0,%xmm2
    +0x2a6f: paddd   %xmm5,%xmm2
    +0x2a73: movdqa  %xmm1,%xmm3
    +0x2a77: paddd   %xmm5,%xmm3
    +0x2a7b: psrad   $0x17,%xmm2
    +0x2a80: psrad   $0x17,%xmm3
    +0x2a85: pshufd  $0xf5,%xmm2,%xmm4
    +0x2a8a: pmuludq %xmm6,%xmm2
    +0x2a8e: pshufd  $0xe8,%xmm2,%xmm2
    +0x2a93: pmuludq %xmm6,%xmm4
    +0x2a97: pshufd  $0xe8,%xmm4,%xmm4
    +0x2a9c: punpckldq %xmm4,%xmm2
    +0x2aa0: pshufd  $0xf5,%xmm3,%xmm4
    +0x2aa5: pmuludq %xmm6,%xmm3
    +0x2aa9: pshufd  $0xe8,%xmm3,%xmm3
    +0x2aae: pmuludq %xmm6,%xmm4
    +0x2ab2: pshufd  $0xe8,%xmm4,%xmm4
    +0x2ab7: punpckldq %xmm4,%xmm3
    +0x2abb: paddd   %xmm0,%xmm2
    +0x2abf: paddd   %xmm1,%xmm3
    +0x2ac3: movdqa  %xmm2,-0x10(%rbx,%rax,4)
    +0x2ac9: movdqa  %xmm3,(%rbx,%rax,4)
    +0x2ace: add     $0x8,%rax
    +0x2ad2: cmp     $0x104,%rax
    +0x2ad8: jne     <mldsa87_signature_internal+0x2a60>
    +0x2ada: xor     %eax,%eax
    +0x2adc: xor     %ecx,%ecx
    +0x2ade: xchg    %ax,%ax
    +0x2ae0: movslq  (%rbx,%rcx,4),%rdx
    +0x2ae4: mov     %edx,%esi
    +0x2ae6: neg     %esi
    +0x2ae8: mov     %rdx,%rdi
    +0x2aeb: shr     $0x1f,%rdi
    +0x2aef: xor     %edx,%esi
    +0x2af1: and     %edi,%esi
    +0x2af3: xor     %edx,%esi
    +0x2af5: mov     $0x3fe87,%edx
    +0x2afa: sub     %esi,%edx
    +0x2afc: movslq  %edx,%rdx
    +0x2aff: shr     $0x1f,%rdx
    +0x2b03: or      %edx,%eax
    +0x2b05: inc     %rcx
    +0x2b08: cmp     $0x100,%rcx
    +0x2b0f: jne     <mldsa87_signature_internal+0x2ae0>
    +0x2b11: test    %eax,%eax
    +0x2b13: jne     <mldsa87_signature_internal+0x30a8>
    +0x2b19: mov     0x60(%rsp),%rax
    +0x2b1e: mov     %r15,0xb8(%rsp)
    +0x2b26: add     %r15,%rax
    +0x2b29: mov     $0x1c,%ecx
    +0x2b2e: xchg    %ax,%ax
    +0x2b30: movzbl  -0xc(%rax),%esi
    +0x2b34: mov     %esi,0x324(%rsp,%rcx,1)
    +0x2b3b: movzbl  -0xb(%rax),%edx
    +0x2b3f: and     $0x1f,%edx
    +0x2b42: shl     $0x8,%edx
    +0x2b45: or      %esi,%edx
    +0x2b47: mov     %edx,0x324(%rsp,%rcx,1)
    +0x2b4e: movzbl  -0xb(%rax),%esi
    +0x2b52: shr     $0x5,%esi
    +0x2b55: mov     %esi,0x328(%rsp,%rcx,1)
    +0x2b5c: movzbl  -0xa(%rax),%edi
    +0x2b60: lea     (%rsi,%rdi,8),%edi
    +0x2b63: mov     %edi,0x328(%rsp,%rcx,1)
    +0x2b6a: movzbl  -0x9(%rax),%esi
    +0x2b6e: and     $0x3,%esi
    +0x2b71: shl     $0xb,%esi
    +0x2b74: or      %edi,%esi
    +0x2b76: mov     %esi,0x328(%rsp,%rcx,1)
    +0x2b7d: movzbl  -0x9(%rax),%r8d
    +0x2b82: shr     $0x2,%r8d
    +0x2b86: mov     %r8d,0x32c(%rsp,%rcx,1)
    +0x2b8e: movzbl  -0x8(%rax),%edi
    +0x2b92: and     $0x7f,%edi
    +0x2b95: shl     $0x6,%edi
    +0x2b98: or      %r8d,%edi
    +0x2b9b: mov     %edi,0x32c(%rsp,%rcx,1)
    +0x2ba2: movzbl  -0x8(%rax),%r8d
    +0x2ba7: shr     $0x7,%r8d
    +0x2bab: mov     %r8d,0x330(%rsp,%rcx,1)
    +0x2bb3: movzbl  -0x7(%rax),%r9d
    +0x2bb8: lea     (%r8,%r9,2),%r9d
    +0x2bbc: mov     %r9d,0x330(%rsp,%rcx,1)
    +0x2bc4: movzbl  -0x6(%rax),%r8d
    +0x2bc9: and     $0xf,%r8d
    +0x2bcd: shl     $0x9,%r8d
    +0x2bd1: or      %r9d,%r8d
    +0x2bd4: mov     %r8d,0x330(%rsp,%rcx,1)
    +0x2bdc: movzbl  -0x6(%rax),%r9d
    +0x2be1: shr     $0x4,%r9d
    +0x2be5: mov     %r9d,0x334(%rsp,%rcx,1)
    +0x2bed: movzbl  -0x5(%rax),%r10d
    +0x2bf2: shl     $0x4,%r10d
    +0x2bf6: or      %r9d,%r10d
    +0x2bf9: mov     %r10d,0x334(%rsp,%rcx,1)
    +0x2c01: movzbl  -0x4(%rax),%r9d
    +0x2c06: and     $0x1,%r9d
    +0x2c0a: shl     $0xc,%r9d
    +0x2c0e: or      %r10d,%r9d
    +0x2c11: mov     %r9d,0x334(%rsp,%rcx,1)
    +0x2c19: movzbl  -0x4(%rax),%r11d
    +0x2c1e: shr     $1,%r11d
    +0x2c21: mov     %r11d,0x338(%rsp,%rcx,1)
    +0x2c29: movzbl  -0x3(%rax),%r10d
    +0x2c2e: and     $0x3f,%r10d
    +0x2c32: shl     $0x7,%r10d
    +0x2c36: or      %r11d,%r10d
    +0x2c39: mov     %r10d,0x338(%rsp,%rcx,1)
    +0x2c41: movzbl  -0x3(%rax),%r11d
    +0x2c46: shr     $0x6,%r11d
    +0x2c4a: mov     %r11d,0x33c(%rsp,%rcx,1)
    +0x2c52: movzbl  -0x2(%rax),%r12d
    +0x2c57: lea     (%r11,%r12,4),%r12d
    +0x2c5b: mov     %r12d,0x33c(%rsp,%rcx,1)
    +0x2c63: movzbl  -0x1(%rax),%r11d
    +0x2c68: and     $0x7,%r11d
    +0x2c6c: shl     $0xa,%r11d
    +0x2c70: or      %r12d,%r11d
    +0x2c73: mov     %r11d,0x33c(%rsp,%rcx,1)
    +0x2c7b: movzbl  -0x1(%rax),%r12d
    +0x2c80: shr     $0x3,%r12d
    +0x2c84: mov     %r12d,0x340(%rsp,%rcx,1)
    +0x2c8c: movzbl  (%rax),%r13d
    +0x2c90: shl     $0x5,%r13d
    +0x2c94: mov     $0x1000,%r15d
    +0x2c9a: sub     %edx,%r15d
    +0x2c9d: mov     %r15d,0x324(%rsp,%rcx,1)
    +0x2ca5: mov     $0x1000,%edx
    +0x2caa: sub     %esi,%edx
    +0x2cac: mov     %edx,0x328(%rsp,%rcx,1)
    +0x2cb3: mov     $0x1000,%edx
    +0x2cb8: sub     %edi,%edx
    +0x2cba: mov     %edx,0x32c(%rsp,%rcx,1)
    +0x2cc1: mov     $0x1000,%edx
    +0x2cc6: sub     %r8d,%edx
    +0x2cc9: mov     %edx,0x330(%rsp,%rcx,1)
    +0x2cd0: mov     $0x1000,%edx
    +0x2cd5: sub     %r9d,%edx
    +0x2cd8: mov     %edx,0x334(%rsp,%rcx,1)
    +0x2cdf: mov     $0x1000,%edx
    +0x2ce4: sub     %r10d,%edx
    +0x2ce7: mov     %edx,0x338(%rsp,%rcx,1)
    +0x2cee: mov     $0x1000,%edx
    +0x2cf3: sub     %r11d,%edx
    +0x2cf6: mov     %edx,0x33c(%rsp,%rcx,1)
    +0x2cfd: or      %r12d,%r13d
    +0x2d00: mov     $0x1000,%edx
    +0x2d05: sub     %r13d,%edx
    +0x2d08: mov     %edx,0x340(%rsp,%rcx,1)
    +0x2d0f: add     $0x20,%rcx
    +0x2d13: add     $0xd,%rax
    +0x2d17: cmp     $0x41c,%rcx
    +0x2d1e: jne     <mldsa87_signature_internal+0x2b30>
    +0x2d24: lea     0x340(%rsp),%rdi
    +0x2d2c: call    <mldsa_poly_ntt>
    +0x2d31: mov     $0x1,%eax
    +0x2d36: movabs  $0x380200100000000,%rsi
    +0x2d40: movslq  0x33c(%rsp,%rax,4),%rcx
    +0x2d48: movslq  0x73c(%rsp,%rax,4),%rdx
    +0x2d50: imul    %rcx,%rdx
    +0x2d54: mov     %rdx,%rcx
    +0x2d57: imul    %rsi,%rcx
    +0x2d5b: sar     $0x20,%rcx
    +0x2d5f: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x2d66: add     %rdx,%rcx
    +0x2d69: shr     $0x20,%rcx
    +0x2d6d: mov     %ecx,0x33c(%rsp,%rax,4)
    +0x2d74: movslq  0x340(%rsp,%rax,4),%rcx
    +0x2d7c: movslq  0x740(%rsp,%rax,4),%rdx
    +0x2d84: imul    %rcx,%rdx
    +0x2d88: mov     %rdx,%rcx
    +0x2d8b: imul    %rsi,%rcx
    +0x2d8f: sar     $0x20,%rcx
    +0x2d93: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x2d9a: add     %rdx,%rcx
    +0x2d9d: shr     $0x20,%rcx
    +0x2da1: mov     %ecx,0x340(%rsp,%rax,4)
    +0x2da8: add     $0x2,%rax
    +0x2dac: cmp     $0x101,%rax
    +0x2db2: jne     <mldsa87_signature_internal+0x2d40>
    +0x2db4: lea     0x340(%rsp),%rdi
    +0x2dbc: call    <mldsa_poly_invntt_tomont>
    +0x2dc1: xor     %eax,%eax
    +0x2dc3: movdqa  0x9da5(%rip),%xmm5
    +0x2dcb: movdqa  0x9dad(%rip),%xmm6
    +0x2dd3: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x2de0: movdqa  0x340(%rsp,%rax,4),%xmm0
    +0x2de9: movdqa  0x350(%rsp,%rax,4),%xmm1
    +0x2df2: movdqa  %xmm0,%xmm2
    +0x2df6: paddd   %xmm5,%xmm2
    +0x2dfa: movdqa  %xmm1,%xmm3
    +0x2dfe: paddd   %xmm5,%xmm3
    +0x2e02: psrad   $0x17,%xmm2
    +0x2e07: psrad   $0x17,%xmm3
    +0x2e0c: pshufd  $0xf5,%xmm2,%xmm4
    +0x2e11: pmuludq %xmm6,%xmm2
    +0x2e15: pshufd  $0xe8,%xmm2,%xmm2
    +0x2e1a: pmuludq %xmm6,%xmm4
    +0x2e1e: pshufd  $0xe8,%xmm4,%xmm4
    +0x2e23: punpckldq %xmm4,%xmm2
    +0x2e27: pshufd  $0xf5,%xmm3,%xmm4
    +0x2e2c: pmuludq %xmm6,%xmm3
    +0x2e30: pshufd  $0xe8,%xmm3,%xmm3
    +0x2e35: pmuludq %xmm6,%xmm4
    +0x2e39: pshufd  $0xe8,%xmm4,%xmm4
    +0x2e3e: punpckldq %xmm4,%xmm3
    +0x2e42: paddd   %xmm0,%xmm2
    +0x2e46: paddd   %xmm1,%xmm3
    +0x2e4a: movdqa  %xmm2,0x340(%rsp,%rax,4)
    +0x2e53: movdqa  %xmm3,0x350(%rsp,%rax,4)
    +0x2e5c: add     $0x8,%rax
    +0x2e60: cmp     $0x100,%rax
    +0x2e66: jne     <mldsa87_signature_internal+0x2de0>
    +0x2e6c: xor     %eax,%eax
    +0x2e6e: xor     %ecx,%ecx
    +0x2e70: pxor    %xmm4,%xmm4
    +0x2e74: data16  data16 cs nopw 0x0(%rax,%rax,1)
    +0x2e80: movslq  0x340(%rsp,%rcx,4),%rdx
    +0x2e88: mov     %edx,%esi
    +0x2e8a: neg     %esi
    +0x2e8c: mov     %rdx,%rdi
    +0x2e8f: shr     $0x1f,%rdi
    +0x2e93: xor     %edx,%esi
    +0x2e95: and     %edi,%esi
    +0x2e97: xor     %edx,%esi
    +0x2e99: mov     $0x3feff,%edx
    +0x2e9e: sub     %esi,%edx
    +0x2ea0: movslq  %edx,%rdx
    +0x2ea3: shr     $0x1f,%rdx
    +0x2ea7: or      %edx,%eax
    +0x2ea9: inc     %rcx
    +0x2eac: cmp     $0x100,%rcx
    +0x2eb3: jne     <mldsa87_signature_internal+0x2e80>
    +0x2eb5: test    %eax,%eax
    +0x2eb7: movdqa  0x9f91(%rip),%xmm5
    +0x2ebf: mov     0xb8(%rsp),%r15
    +0x2ec7: jne     <mldsa87_signature_internal+0x30a8>
    +0x2ecd: mov     $0xc,%eax
    +0x2ed2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x2ee0: movdqa  0x310(%rsp,%rax,4),%xmm0
    +0x2ee9: movdqa  0x320(%rsp,%rax,4),%xmm1
    +0x2ef2: paddd   -0x30(%rbx,%rax,4),%xmm0
    +0x2ef8: paddd   -0x20(%rbx,%rax,4),%xmm1
    +0x2efe: movdqa  %xmm0,-0x30(%rbx,%rax,4)
    +0x2f04: movdqa  %xmm1,-0x20(%rbx,%rax,4)
    +0x2f0a: movdqa  0x330(%rsp,%rax,4),%xmm0
    +0x2f13: movdqa  0x340(%rsp,%rax,4),%xmm1
    +0x2f1c: paddd   -0x10(%rbx,%rax,4),%xmm0
    +0x2f22: paddd   (%rbx,%rax,4),%xmm1
    +0x2f27: movdqa  %xmm0,-0x10(%rbx,%rax,4)
    +0x2f2d: movdqa  %xmm1,(%rbx,%rax,4)
    +0x2f32: add     $0x10,%rax
    +0x2f36: cmp     $0x10c,%rax
    +0x2f3c: jne     <mldsa87_signature_internal+0x2ee0>
    +0x2f3e: mov     0x38(%rsp),%rax
    +0x2f43: inc     %rax
    +0x2f46: add     $0x60,%r14
    +0x2f4a: add     $0x400,%rbx
    +0x2f51: add     $0x1a0,%r15
    +0x2f58: cmp     $0x8,%rax
    +0x2f5c: jne     <mldsa87_signature_internal+0x27f0>
    +0x2f62: movaps  0x200(%rsp),%xmm0
    +0x2f6a: movaps  0x210(%rsp),%xmm1
    +0x2f72: movaps  0x220(%rsp),%xmm2
    +0x2f7a: movaps  0x230(%rsp),%xmm3
    +0x2f82: mov     0x20(%rsp),%rax
    +0x2f87: movups  %xmm3,0x30(%rax)
    +0x2f8b: movups  %xmm2,0x20(%rax)
    +0x2f8f: movups  %xmm1,0x10(%rax)
    +0x2f93: movups  %xmm0,(%rax)
    +0x2f96: mov     0x28(%rsp),%rax
    +0x2f9b: movdqu  %xmm4,0x40(%rax)
    +0x2fa0: movdqu  %xmm4,0x30(%rax)
    +0x2fa5: movdqu  %xmm4,0x20(%rax)
    +0x2faa: movdqu  %xmm4,0x10(%rax)
    +0x2faf: movdqu  %xmm4,(%rax)
    +0x2fb3: movl    $0x0,0x4f(%rax)
    +0x2fba: xor     %eax,%eax
    +0x2fbc: nopl    0x0(%rax)
    +0x2fc0: movd    0x1620(%rsp,%rax,1),%xmm0
    +0x2fc9: movzwl  0x1622(%rsp,%rax,1),%ecx
    +0x2fd1: movd    %ecx,%xmm1
    +0x2fd5: movdqa  %xmm0,%xmm2
    +0x2fd9: psrlw   $0x4,%xmm2
    +0x2fde: movdqa  %xmm1,%xmm3
    +0x2fe2: psrlw   $0x4,%xmm3
    +0x2fe7: punpcklbw %xmm2,%xmm0
    +0x2feb: pand    %xmm5,%xmm0
    +0x2fef: punpcklbw %xmm4,%xmm0
    +0x2ff3: punpcklwd %xmm4,%xmm0
    +0x2ff7: movdqa  %xmm0,0x340(%rsp,%rax,8)
    +0x3000: punpcklbw %xmm3,%xmm1
    +0x3004: pand    %xmm5,%xmm1
    +0x3008: punpcklbw %xmm4,%xmm1
    +0x300c: punpcklwd %xmm4,%xmm1
    +0x3010: movdqa  %xmm1,0x350(%rsp,%rax,8)
    +0x3019: add     $0x4,%rax
    +0x301d: cmp     $0x80,%rax
    +0x3023: jne     <mldsa87_signature_internal+0x2fc0>
    +0x3025: xor     %eax,%eax
    +0x3027: xor     %ecx,%ecx
    +0x3029: jmp     <mldsa87_signature_internal+0x3051>
    +0x302b: nopl    0x0(%rax,%rax,1)
    +0x3030: cmp     $0x4b,%eax
    +0x3033: je      <mldsa87_signature_internal+0x30a8>
    +0x3035: mov     %eax,%edx
    +0x3037: mov     0x28(%rsp),%rsi
    +0x303c: mov     %cl,(%rsi,%rdx,1)
    +0x303f: inc     %eax
    +0x3041: inc     %rcx
    +0x3044: cmp     $0x100,%rcx
    +0x304b: je      <mldsa87_signature_internal+0x3183>
    +0x3051: mov     0x1a20(%rsp,%rcx,4),%edi
    +0x3058: sub     $0xfffc0100,%edi
    +0x305e: setne   %dl
    +0x3061: cmpl    $0x0,0x340(%rsp,%rcx,4)
    +0x3069: sete    %sil
    +0x306d: cmp     $0x7fe00,%edi
    +0x3073: ja      <mldsa87_signature_internal+0x3030>
    +0x3075: or      %sil,%dl
    +0x3078: jne     <mldsa87_signature_internal+0x3041>
    +0x307a: jmp     <mldsa87_signature_internal+0x3030>
    +0x307c: nopl    0x0(%rax)
    +0x3080: movzbl  (%r15,%rax,1),%ecx
    +0x3085: xor     %cl,0x740(%rsp,%rax,1)
    +0x308c: inc     %rax
    +0x308f: cmp     %rax,%rbx
    +0x3092: jne     <mldsa87_signature_internal+0x3080>
    +0x3094: jmp     <mldsa87_signature_internal+0x1f25>
    +0x3099: nopl    0x0(%rax)
    +0x30a0: movl    $0x0,0x30(%rsp)
    +0x30a8: xor     %ebx,%ebx
    +0x30aa: mov     $0x400,%edx
    +0x30af: lea     0xb40(%rsp),%r14
    +0x30b7: mov     %r14,%rdi
    +0x30ba: xor     %esi,%esi
    +0x30bc: call    <memset>
    +0x30c1: mov     $0x400,%edx
    +0x30c6: lea     0x740(%rsp),%r14
    +0x30ce: mov     %r14,%rdi
    +0x30d1: xor     %esi,%esi
    +0x30d3: call    <memset>
    +0x30d8: mov     $0x2000,%edx
    +0x30dd: lea     0x1a20(%rsp),%r14
    +0x30e5: mov     %r14,%rdi
    +0x30e8: xor     %esi,%esi
    +0x30ea: call    <memset>
    +0x30ef: mov     $0x400,%edx
    +0x30f4: lea     0x1620(%rsp),%r14
    +0x30fc: mov     %r14,%rdi
    +0x30ff: xor     %esi,%esi
    +0x3101: call    <memset>
    +0x3106: mov     $0x400,%edx
    +0x310b: lea     0x340(%rsp),%r14
    +0x3113: mov     %r14,%rdi
    +0x3116: xor     %esi,%esi
    +0x3118: call    <memset>
    +0x311d: pxor    %xmm4,%xmm4
    +0x3121: movdqa  %xmm4,0xa0(%rsp)
    +0x312a: lea     0xa0(%rsp),%rax
    +0x3132: movdqa  %xmm4,0x230(%rsp)
    +0x313b: movdqa  %xmm4,0x220(%rsp)
    +0x3144: movdqa  %xmm4,0x210(%rsp)
    +0x314d: movdqa  %xmm4,0x200(%rsp)
    +0x3156: lea     0x200(%rsp),%rax
    +0x315e: test    %bl,%bl
    +0x3160: jne     <mldsa87_signature_internal+0x375a>
    +0x3166: mov     0x198(%rsp),%rcx
    +0x316e: inc     %ecx
    +0x3170: movzwl  %cx,%eax
    +0x3173: cmp     $0x2491,%eax
    +0x3178: jne     <mldsa87_signature_internal+0x1b0>
    +0x317e: jmp     <mldsa87_signature_internal+0x373e>
    +0x3183: mov     0x20(%rsp),%rcx
    +0x3188: mov     %al,0x120b(%rcx)
    +0x318e: xor     %ecx,%ecx
    +0x3190: movd    0x16a0(%rsp,%rcx,1),%xmm0
    +0x3199: movzwl  0x16a2(%rsp,%rcx,1),%edx
    +0x31a1: movd    %edx,%xmm1
    +0x31a5: movdqa  %xmm0,%xmm2
    +0x31a9: psrlw   $0x4,%xmm2
    +0x31ae: movdqa  %xmm1,%xmm3
    +0x31b2: psrlw   $0x4,%xmm3
    +0x31b7: punpcklbw %xmm2,%xmm0
    +0x31bb: pand    %xmm5,%xmm0
    +0x31bf: punpcklbw %xmm4,%xmm0
    +0x31c3: punpcklwd %xmm4,%xmm0
    +0x31c7: movdqa  %xmm0,0x340(%rsp,%rcx,8)
    +0x31d0: punpcklbw %xmm3,%xmm1
    +0x31d4: pand    %xmm5,%xmm1
    +0x31d8: punpcklbw %xmm4,%xmm1
    +0x31dc: punpcklwd %xmm4,%xmm1
    +0x31e0: movdqa  %xmm1,0x350(%rsp,%rcx,8)
    +0x31e9: add     $0x4,%rcx
    +0x31ed: cmp     $0x80,%rcx
    +0x31f4: jne     <mldsa87_signature_internal+0x3190>
    +0x31f6: xor     %ecx,%ecx
    +0x31f8: jmp     <mldsa87_signature_internal+0x320c>
    +0x31fa: nopw    0x0(%rax,%rax,1)
    +0x3200: inc     %rcx
    +0x3203: cmp     $0x100,%rcx
    +0x320a: je      <mldsa87_signature_internal+0x324c>
    +0x320c: mov     0x1e20(%rsp,%rcx,4),%edi
    +0x3213: sub     $0xfffc0100,%edi
    +0x3219: setne   %dl
    +0x321c: cmpl    $0x0,0x340(%rsp,%rcx,4)
    +0x3224: sete    %sil
    +0x3228: cmp     $0x7fe00,%edi
    +0x322e: ja      <mldsa87_signature_internal+0x3235>
    +0x3230: or      %sil,%dl
    +0x3233: jne     <mldsa87_signature_internal+0x3200>
    +0x3235: cmp     $0x4b,%eax
    +0x3238: je      <mldsa87_signature_internal+0x30a8>
    +0x323e: mov     %eax,%edx
    +0x3240: mov     0x28(%rsp),%rsi
    +0x3245: mov     %cl,(%rsi,%rdx,1)
    +0x3248: inc     %eax
    +0x324a: jmp     <mldsa87_signature_internal+0x3200>
    +0x324c: mov     0x20(%rsp),%rcx
    +0x3251: mov     %al,0x120c(%rcx)
    +0x3257: xor     %ecx,%ecx
    +0x3259: nopl    0x0(%rax)
    +0x3260: movd    0x1720(%rsp,%rcx,1),%xmm0
    +0x3269: movzwl  0x1722(%rsp,%rcx,1),%edx
    +0x3271: movd    %edx,%xmm1
    +0x3275: movdqa  %xmm0,%xmm2
    +0x3279: psrlw   $0x4,%xmm2
    +0x327e: movdqa  %xmm1,%xmm3
    +0x3282: psrlw   $0x4,%xmm3
    +0x3287: punpcklbw %xmm2,%xmm0
    +0x328b: pand    %xmm5,%xmm0
    +0x328f: punpcklbw %xmm4,%xmm0
    +0x3293: punpcklwd %xmm4,%xmm0
    +0x3297: movdqa  %xmm0,0x340(%rsp,%rcx,8)
    +0x32a0: punpcklbw %xmm3,%xmm1
    +0x32a4: pand    %xmm5,%xmm1
    +0x32a8: punpcklbw %xmm4,%xmm1
    +0x32ac: punpcklwd %xmm4,%xmm1
    +0x32b0: movdqa  %xmm1,0x350(%rsp,%rcx,8)
    +0x32b9: add     $0x4,%rcx
    +0x32bd: cmp     $0x80,%rcx
    +0x32c4: jne     <mldsa87_signature_internal+0x3260>
    +0x32c6: xor     %ecx,%ecx
    +0x32c8: jmp     <mldsa87_signature_internal+0x32dc>
    +0x32ca: nopw    0x0(%rax,%rax,1)
    +0x32d0: inc     %rcx
    +0x32d3: cmp     $0x100,%rcx
    +0x32da: je      <mldsa87_signature_internal+0x331c>
    +0x32dc: mov     0x2220(%rsp,%rcx,4),%edi
    +0x32e3: sub     $0xfffc0100,%edi
    +0x32e9: setne   %dl
    +0x32ec: cmpl    $0x0,0x340(%rsp,%rcx,4)
    +0x32f4: sete    %sil
    +0x32f8: cmp     $0x7fe00,%edi
    +0x32fe: ja      <mldsa87_signature_internal+0x3305>
    +0x3300: or      %sil,%dl
    +0x3303: jne     <mldsa87_signature_internal+0x32d0>
    +0x3305: cmp     $0x4b,%eax
    +0x3308: je      <mldsa87_signature_internal+0x30a8>
    +0x330e: mov     %eax,%edx
    +0x3310: mov     0x28(%rsp),%rsi
    +0x3315: mov     %cl,(%rsi,%rdx,1)
    +0x3318: inc     %eax
    +0x331a: jmp     <mldsa87_signature_internal+0x32d0>
    +0x331c: mov     0x20(%rsp),%rcx
    +0x3321: mov     %al,0x120d(%rcx)
    +0x3327: xor     %ecx,%ecx
    +0x3329: nopl    0x0(%rax)
    +0x3330: movd    0x17a0(%rsp,%rcx,1),%xmm0
    +0x3339: movzwl  0x17a2(%rsp,%rcx,1),%edx
    +0x3341: movd    %edx,%xmm1
    +0x3345: movdqa  %xmm0,%xmm2
    +0x3349: psrlw   $0x4,%xmm2
    +0x334e: movdqa  %xmm1,%xmm3
    +0x3352: psrlw   $0x4,%xmm3
    +0x3357: punpcklbw %xmm2,%xmm0
    +0x335b: pand    %xmm5,%xmm0
    +0x335f: punpcklbw %xmm4,%xmm0
    +0x3363: punpcklwd %xmm4,%xmm0
    +0x3367: movdqa  %xmm0,0x340(%rsp,%rcx,8)
    +0x3370: punpcklbw %xmm3,%xmm1
    +0x3374: pand    %xmm5,%xmm1
    +0x3378: punpcklbw %xmm4,%xmm1
    +0x337c: punpcklwd %xmm4,%xmm1
    +0x3380: movdqa  %xmm1,0x350(%rsp,%rcx,8)
    +0x3389: add     $0x4,%rcx
    +0x338d: cmp     $0x80,%rcx
    +0x3394: jne     <mldsa87_signature_internal+0x3330>
    +0x3396: xor     %ecx,%ecx
    +0x3398: jmp     <mldsa87_signature_internal+0x33ac>
    +0x339a: nopw    0x0(%rax,%rax,1)
    +0x33a0: inc     %rcx
    +0x33a3: cmp     $0x100,%rcx
    +0x33aa: je      <mldsa87_signature_internal+0x33ec>
    +0x33ac: mov     0x2620(%rsp,%rcx,4),%edi
    +0x33b3: sub     $0xfffc0100,%edi
    +0x33b9: setne   %dl
    +0x33bc: cmpl    $0x0,0x340(%rsp,%rcx,4)
    +0x33c4: sete    %sil
    +0x33c8: cmp     $0x7fe00,%edi
    +0x33ce: ja      <mldsa87_signature_internal+0x33d5>
    +0x33d0: or      %sil,%dl
    +0x33d3: jne     <mldsa87_signature_internal+0x33a0>
    +0x33d5: cmp     $0x4b,%eax
    +0x33d8: je      <mldsa87_signature_internal+0x30a8>
    +0x33de: mov     %eax,%edx
    +0x33e0: mov     0x28(%rsp),%rsi
    +0x33e5: mov     %cl,(%rsi,%rdx,1)
    +0x33e8: inc     %eax
    +0x33ea: jmp     <mldsa87_signature_internal+0x33a0>
    +0x33ec: mov     0x20(%rsp),%rcx
    +0x33f1: mov     %al,0x120e(%rcx)
    +0x33f7: xor     %ecx,%ecx
    +0x33f9: nopl    0x0(%rax)
    +0x3400: movd    0x1820(%rsp,%rcx,1),%xmm0
    +0x3409: movzwl  0x1822(%rsp,%rcx,1),%edx
    +0x3411: movd    %edx,%xmm1
    +0x3415: movdqa  %xmm0,%xmm2
    +0x3419: psrlw   $0x4,%xmm2
    +0x341e: movdqa  %xmm1,%xmm3
    +0x3422: psrlw   $0x4,%xmm3
    +0x3427: punpcklbw %xmm2,%xmm0
    +0x342b: pand    %xmm5,%xmm0
    +0x342f: punpcklbw %xmm4,%xmm0
    +0x3433: punpcklwd %xmm4,%xmm0
    +0x3437: movdqa  %xmm0,0x340(%rsp,%rcx,8)
    +0x3440: punpcklbw %xmm3,%xmm1
    +0x3444: pand    %xmm5,%xmm1
    +0x3448: punpcklbw %xmm4,%xmm1
    +0x344c: punpcklwd %xmm4,%xmm1
    +0x3450: movdqa  %xmm1,0x350(%rsp,%rcx,8)
    +0x3459: add     $0x4,%rcx
    +0x345d: cmp     $0x80,%rcx
    +0x3464: jne     <mldsa87_signature_internal+0x3400>
    +0x3466: xor     %ecx,%ecx
    +0x3468: jmp     <mldsa87_signature_internal+0x3491>
    +0x346a: nopw    0x0(%rax,%rax,1)
    +0x3470: cmp     $0x4b,%eax
    +0x3473: je      <mldsa87_signature_internal+0x30a8>
    +0x3479: mov     %eax,%edx
    +0x347b: mov     0x28(%rsp),%rsi
    +0x3480: mov     %cl,(%rsi,%rdx,1)
    +0x3483: inc     %eax
    +0x3485: inc     %rcx
    +0x3488: cmp     $0x100,%rcx
    +0x348f: je      <mldsa87_signature_internal+0x34bc>
    +0x3491: mov     0x2a20(%rsp,%rcx,4),%edi
    +0x3498: sub     $0xfffc0100,%edi
    +0x349e: setne   %dl
    +0x34a1: cmpl    $0x0,0x340(%rsp,%rcx,4)
    +0x34a9: sete    %sil
    +0x34ad: cmp     $0x7fe00,%edi
    +0x34b3: ja      <mldsa87_signature_internal+0x3470>
    +0x34b5: or      %sil,%dl
    +0x34b8: jne     <mldsa87_signature_internal+0x3485>
    +0x34ba: jmp     <mldsa87_signature_internal+0x3470>
    +0x34bc: mov     0x20(%rsp),%rcx
    +0x34c1: mov     %al,0x120f(%rcx)
    +0x34c7: xor     %ecx,%ecx
    +0x34c9: nopl    0x0(%rax)
    +0x34d0: movd    0x18a0(%rsp,%rcx,1),%xmm0
    +0x34d9: movzwl  0x18a2(%rsp,%rcx,1),%edx
    +0x34e1: movd    %edx,%xmm1
    +0x34e5: movdqa  %xmm0,%xmm2
    +0x34e9: psrlw   $0x4,%xmm2
    +0x34ee: movdqa  %xmm1,%xmm3
    +0x34f2: psrlw   $0x4,%xmm3
    +0x34f7: punpcklbw %xmm2,%xmm0
    +0x34fb: pand    %xmm5,%xmm0
    +0x34ff: punpcklbw %xmm4,%xmm0
    +0x3503: punpcklwd %xmm4,%xmm0
    +0x3507: movdqa  %xmm0,0x340(%rsp,%rcx,8)
    +0x3510: punpcklbw %xmm3,%xmm1
    +0x3514: pand    %xmm5,%xmm1
    +0x3518: punpcklbw %xmm4,%xmm1
    +0x351c: punpcklwd %xmm4,%xmm1
    +0x3520: movdqa  %xmm1,0x350(%rsp,%rcx,8)
    +0x3529: add     $0x4,%rcx
    +0x352d: cmp     $0x80,%rcx
    +0x3534: jne     <mldsa87_signature_internal+0x34d0>
    +0x3536: xor     %ecx,%ecx
    +0x3538: jmp     <mldsa87_signature_internal+0x354c>
    +0x353a: nopw    0x0(%rax,%rax,1)
    +0x3540: inc     %rcx
    +0x3543: cmp     $0x100,%rcx
    +0x354a: je      <mldsa87_signature_internal+0x358c>
    +0x354c: mov     0x2e20(%rsp,%rcx,4),%edi
    +0x3553: sub     $0xfffc0100,%edi
    +0x3559: setne   %dl
    +0x355c: cmpl    $0x0,0x340(%rsp,%rcx,4)
    +0x3564: sete    %sil
    +0x3568: cmp     $0x7fe00,%edi
    +0x356e: ja      <mldsa87_signature_internal+0x3575>
    +0x3570: or      %sil,%dl
    +0x3573: jne     <mldsa87_signature_internal+0x3540>
    +0x3575: cmp     $0x4b,%eax
    +0x3578: je      <mldsa87_signature_internal+0x30a8>
    +0x357e: mov     %eax,%edx
    +0x3580: mov     0x28(%rsp),%rsi
    +0x3585: mov     %cl,(%rsi,%rdx,1)
    +0x3588: inc     %eax
    +0x358a: jmp     <mldsa87_signature_internal+0x3540>
    +0x358c: mov     0x20(%rsp),%rcx
    +0x3591: mov     %al,0x1210(%rcx)
    +0x3597: xor     %ecx,%ecx
    +0x3599: nopl    0x0(%rax)
    +0x35a0: movd    0x1920(%rsp,%rcx,1),%xmm0
    +0x35a9: movzwl  0x1922(%rsp,%rcx,1),%edx
    +0x35b1: movd    %edx,%xmm1
    +0x35b5: movdqa  %xmm0,%xmm2
    +0x35b9: psrlw   $0x4,%xmm2
    +0x35be: movdqa  %xmm1,%xmm3
    +0x35c2: psrlw   $0x4,%xmm3
    +0x35c7: punpcklbw %xmm2,%xmm0
    +0x35cb: pand    %xmm5,%xmm0
    +0x35cf: punpcklbw %xmm4,%xmm0
    +0x35d3: punpcklwd %xmm4,%xmm0
    +0x35d7: movdqa  %xmm0,0x340(%rsp,%rcx,8)
    +0x35e0: punpcklbw %xmm3,%xmm1
    +0x35e4: pand    %xmm5,%xmm1
    +0x35e8: punpcklbw %xmm4,%xmm1
    +0x35ec: punpcklwd %xmm4,%xmm1
    +0x35f0: movdqa  %xmm1,0x350(%rsp,%rcx,8)
    +0x35f9: add     $0x4,%rcx
    +0x35fd: cmp     $0x80,%rcx
    +0x3604: jne     <mldsa87_signature_internal+0x35a0>
    +0x3606: xor     %ecx,%ecx
    +0x3608: jmp     <mldsa87_signature_internal+0x3631>
    +0x360a: nopw    0x0(%rax,%rax,1)
    +0x3610: cmp     $0x4b,%eax
    +0x3613: je      <mldsa87_signature_internal+0x30a8>
    +0x3619: mov     %eax,%edx
    +0x361b: mov     0x28(%rsp),%rsi
    +0x3620: mov     %cl,(%rsi,%rdx,1)
    +0x3623: inc     %eax
    +0x3625: inc     %rcx
    +0x3628: cmp     $0x100,%rcx
    +0x362f: je      <mldsa87_signature_internal+0x365c>
    +0x3631: mov     0x3220(%rsp,%rcx,4),%edi
    +0x3638: sub     $0xfffc0100,%edi
    +0x363e: setne   %dl
    +0x3641: cmpl    $0x0,0x340(%rsp,%rcx,4)
    +0x3649: sete    %sil
    +0x364d: cmp     $0x7fe00,%edi
    +0x3653: ja      <mldsa87_signature_internal+0x3610>
    +0x3655: or      %sil,%dl
    +0x3658: jne     <mldsa87_signature_internal+0x3625>
    +0x365a: jmp     <mldsa87_signature_internal+0x3610>
    +0x365c: mov     0x20(%rsp),%rcx
    +0x3661: mov     %al,0x1211(%rcx)
    +0x3667: xor     %ecx,%ecx
    +0x3669: nopl    0x0(%rax)
    +0x3670: movd    0x19a0(%rsp,%rcx,1),%xmm0
    +0x3679: movzwl  0x19a2(%rsp,%rcx,1),%edx
    +0x3681: movd    %edx,%xmm1
    +0x3685: movdqa  %xmm0,%xmm2
    +0x3689: psrlw   $0x4,%xmm2
    +0x368e: movdqa  %xmm1,%xmm3
    +0x3692: psrlw   $0x4,%xmm3
    +0x3697: punpcklbw %xmm2,%xmm0
    +0x369b: pand    %xmm5,%xmm0
    +0x369f: punpcklbw %xmm4,%xmm0
    +0x36a3: punpcklwd %xmm4,%xmm0
    +0x36a7: movdqa  %xmm0,0x340(%rsp,%rcx,8)
    +0x36b0: punpcklbw %xmm3,%xmm1
    +0x36b4: pand    %xmm5,%xmm1
    +0x36b8: punpcklbw %xmm4,%xmm1
    +0x36bc: punpcklwd %xmm4,%xmm1
    +0x36c0: movdqa  %xmm1,0x350(%rsp,%rcx,8)
    +0x36c9: add     $0x4,%rcx
    +0x36cd: cmp     $0x80,%rcx
    +0x36d4: jne     <mldsa87_signature_internal+0x3670>
    +0x36d6: xor     %ecx,%ecx
    +0x36d8: jmp     <mldsa87_signature_internal+0x3701>
    +0x36da: nopw    0x0(%rax,%rax,1)
    +0x36e0: cmp     $0x4b,%eax
    +0x36e3: je      <mldsa87_signature_internal+0x30a8>
    +0x36e9: mov     %eax,%edx
    +0x36eb: mov     0x28(%rsp),%rsi
    +0x36f0: mov     %cl,(%rsi,%rdx,1)
    +0x36f3: inc     %eax
    +0x36f5: inc     %rcx
    +0x36f8: cmp     $0x100,%rcx
    +0x36ff: je      <mldsa87_signature_internal+0x372c>
    +0x3701: mov     0x3620(%rsp,%rcx,4),%edi
    +0x3708: sub     $0xfffc0100,%edi
    +0x370e: setne   %dl
    +0x3711: cmpl    $0x0,0x340(%rsp,%rcx,4)
    +0x3719: sete    %sil
    +0x371d: cmp     $0x7fe00,%edi
    +0x3723: ja      <mldsa87_signature_internal+0x36e0>
    +0x3725: or      %sil,%dl
    +0x3728: jne     <mldsa87_signature_internal+0x36f5>
    +0x372a: jmp     <mldsa87_signature_internal+0x36e0>
    +0x372c: mov     0x20(%rsp),%rcx
    +0x3731: mov     %al,0x1212(%rcx)
    +0x3737: mov     $0x1,%bl
    +0x3739: jmp     <mldsa87_signature_internal+0x30aa>
    +0x373e: mov     $0x1213,%edx
    +0x3743: mov     0x20(%rsp),%rbx
    +0x3748: mov     %rbx,%rdi
    +0x374b: xor     %esi,%esi
    +0x374d: call    <memset>
    +0x3752: movl    $0xfffffffc,0x30(%rsp)
    +0x375a: movq    $0x0,0x40(%rsp)
    +0x3763: lea     0x40(%rsp),%rax
    +0x3768: movq    $0x0,0x60(%rsp)
    +0x3771: lea     0x60(%rsp),%rax
    +0x3776: movq    $0x0,0x80(%rsp)
    +0x3782: lea     0x80(%rsp),%rax
    +0x378a: lea     0xf40(%rsp),%r14
    +0x3792: mov     $0x420,%edx
    +0x3797: mov     %r14,%rdi
    +0x379a: xor     %esi,%esi
    +0x379c: call    <memset>
    +0x37a1: pxor    %xmm0,%xmm0
    +0x37a5: movdqa  %xmm0,0x330(%rsp)
    +0x37ae: movdqa  %xmm0,0x320(%rsp)
    +0x37b7: movdqa  %xmm0,0x310(%rsp)
    +0x37c0: movdqa  %xmm0,0x300(%rsp)
    +0x37c9: movdqa  %xmm0,0x2f0(%rsp)
    +0x37d2: movdqa  %xmm0,0x2e0(%rsp)
    +0x37db: movdqa  %xmm0,0x2d0(%rsp)
    +0x37e4: movdqa  %xmm0,0x2c0(%rsp)
    +0x37ed: movdqa  %xmm0,0x2b0(%rsp)
    +0x37f6: movdqa  %xmm0,0x2a0(%rsp)
    +0x37ff: movdqa  %xmm0,0x290(%rsp)
    +0x3808: movdqa  %xmm0,0x280(%rsp)
    +0x3811: movdqa  %xmm0,0x270(%rsp)
    +0x381a: movdqa  %xmm0,0x260(%rsp)
    +0x3823: movdqa  %xmm0,0x250(%rsp)
    +0x382c: movdqa  %xmm0,0x240(%rsp)
    +0x3835: lea     0x240(%rsp),%rax
    +0x383d: mov     0x30(%rsp),%eax
    +0x3841: lea     -0x28(%rbp),%rsp
    +0x3845: pop     %rbx
    +0x3846: pop     %r12
    +0x3848: pop     %r13
    +0x384a: pop     %r14
    +0x384c: pop     %r15
    +0x384e: pop     %rbp
    +0x384f: xor     %ecx,%ecx
    +0x3851: xor     %edi,%edi
    +0x3853: xor     %edx,%edx
    +0x3855: xor     %esi,%esi
    +0x3857: xor     %r8d,%r8d
    +0x385a: xor     %r9d,%r9d
    +0x385d: xor     %r10d,%r10d
    +0x3860: xor     %r11d,%r11d
    +0x3863: ret     
 ***)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa87_signature_internal";
    layout_range "plt_memcpy";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* secret key skb at sk (4896 bytes), the message M of mlen bytes at m and   *)
(* the prefix PRE of prelen bytes at pre (or, if ext is nonzero as a 32-bit  *)
(* integer, mu in the first 64 bytes at m), and the 32 bytes RND at rnd,     *)
(* with MU the mu that the code uses: the result is 0, with the signature    *)
(* mld_sign_sig_87 at sig (4627 bytes), if one of the 16382 attempts         *)
(* succeeds (mld_sign_ok_87), and -4 with the signature zeroed otherwise.    *)
(* The last two arguments, sk and ext, are on the stack above the return     *)
(* address, sk as a 64-bit word and ext as a 32-bit one. The function aligns *)
(* the stack pointer down to a multiple of 32, which may lower it by up to   *)
(* 31 bytes, saves RBP, the frame pointer, and five more registers, and      *)
(* reserves its buffers, below which the callees use theirs: 16462 bytes of  *)
(* stack below the return address in all (the figure of stackx.py, which     *)
(* counts the red zone that mldsa_keccakf1600_permute writes below RSP). The *)
(* GOT entries of memset and memcpy, which the PLT stubs read, and the       *)
(* region (ea,el) that they may read are apart from the signature and the    *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen pre prelen rnd sk (ext:int32) skb M PRE RND MU
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(ext = (word 0:int32)) ==> 64 <= mlen) /\
          MU = (if ext = (word 0:int32)
                then mld_sign_mu (\j. skb(64 + j)) prelen PRE mlen M
                else M MOD 2 EXP 512) /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          mld_sign_terminates_87 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 16462),16462)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 16462),16462)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa87_signature_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; rnd] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8)))
                         s = sk /\
                    read (memory :> bytes32(word_add stackpointer (word 16)))
                         s = ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mld_sign_ok_87 skb MU RND
                     then word 0 else word 4294967292) /\
                    (!t. t < 4627
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             mld_sign_sig_87 skb MU RND t))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 16462),16462)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, ext, rho, what the C *)
(* code declassifies in each attempt (mld_sign_declass), the addresses of    *)
(* memset and memcpy and the stack, with all accesses within the arguments,  *)
(* the stack, the return address and the arguments above it, the GOT entries *)
(* of memset and memcpy, the region (ea,el) that they may read and the       *)
(* constants of the callees, and the writes within the signature and the     *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen rnd sk (ext:int32) skb M PRE RND MU
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(ext = (word 0:int32)) ==> 64 <= mlen) /\
          MU = (if ext = (word 0:int32)
                then mld_sign_mu (\j. skb(64 + j)) prelen PRE mlen M
                else M MOD 2 EXP 512) /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          mld_sign_terminates_87 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 16462),16462)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 16462),16462)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa87_signature_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; rnd] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8)))
                         s = sk /\
                    read (memory :> bytes32(word_add stackpointer (word 16)))
                         s = ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mld_sign_ok_87 skb MU RND
                     then word 0 else word 4294967292) /\
                    (!t. t < 4627
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             mld_sign_sig_87 skb MU RND t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen rnd sk ext
                             (mld_sk_rho skb)
                             (mld_sign_declass_87 skb MU RND)
                             mf mc pc (word_sub stackpointer (word 16462))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; rnd,32; sk,4896;
                         word_sub stackpointer (word 16462),16462;
                         stackpointer,8; word_add stackpointer (word 8),16;
                         word(pc + got_memset),8;
                          word(pc + got_memcpy),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa87_signature_internal_consts),784;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448]
                        [sig,4627;
                         word_sub stackpointer (word 16462),16462]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 16462),16462)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen rnd sk (ext:int32) skb M PRE RND MU
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(ext = (word 0:int32)) ==> 64 <= mlen) /\
          MU = (if ext = (word 0:int32)
                then mld_sign_mu (\j. skb(64 + j)) prelen PRE mlen M
                else M MOD 2 EXP 512) /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          mld_sign_terminates_87 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 16462),16462)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 16462),16462)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa87_signature_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; rnd] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8)))
                         s = sk /\
                    read (memory :> bytes32(word_add stackpointer (word 16)))
                         s = ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen rnd sk ext
                             (mld_sk_rho skb)
                             (mld_sign_declass_87 skb MU RND)
                             mf mc pc (word_sub stackpointer (word 16462))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; rnd,32; sk,4896;
                         word_sub stackpointer (word 16462),16462;
                         stackpointer,8; word_add stackpointer (word 8),16;
                         word(pc + got_memset),8;
                          word(pc + got_memcpy),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa87_signature_internal_consts),784;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448]
                        [sig,4627;
                         word_sub stackpointer (word 16462),16462]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 16462),16462)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
