(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing: the statement. This is the code for mldsa65_signature_internal   *)
(* (mld_sign_signature_internal in sign.c, with                              *)
(* mld_attempt_signature_generation and mld_compute_pack_z inlined) from     *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3    *)
(* and MLD_CONFIG_REDUCE_RAM as one translation unit (see                    *)
(* mldsa_native/README.md), which aligns its stack frame to 32 bytes,        *)
(* unpacks the secret key, computes mu (or takes it from m if ext is         *)
(* nonzero) and rho'', and makes up to 13106 attempts: each samples y,       *)
(* computes w = A y and its packed w1, c~ and the challenge, then z,         *)
(* checking and packing each polynomial, and for each row checks w0 - c s2   *)
(* and c t0, and finally packs c~ and the hints, rejecting at the first      *)
(* check that fails. It returns 0 with the signature of the first attempt    *)
(* that succeeds, or -4 (MLD_ERR_SIGN_ATTEMPTS_EXHAUSTED) with the signature *)
(* zeroed, and zeroes its buffers. Clang has inlined most of its callees; it *)
(* still calls mld_H65, mldsa65_poly_challenge, mldsa_poly_uniform,          *)
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
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/H_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_challenge_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa65_signature_internal:
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
      +0x3e: sub     $0x140,%rsp
      +0x45: mov     %r9,%rbx
      +0x48: mov     %r8,%r9
      +0x4b: mov     %rcx,%r8
      +0x4e: mov     %rdx,%r10
      +0x51: mov     %rsi,%rax
      +0x54: mov     %rdi,0x8(%rsp)
      +0x59: mov     0x10(%rbp),%rcx
      +0x5d: lea     0x680(%rsp),%r15
      +0x65: lea     0x6a0(%rsp),%r11
      +0x6d: movups  (%rcx),%xmm0
      +0x70: movups  0x10(%rcx),%xmm1
      +0x74: movaps  %xmm1,0x630(%rsp)
      +0x7c: movaps  %xmm0,0x620(%rsp)
      +0x84: movups  0x20(%rcx),%xmm0
      +0x88: movups  0x30(%rcx),%xmm1
      +0x8c: movaps  %xmm0,0x680(%rsp)
      +0x94: movaps  %xmm1,0x690(%rsp)
      +0x9c: movups  0x40(%rcx),%xmm0
      +0xa0: movups  0x50(%rcx),%xmm1
      +0xa4: movdqu  0x60(%rcx),%xmm2
      +0xa9: movdqu  0x70(%rcx),%xmm3
      +0xae: movdqa  %xmm2,0x660(%rsp)
      +0xb7: movaps  %xmm1,0x650(%rsp)
      +0xbf: movaps  %xmm0,0x640(%rsp)
      +0xc7: movdqa  %xmm3,0x670(%rsp)
      +0xd0: lea     0x80(%rcx),%rdx
      +0xd7: mov     %rdx,0x60(%rsp)
      +0xdc: lea     0x300(%rcx),%rdx
      +0xe3: mov     %rdx,0x20(%rsp)
      +0xe8: add     $0x600,%rcx
      +0xef: mov     %rcx,0x40(%rsp)
      +0xf4: cmpl    $0x0,0x18(%rbp)
      +0xf8: je      <mldsa65_signature_internal+0x122>
      +0xfa: movups  (%rax),%xmm0
      +0xfd: movups  0x10(%rax),%xmm1
     +0x101: movdqu  0x20(%rax),%xmm2
     +0x106: movdqu  0x30(%rax),%xmm3
     +0x10b: movdqa  %xmm3,0x30(%r11)
     +0x111: movdqa  %xmm2,0x20(%r11)
     +0x117: movaps  %xmm1,0x10(%r11)
     +0x11c: movaps  %xmm0,(%r11)
     +0x120: jmp     <mldsa65_signature_internal+0x14b>
     +0x122: lea     0x640(%rsp),%rdx
     +0x12a: mov     $0x40,%esi
     +0x12f: mov     $0x40,%ecx
     +0x134: mov     %r11,%rdi
     +0x137: push    %r10
     +0x139: push    %rax
     +0x13a: call    <mld_H65>
     +0x13f: lea     0x6b0(%rsp),%r11
     +0x147: add     $0x10,%rsp
     +0x14b: mov     $0x40,%esi
     +0x150: mov     $0x20,%ecx
     +0x155: mov     $0x20,%r9d
     +0x15b: lea     0x6e0(%rsp),%rdi
     +0x163: mov     %r15,%rdx
     +0x166: mov     %rbx,%r8
     +0x169: push    $0x40
     +0x16b: push    %r11
     +0x16d: call    <mld_H65>
     +0x172: add     $0x10,%rsp
     +0x176: movdqa  0x620(%rsp),%xmm0
     +0x17f: movdqa  0x630(%rsp),%xmm1
     +0x188: movdqa  %xmm1,0x1230(%rsp)
     +0x191: movdqa  %xmm0,0x1220(%rsp)
     +0x19a: mov     0x8(%rsp),%rax
     +0x19f: lea     0xcb0(%rax),%rcx
     +0x1a6: mov     %rcx,0x10(%rsp)
     +0x1ab: add     $0x33,%rax
     +0x1af: mov     %rax,0xa8(%rsp)
     +0x1b7: xor     %ecx,%ecx
     +0x1b9: pxor    %xmm4,%xmm4
     +0x1bd: nopl    (%rax)
     +0x1c0: mov     %rcx,0xb0(%rsp)
     +0x1c8: lea     (%rcx,%rcx,4),%eax
     +0x1cb: lea     0x6e0(%rsp),%rcx
     +0x1d3: mov     %rcx,0x80(%rsp)
     +0x1db: mov     %ax,0x88(%rsp)
     +0x1e3: lea     0x1220(%rsp),%rax
     +0x1eb: movaps  (%rax),%xmm0
     +0x1ee: movaps  0x10(%rax),%xmm1
     +0x1f2: movaps  %xmm1,0x1250(%rsp)
     +0x1fa: movaps  %xmm0,0x1240(%rsp)
     +0x202: xor     %r12d,%r12d
     +0x205: jmp     <mldsa65_signature_internal+0x21d>
     +0x207: nopw    0x0(%rax,%rax,1)
     +0x210: inc     %r12d
     +0x213: cmp     $0x5,%r12d
     +0x217: je      <mldsa65_signature_internal+0xfd0>
     +0x21d: mov     0x80(%rsp),%rax
     +0x225: movzwl  0x88(%rsp),%ecx
     +0x22d: mov     %r12d,0x18(%rsp)
     +0x232: add     %r12w,%cx
     +0x236: movups  (%rax),%xmm0
     +0x239: movups  0x10(%rax),%xmm1
     +0x23d: movups  0x20(%rax),%xmm2
     +0x241: movups  0x30(%rax),%xmm3
     +0x245: movaps  %xmm0,0xb20(%rsp)
     +0x24d: movaps  %xmm1,0xb30(%rsp)
     +0x255: movaps  %xmm2,0xb40(%rsp)
     +0x25d: movaps  %xmm3,0xb50(%rsp)
     +0x265: mov     %cx,0xb60(%rsp)
     +0x26d: movdqa  %xmm4,0x720(%rsp)
     +0x276: movdqa  %xmm4,0x730(%rsp)
     +0x27f: movdqa  %xmm4,0x740(%rsp)
     +0x288: movdqa  %xmm4,0x750(%rsp)
     +0x291: movdqa  %xmm4,0x760(%rsp)
     +0x29a: movdqa  %xmm4,0x770(%rsp)
     +0x2a3: movdqa  %xmm4,0x780(%rsp)
     +0x2ac: movdqa  %xmm4,0x790(%rsp)
     +0x2b5: movdqa  %xmm4,0x7a0(%rsp)
     +0x2be: movdqa  %xmm4,0x7b0(%rsp)
     +0x2c7: movdqa  %xmm4,0x7c0(%rsp)
     +0x2d0: movdqa  %xmm4,0x7d0(%rsp)
     +0x2d9: movdqu  %xmm4,0x7dc(%rsp)
     +0x2e2: movdqa  0xb20(%rsp),%xmm0
     +0x2eb: movdqa  0x730(%rsp),%xmm1
     +0x2f4: movdqa  0x740(%rsp),%xmm2
     +0x2fd: movdqa  0x750(%rsp),%xmm3
     +0x306: pxor    0xb30(%rsp),%xmm1
     +0x30f: movdqa  0x760(%rsp),%xmm4
     +0x318: movdqa  %xmm0,0x720(%rsp)
     +0x321: pxor    0xb40(%rsp),%xmm2
     +0x32a: movdqa  %xmm1,0x730(%rsp)
     +0x333: pxor    0xb50(%rsp),%xmm3
     +0x33c: movdqa  %xmm2,0x740(%rsp)
     +0x345: movdqa  %xmm3,0x750(%rsp)
     +0x34e: pxor    0xb60(%rsp),%xmm4
     +0x357: movd    %xmm4,%eax
     +0x35b: mov     %ax,0x760(%rsp)
     +0x363: xorb    $0x1f,0x762(%rsp)
     +0x36b: xorb    $0x80,0x7a7(%rsp)
     +0x373: movl    $0x88,0x7e8(%rsp)
     +0x37e: mov     $0x88,%ebx
     +0x383: mov     $0x2a8,%r15d
     +0x389: xor     %r12d,%r12d
     +0x38c: jmp     <mldsa65_signature_internal+0x3cb>
     +0x38e: xchg    %ax,%ax
     +0x390: mov     $0x88,%r13d
     +0x396: sub     %ebx,%r13d
     +0x399: cmp     %r13,%r15
     +0x39c: cmovb   %r15,%r13
     +0x3a0: mov     %ebx,%eax
     +0x3a2: lea     (%rsp,%rax,1),%rsi
     +0x3a6: add     $0x720,%rsi
     +0x3ad: lea     (%rsp,%r12,1),%rdi
     +0x3b1: add     $0x2d00,%rdi
     +0x3b8: mov     %r13,%rdx
     +0x3bb: call    <memcpy>
     +0x3c0: add     %r13d,%ebx
     +0x3c3: add     %r13,%r12
     +0x3c6: sub     %r13,%r15
     +0x3c9: je      <mldsa65_signature_internal+0x400>
     +0x3cb: cmp     $0x88,%ebx
     +0x3d1: jne     <mldsa65_signature_internal+0x390>
     +0x3d3: lea     0x720(%rsp),%r14
     +0x3db: mov     %r14,%rdi
     +0x3de: call    <mldsa_keccakf1600_permute>
     +0x3e3: cmp     $0x88,%r15
     +0x3ea: mov     $0x88,%r13d
     +0x3f0: cmovb   %r15,%r13
     +0x3f4: xor     %ebx,%ebx
     +0x3f6: mov     %r14,%rsi
     +0x3f9: jmp     <mldsa65_signature_internal+0x3ad>
     +0x3fb: nopl    0x0(%rax,%rax,1)
     +0x400: lea     0x2d04(%rsp),%rax
     +0x408: xor     %ecx,%ecx
     +0x40a: nopw    0x0(%rax,%rax,1)
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
     +0x436: mov     %r9d,0x220(%rsp,%rcx,8)
     +0x43e: shl     $0xc,%r8d
     +0x442: shl     $0x4,%edx
     +0x445: or      %esi,%edx
     +0x447: or      %r8d,%edx
     +0x44a: mov     $0x80000,%esi
     +0x44f: sub     %edx,%esi
     +0x451: mov     %esi,0x224(%rsp,%rcx,8)
     +0x458: inc     %rcx
     +0x45b: add     $0x5,%rax
     +0x45f: cmp     $0x80,%rcx
     +0x466: jne     <mldsa65_signature_internal+0x410>
     +0x468: pxor    %xmm0,%xmm0
     +0x46c: movdqa  %xmm0,0x7e0(%rsp)
     +0x475: movdqa  %xmm0,0x7d0(%rsp)
     +0x47e: movdqa  %xmm0,0x7c0(%rsp)
     +0x487: movdqa  %xmm0,0x7b0(%rsp)
     +0x490: movdqa  %xmm0,0x7a0(%rsp)
     +0x499: movdqa  %xmm0,0x790(%rsp)
     +0x4a2: movdqa  %xmm0,0x780(%rsp)
     +0x4ab: movdqa  %xmm0,0x770(%rsp)
     +0x4b4: movdqa  %xmm0,0x760(%rsp)
     +0x4bd: movdqa  %xmm0,0x750(%rsp)
     +0x4c6: movdqa  %xmm0,0x740(%rsp)
     +0x4cf: movdqa  %xmm0,0x730(%rsp)
     +0x4d8: movdqa  %xmm0,0x720(%rsp)
     +0x4e1: lea     0x720(%rsp),%rax
     +0x4e9: mov     $0x2a8,%edx
     +0x4ee: lea     0x2d00(%rsp),%rbx
     +0x4f6: mov     %rbx,%rdi
     +0x4f9: xor     %esi,%esi
     +0x4fb: call    <memset>
     +0x500: pxor    %xmm0,%xmm0
     +0x504: movdqa  %xmm0,0xb50(%rsp)
     +0x50d: movdqa  %xmm0,0xb40(%rsp)
     +0x516: movdqa  %xmm0,0xb30(%rsp)
     +0x51f: movdqa  %xmm0,0xb20(%rsp)
     +0x528: movw    $0x0,0xb60(%rsp)
     +0x532: lea     0xb20(%rsp),%rax
     +0x53a: lea     0x220(%rsp),%rdi
     +0x542: call    <mldsa_poly_ntt>
     +0x547: mov     0x18(%rsp),%r12d
     +0x54c: test    %r12d,%r12d
     +0x54f: movabs  $0x380200100000000,%rbx
     +0x559: lea     0x1240(%rsp),%r14
     +0x561: lea     0xe20(%rsp),%r15
     +0x569: je      <mldsa65_signature_internal+0xc40>
     +0x56f: mov     %r12b,0x1260(%rsp)
     +0x577: movb    $0x0,0x1261(%rsp)
     +0x57f: mov     %r15,%rdi
     +0x582: mov     %r14,%rsi
     +0x585: call    <mldsa_poly_uniform>
     +0x58a: mov     $0x1,%eax
     +0x58f: nop     
     +0x590: movslq  0xe1c(%rsp,%rax,4),%rcx
     +0x598: movslq  0x21c(%rsp,%rax,4),%rdx
     +0x5a0: imul    %rcx,%rdx
     +0x5a4: mov     %rdx,%rcx
     +0x5a7: imul    %rbx,%rcx
     +0x5ab: sar     $0x20,%rcx
     +0x5af: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x5b6: add     %rdx,%rcx
     +0x5b9: shr     $0x20,%rcx
     +0x5bd: mov     %ecx,0xe1c(%rsp,%rax,4)
     +0x5c4: movslq  0xe20(%rsp,%rax,4),%rcx
     +0x5cc: movslq  0x220(%rsp,%rax,4),%rdx
     +0x5d4: imul    %rcx,%rdx
     +0x5d8: mov     %rdx,%rcx
     +0x5db: imul    %rbx,%rcx
     +0x5df: sar     $0x20,%rcx
     +0x5e3: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x5ea: add     %rdx,%rcx
     +0x5ed: shr     $0x20,%rcx
     +0x5f1: mov     %ecx,0xe20(%rsp,%rax,4)
     +0x5f8: add     $0x2,%rax
     +0x5fc: cmp     $0x101,%rax
     +0x602: jne     <mldsa65_signature_internal+0x590>
     +0x604: mov     $0xc,%eax
     +0x609: nopl    0x0(%rax)
     +0x610: movdqa  0xdf0(%rsp,%rax,4),%xmm0
     +0x619: movdqa  0xe00(%rsp,%rax,4),%xmm1
     +0x622: movdqa  0xe10(%rsp,%rax,4),%xmm2
     +0x62b: movdqa  0xe20(%rsp,%rax,4),%xmm3
     +0x634: paddd   0x14d0(%rsp,%rax,4),%xmm0
     +0x63d: paddd   0x14e0(%rsp,%rax,4),%xmm1
     +0x646: movdqa  %xmm0,0x14d0(%rsp,%rax,4)
     +0x64f: movdqa  %xmm1,0x14e0(%rsp,%rax,4)
     +0x658: paddd   0x14f0(%rsp,%rax,4),%xmm2
     +0x661: paddd   0x1500(%rsp,%rax,4),%xmm3
     +0x66a: movdqa  %xmm2,0x14f0(%rsp,%rax,4)
     +0x673: movdqa  %xmm3,0x1500(%rsp,%rax,4)
     +0x67c: add     $0x10,%rax
     +0x680: cmp     $0x10c,%rax
     +0x686: jne     <mldsa65_signature_internal+0x610>
     +0x688: mov     %r12b,0x1260(%rsp)
     +0x690: movb    $0x1,0x1261(%rsp)
     +0x698: mov     %r15,%rdi
     +0x69b: mov     %r14,%rsi
     +0x69e: call    <mldsa_poly_uniform>
     +0x6a3: mov     $0x1,%eax
     +0x6a8: nopl    0x0(%rax,%rax,1)
     +0x6b0: movslq  0xe1c(%rsp,%rax,4),%rcx
     +0x6b8: movslq  0x21c(%rsp,%rax,4),%rdx
     +0x6c0: imul    %rcx,%rdx
     +0x6c4: mov     %rdx,%rcx
     +0x6c7: imul    %rbx,%rcx
     +0x6cb: sar     $0x20,%rcx
     +0x6cf: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x6d6: add     %rdx,%rcx
     +0x6d9: shr     $0x20,%rcx
     +0x6dd: mov     %ecx,0xe1c(%rsp,%rax,4)
     +0x6e4: movslq  0xe20(%rsp,%rax,4),%rcx
     +0x6ec: movslq  0x220(%rsp,%rax,4),%rdx
     +0x6f4: imul    %rcx,%rdx
     +0x6f8: mov     %rdx,%rcx
     +0x6fb: imul    %rbx,%rcx
     +0x6ff: sar     $0x20,%rcx
     +0x703: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x70a: add     %rdx,%rcx
     +0x70d: shr     $0x20,%rcx
     +0x711: mov     %ecx,0xe20(%rsp,%rax,4)
     +0x718: add     $0x2,%rax
     +0x71c: cmp     $0x101,%rax
     +0x722: jne     <mldsa65_signature_internal+0x6b0>
     +0x724: mov     $0xc,%eax
     +0x729: nopl    0x0(%rax)
     +0x730: movdqa  0xdf0(%rsp,%rax,4),%xmm0
     +0x739: movdqa  0xe00(%rsp,%rax,4),%xmm1
     +0x742: movdqa  0xe10(%rsp,%rax,4),%xmm2
     +0x74b: movdqa  0xe20(%rsp,%rax,4),%xmm3
     +0x754: paddd   0x18d0(%rsp,%rax,4),%xmm0
     +0x75d: paddd   0x18e0(%rsp,%rax,4),%xmm1
     +0x766: movdqa  %xmm0,0x18d0(%rsp,%rax,4)
     +0x76f: movdqa  %xmm1,0x18e0(%rsp,%rax,4)
     +0x778: paddd   0x18f0(%rsp,%rax,4),%xmm2
     +0x781: paddd   0x1900(%rsp,%rax,4),%xmm3
     +0x78a: movdqa  %xmm2,0x18f0(%rsp,%rax,4)
     +0x793: movdqa  %xmm3,0x1900(%rsp,%rax,4)
     +0x79c: add     $0x10,%rax
     +0x7a0: cmp     $0x10c,%rax
     +0x7a6: jne     <mldsa65_signature_internal+0x730>
     +0x7a8: mov     %r12b,0x1260(%rsp)
     +0x7b0: movb    $0x2,0x1261(%rsp)
     +0x7b8: mov     %r15,%rdi
     +0x7bb: mov     %r14,%rsi
     +0x7be: call    <mldsa_poly_uniform>
     +0x7c3: mov     $0x1,%eax
     +0x7c8: nopl    0x0(%rax,%rax,1)
     +0x7d0: movslq  0xe1c(%rsp,%rax,4),%rcx
     +0x7d8: movslq  0x21c(%rsp,%rax,4),%rdx
     +0x7e0: imul    %rcx,%rdx
     +0x7e4: mov     %rdx,%rcx
     +0x7e7: imul    %rbx,%rcx
     +0x7eb: sar     $0x20,%rcx
     +0x7ef: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x7f6: add     %rdx,%rcx
     +0x7f9: shr     $0x20,%rcx
     +0x7fd: mov     %ecx,0xe1c(%rsp,%rax,4)
     +0x804: movslq  0xe20(%rsp,%rax,4),%rcx
     +0x80c: movslq  0x220(%rsp,%rax,4),%rdx
     +0x814: imul    %rcx,%rdx
     +0x818: mov     %rdx,%rcx
     +0x81b: imul    %rbx,%rcx
     +0x81f: sar     $0x20,%rcx
     +0x823: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x82a: add     %rdx,%rcx
     +0x82d: shr     $0x20,%rcx
     +0x831: mov     %ecx,0xe20(%rsp,%rax,4)
     +0x838: add     $0x2,%rax
     +0x83c: cmp     $0x101,%rax
     +0x842: jne     <mldsa65_signature_internal+0x7d0>
     +0x844: xor     %eax,%eax
     +0x846: cs      nopw 0x0(%rax,%rax,1)
     +0x850: movdqa  0xe20(%rsp,%rax,4),%xmm0
     +0x859: movdqa  0xe30(%rsp,%rax,4),%xmm1
     +0x862: movdqa  0xe40(%rsp,%rax,4),%xmm2
     +0x86b: movdqa  0xe50(%rsp,%rax,4),%xmm3
     +0x874: paddd   0x1d00(%rsp,%rax,4),%xmm0
     +0x87d: paddd   0x1d10(%rsp,%rax,4),%xmm1
     +0x886: movdqa  %xmm0,0x1d00(%rsp,%rax,4)
     +0x88f: movdqa  %xmm1,0x1d10(%rsp,%rax,4)
     +0x898: paddd   0x1d20(%rsp,%rax,4),%xmm2
     +0x8a1: paddd   0x1d30(%rsp,%rax,4),%xmm3
     +0x8aa: movdqa  %xmm2,0x1d20(%rsp,%rax,4)
     +0x8b3: movdqa  %xmm3,0x1d30(%rsp,%rax,4)
     +0x8bc: add     $0x10,%rax
     +0x8c0: cmp     $0x100,%rax
     +0x8c6: jne     <mldsa65_signature_internal+0x850>
     +0x8c8: mov     %r12b,0x1260(%rsp)
     +0x8d0: movb    $0x3,0x1261(%rsp)
     +0x8d8: mov     %r15,%rdi
     +0x8db: mov     %r14,%rsi
     +0x8de: call    <mldsa_poly_uniform>
     +0x8e3: mov     $0x1,%eax
     +0x8e8: nopl    0x0(%rax,%rax,1)
     +0x8f0: movslq  0xe1c(%rsp,%rax,4),%rcx
     +0x8f8: movslq  0x21c(%rsp,%rax,4),%rdx
     +0x900: imul    %rcx,%rdx
     +0x904: mov     %rdx,%rcx
     +0x907: imul    %rbx,%rcx
     +0x90b: sar     $0x20,%rcx
     +0x90f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x916: add     %rdx,%rcx
     +0x919: shr     $0x20,%rcx
     +0x91d: mov     %ecx,0xe1c(%rsp,%rax,4)
     +0x924: movslq  0xe20(%rsp,%rax,4),%rcx
     +0x92c: movslq  0x220(%rsp,%rax,4),%rdx
     +0x934: imul    %rcx,%rdx
     +0x938: mov     %rdx,%rcx
     +0x93b: imul    %rbx,%rcx
     +0x93f: sar     $0x20,%rcx
     +0x943: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x94a: add     %rdx,%rcx
     +0x94d: shr     $0x20,%rcx
     +0x951: mov     %ecx,0xe20(%rsp,%rax,4)
     +0x958: add     $0x2,%rax
     +0x95c: cmp     $0x101,%rax
     +0x962: jne     <mldsa65_signature_internal+0x8f0>
     +0x964: xor     %eax,%eax
     +0x966: cs      nopw 0x0(%rax,%rax,1)
     +0x970: movdqa  0xe20(%rsp,%rax,4),%xmm0
     +0x979: movdqa  0xe30(%rsp,%rax,4),%xmm1
     +0x982: movdqa  0xe40(%rsp,%rax,4),%xmm2
     +0x98b: movdqa  0xe50(%rsp,%rax,4),%xmm3
     +0x994: paddd   0x2100(%rsp,%rax,4),%xmm0
     +0x99d: paddd   0x2110(%rsp,%rax,4),%xmm1
     +0x9a6: movdqa  %xmm0,0x2100(%rsp,%rax,4)
     +0x9af: movdqa  %xmm1,0x2110(%rsp,%rax,4)
     +0x9b8: paddd   0x2120(%rsp,%rax,4),%xmm2
     +0x9c1: paddd   0x2130(%rsp,%rax,4),%xmm3
     +0x9ca: movdqa  %xmm2,0x2120(%rsp,%rax,4)
     +0x9d3: movdqa  %xmm3,0x2130(%rsp,%rax,4)
     +0x9dc: add     $0x10,%rax
     +0x9e0: cmp     $0x100,%rax
     +0x9e6: jne     <mldsa65_signature_internal+0x970>
     +0x9e8: mov     %r12b,0x1260(%rsp)
     +0x9f0: movb    $0x4,0x1261(%rsp)
     +0x9f8: mov     %r15,%rdi
     +0x9fb: mov     %r14,%rsi
     +0x9fe: call    <mldsa_poly_uniform>
     +0xa03: mov     $0x1,%eax
     +0xa08: nopl    0x0(%rax,%rax,1)
     +0xa10: movslq  0xe1c(%rsp,%rax,4),%rcx
     +0xa18: movslq  0x21c(%rsp,%rax,4),%rdx
     +0xa20: imul    %rcx,%rdx
     +0xa24: mov     %rdx,%rcx
     +0xa27: imul    %rbx,%rcx
     +0xa2b: sar     $0x20,%rcx
     +0xa2f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xa36: add     %rdx,%rcx
     +0xa39: shr     $0x20,%rcx
     +0xa3d: mov     %ecx,0xe1c(%rsp,%rax,4)
     +0xa44: movslq  0xe20(%rsp,%rax,4),%rcx
     +0xa4c: movslq  0x220(%rsp,%rax,4),%rdx
     +0xa54: imul    %rcx,%rdx
     +0xa58: mov     %rdx,%rcx
     +0xa5b: imul    %rbx,%rcx
     +0xa5f: sar     $0x20,%rcx
     +0xa63: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xa6a: add     %rdx,%rcx
     +0xa6d: shr     $0x20,%rcx
     +0xa71: mov     %ecx,0xe20(%rsp,%rax,4)
     +0xa78: add     $0x2,%rax
     +0xa7c: cmp     $0x101,%rax
     +0xa82: jne     <mldsa65_signature_internal+0xa10>
     +0xa84: xor     %eax,%eax
     +0xa86: cs      nopw 0x0(%rax,%rax,1)
     +0xa90: movdqa  0xe20(%rsp,%rax,4),%xmm0
     +0xa99: movdqa  0xe30(%rsp,%rax,4),%xmm1
     +0xaa2: movdqa  0xe40(%rsp,%rax,4),%xmm2
     +0xaab: movdqa  0xe50(%rsp,%rax,4),%xmm3
     +0xab4: paddd   0x2500(%rsp,%rax,4),%xmm0
     +0xabd: paddd   0x2510(%rsp,%rax,4),%xmm1
     +0xac6: movdqa  %xmm0,0x2500(%rsp,%rax,4)
     +0xacf: movdqa  %xmm1,0x2510(%rsp,%rax,4)
     +0xad8: paddd   0x2520(%rsp,%rax,4),%xmm2
     +0xae1: paddd   0x2530(%rsp,%rax,4),%xmm3
     +0xaea: movdqa  %xmm2,0x2520(%rsp,%rax,4)
     +0xaf3: movdqa  %xmm3,0x2530(%rsp,%rax,4)
     +0xafc: add     $0x10,%rax
     +0xb00: cmp     $0x100,%rax
     +0xb06: jne     <mldsa65_signature_internal+0xa90>
     +0xb08: mov     %r12b,0x1260(%rsp)
     +0xb10: movb    $0x5,0x1261(%rsp)
     +0xb18: mov     %r15,%rdi
     +0xb1b: mov     %r14,%rsi
     +0xb1e: call    <mldsa_poly_uniform>
     +0xb23: xor     %eax,%eax
     +0xb25: data16  cs nopw 0x0(%rax,%rax,1)
     +0xb30: movslq  0xe20(%rsp,%rax,4),%rcx
     +0xb38: movslq  0x220(%rsp,%rax,4),%rdx
     +0xb40: imul    %rcx,%rdx
     +0xb44: mov     %rdx,%rcx
     +0xb47: imul    %rbx,%rcx
     +0xb4b: sar     $0x20,%rcx
     +0xb4f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xb56: add     %rdx,%rcx
     +0xb59: shr     $0x20,%rcx
     +0xb5d: mov     %ecx,0xe20(%rsp,%rax,4)
     +0xb64: movslq  0xe24(%rsp,%rax,4),%rcx
     +0xb6c: movslq  0x224(%rsp,%rax,4),%rdx
     +0xb74: imul    %rcx,%rdx
     +0xb78: mov     %rdx,%rcx
     +0xb7b: imul    %rbx,%rcx
     +0xb7f: sar     $0x20,%rcx
     +0xb83: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xb8a: add     %rdx,%rcx
     +0xb8d: shr     $0x20,%rcx
     +0xb91: mov     %ecx,0xe24(%rsp,%rax,4)
     +0xb98: add     $0x2,%rax
     +0xb9c: cmp     $0x100,%rax
     +0xba2: jne     <mldsa65_signature_internal+0xb30>
     +0xba4: xor     %eax,%eax
     +0xba6: pxor    %xmm4,%xmm4
     +0xbaa: movdqa  0x166ee(%rip),%xmm5
     +0xbb2: movdqa  0x166f6(%rip),%xmm6
     +0xbba: nopw    0x0(%rax,%rax,1)
     +0xbc0: movdqa  0xe20(%rsp,%rax,4),%xmm0
     +0xbc9: movdqa  0xe30(%rsp,%rax,4),%xmm1
     +0xbd2: movdqa  0xe40(%rsp,%rax,4),%xmm2
     +0xbdb: movdqa  0xe50(%rsp,%rax,4),%xmm3
     +0xbe4: paddd   0x2900(%rsp,%rax,4),%xmm0
     +0xbed: paddd   0x2910(%rsp,%rax,4),%xmm1
     +0xbf6: movdqa  %xmm0,0x2900(%rsp,%rax,4)
     +0xbff: movdqa  %xmm1,0x2910(%rsp,%rax,4)
     +0xc08: paddd   0x2920(%rsp,%rax,4),%xmm2
     +0xc11: paddd   0x2930(%rsp,%rax,4),%xmm3
     +0xc1a: movdqa  %xmm2,0x2920(%rsp,%rax,4)
     +0xc23: movdqa  %xmm3,0x2930(%rsp,%rax,4)
     +0xc2c: add     $0x10,%rax
     +0xc30: cmp     $0x100,%rax
     +0xc36: jne     <mldsa65_signature_internal+0xbc0>
     +0xc38: jmp     <mldsa65_signature_internal+0x210>
     +0xc3d: nopl    (%rax)
     +0xc40: movw    $0x0,0x1260(%rsp)
     +0xc4a: lea     0x1500(%rsp),%rdi
     +0xc52: mov     %r14,%rsi
     +0xc55: call    <mldsa_poly_uniform>
     +0xc5a: xor     %eax,%eax
     +0xc5c: nopl    0x0(%rax)
     +0xc60: movslq  0x1500(%rsp,%rax,4),%rcx
     +0xc68: movslq  0x220(%rsp,%rax,4),%rdx
     +0xc70: imul    %rcx,%rdx
     +0xc74: mov     %rdx,%rcx
     +0xc77: imul    %rbx,%rcx
     +0xc7b: sar     $0x20,%rcx
     +0xc7f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xc86: add     %rdx,%rcx
     +0xc89: shr     $0x20,%rcx
     +0xc8d: mov     %ecx,0x1500(%rsp,%rax,4)
     +0xc94: movslq  0x1504(%rsp,%rax,4),%rcx
     +0xc9c: movslq  0x224(%rsp,%rax,4),%rdx
     +0xca4: imul    %rcx,%rdx
     +0xca8: mov     %rdx,%rcx
     +0xcab: imul    %rbx,%rcx
     +0xcaf: sar     $0x20,%rcx
     +0xcb3: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xcba: add     %rdx,%rcx
     +0xcbd: shr     $0x20,%rcx
     +0xcc1: mov     %ecx,0x1504(%rsp,%rax,4)
     +0xcc8: add     $0x2,%rax
     +0xccc: cmp     $0x100,%rax
     +0xcd2: jne     <mldsa65_signature_internal+0xc60>
     +0xcd4: movw    $0x100,0x1260(%rsp)
     +0xcde: lea     0x1900(%rsp),%rdi
     +0xce6: mov     %r14,%rsi
     +0xce9: call    <mldsa_poly_uniform>
     +0xcee: xor     %eax,%eax
     +0xcf0: movslq  0x1900(%rsp,%rax,4),%rcx
     +0xcf8: movslq  0x220(%rsp,%rax,4),%rdx
     +0xd00: imul    %rcx,%rdx
     +0xd04: mov     %rdx,%rcx
     +0xd07: imul    %rbx,%rcx
     +0xd0b: sar     $0x20,%rcx
     +0xd0f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xd16: add     %rdx,%rcx
     +0xd19: shr     $0x20,%rcx
     +0xd1d: mov     %ecx,0x1900(%rsp,%rax,4)
     +0xd24: movslq  0x1904(%rsp,%rax,4),%rcx
     +0xd2c: movslq  0x224(%rsp,%rax,4),%rdx
     +0xd34: imul    %rcx,%rdx
     +0xd38: mov     %rdx,%rcx
     +0xd3b: imul    %rbx,%rcx
     +0xd3f: sar     $0x20,%rcx
     +0xd43: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xd4a: add     %rdx,%rcx
     +0xd4d: shr     $0x20,%rcx
     +0xd51: mov     %ecx,0x1904(%rsp,%rax,4)
     +0xd58: add     $0x2,%rax
     +0xd5c: cmp     $0x100,%rax
     +0xd62: jne     <mldsa65_signature_internal+0xcf0>
     +0xd64: movw    $0x200,0x1260(%rsp)
     +0xd6e: lea     0x1d00(%rsp),%rdi
     +0xd76: mov     %r14,%rsi
     +0xd79: call    <mldsa_poly_uniform>
     +0xd7e: xor     %eax,%eax
     +0xd80: movslq  0x1d00(%rsp,%rax,4),%rcx
     +0xd88: movslq  0x220(%rsp,%rax,4),%rdx
     +0xd90: imul    %rcx,%rdx
     +0xd94: mov     %rdx,%rcx
     +0xd97: imul    %rbx,%rcx
     +0xd9b: sar     $0x20,%rcx
     +0xd9f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xda6: add     %rdx,%rcx
     +0xda9: shr     $0x20,%rcx
     +0xdad: mov     %ecx,0x1d00(%rsp,%rax,4)
     +0xdb4: movslq  0x1d04(%rsp,%rax,4),%rcx
     +0xdbc: movslq  0x224(%rsp,%rax,4),%rdx
     +0xdc4: imul    %rcx,%rdx
     +0xdc8: mov     %rdx,%rcx
     +0xdcb: imul    %rbx,%rcx
     +0xdcf: sar     $0x20,%rcx
     +0xdd3: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xdda: add     %rdx,%rcx
     +0xddd: shr     $0x20,%rcx
     +0xde1: mov     %ecx,0x1d04(%rsp,%rax,4)
     +0xde8: add     $0x2,%rax
     +0xdec: cmp     $0x100,%rax
     +0xdf2: jne     <mldsa65_signature_internal+0xd80>
     +0xdf4: movw    $0x300,0x1260(%rsp)
     +0xdfe: lea     0x2100(%rsp),%rdi
     +0xe06: mov     %r14,%rsi
     +0xe09: call    <mldsa_poly_uniform>
     +0xe0e: xor     %eax,%eax
     +0xe10: movslq  0x2100(%rsp,%rax,4),%rcx
     +0xe18: movslq  0x220(%rsp,%rax,4),%rdx
     +0xe20: imul    %rcx,%rdx
     +0xe24: mov     %rdx,%rcx
     +0xe27: imul    %rbx,%rcx
     +0xe2b: sar     $0x20,%rcx
     +0xe2f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xe36: add     %rdx,%rcx
     +0xe39: shr     $0x20,%rcx
     +0xe3d: mov     %ecx,0x2100(%rsp,%rax,4)
     +0xe44: movslq  0x2104(%rsp,%rax,4),%rcx
     +0xe4c: movslq  0x224(%rsp,%rax,4),%rdx
     +0xe54: imul    %rcx,%rdx
     +0xe58: mov     %rdx,%rcx
     +0xe5b: imul    %rbx,%rcx
     +0xe5f: sar     $0x20,%rcx
     +0xe63: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xe6a: add     %rdx,%rcx
     +0xe6d: shr     $0x20,%rcx
     +0xe71: mov     %ecx,0x2104(%rsp,%rax,4)
     +0xe78: add     $0x2,%rax
     +0xe7c: cmp     $0x100,%rax
     +0xe82: jne     <mldsa65_signature_internal+0xe10>
     +0xe84: movw    $0x400,0x1260(%rsp)
     +0xe8e: lea     0x2500(%rsp),%rdi
     +0xe96: mov     %r14,%rsi
     +0xe99: call    <mldsa_poly_uniform>
     +0xe9e: xor     %eax,%eax
     +0xea0: movslq  0x2500(%rsp,%rax,4),%rcx
     +0xea8: movslq  0x220(%rsp,%rax,4),%rdx
     +0xeb0: imul    %rcx,%rdx
     +0xeb4: mov     %rdx,%rcx
     +0xeb7: imul    %rbx,%rcx
     +0xebb: sar     $0x20,%rcx
     +0xebf: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xec6: add     %rdx,%rcx
     +0xec9: shr     $0x20,%rcx
     +0xecd: mov     %ecx,0x2500(%rsp,%rax,4)
     +0xed4: movslq  0x2504(%rsp,%rax,4),%rcx
     +0xedc: movslq  0x224(%rsp,%rax,4),%rdx
     +0xee4: imul    %rcx,%rdx
     +0xee8: mov     %rdx,%rcx
     +0xeeb: imul    %rbx,%rcx
     +0xeef: sar     $0x20,%rcx
     +0xef3: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xefa: add     %rdx,%rcx
     +0xefd: shr     $0x20,%rcx
     +0xf01: mov     %ecx,0x2504(%rsp,%rax,4)
     +0xf08: add     $0x2,%rax
     +0xf0c: cmp     $0x100,%rax
     +0xf12: jne     <mldsa65_signature_internal+0xea0>
     +0xf14: movw    $0x500,0x1260(%rsp)
     +0xf1e: lea     0x2900(%rsp),%rdi
     +0xf26: mov     %r14,%rsi
     +0xf29: call    <mldsa_poly_uniform>
     +0xf2e: xor     %eax,%eax
     +0xf30: pxor    %xmm4,%xmm4
     +0xf34: movdqa  0x16364(%rip),%xmm5
     +0xf3c: movdqa  0x1636c(%rip),%xmm6
     +0xf44: data16  data16 cs nopw 0x0(%rax,%rax,1)
     +0xf50: movslq  0x2900(%rsp,%rax,4),%rcx
     +0xf58: movslq  0x220(%rsp,%rax,4),%rdx
     +0xf60: imul    %rcx,%rdx
     +0xf64: mov     %rdx,%rcx
     +0xf67: imul    %rbx,%rcx
     +0xf6b: sar     $0x20,%rcx
     +0xf6f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xf76: add     %rdx,%rcx
     +0xf79: shr     $0x20,%rcx
     +0xf7d: mov     %ecx,0x2900(%rsp,%rax,4)
     +0xf84: movslq  0x2904(%rsp,%rax,4),%rcx
     +0xf8c: movslq  0x224(%rsp,%rax,4),%rdx
     +0xf94: imul    %rcx,%rdx
     +0xf98: mov     %rdx,%rcx
     +0xf9b: imul    %rbx,%rcx
     +0xf9f: sar     $0x20,%rcx
     +0xfa3: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xfaa: add     %rdx,%rcx
     +0xfad: shr     $0x20,%rcx
     +0xfb1: mov     %ecx,0x2904(%rsp,%rax,4)
     +0xfb8: add     $0x2,%rax
     +0xfbc: cmp     $0x100,%rax
     +0xfc2: jne     <mldsa65_signature_internal+0xf50>
     +0xfc4: jmp     <mldsa65_signature_internal+0x210>
     +0xfc9: nopl    0x0(%rax)
     +0xfd0: movdqa  %xmm4,0x1270(%rsp)
     +0xfd9: movdqa  %xmm4,0x1260(%rsp)
     +0xfe2: movdqa  %xmm4,0x1250(%rsp)
     +0xfeb: movdqa  %xmm4,0x1240(%rsp)
     +0xff4: mov     $0x4,%eax
     +0xff9: nopl    0x0(%rax)
    +0x1000: movdqa  0x14f0(%rsp,%rax,4),%xmm0
    +0x1009: movdqa  0x1500(%rsp,%rax,4),%xmm1
    +0x1012: movdqa  %xmm0,%xmm2
    +0x1016: paddd   %xmm5,%xmm2
    +0x101a: movdqa  %xmm1,%xmm3
    +0x101e: paddd   %xmm5,%xmm3
    +0x1022: psrad   $0x17,%xmm2
    +0x1027: psrad   $0x17,%xmm3
    +0x102c: pshufd  $0xf5,%xmm2,%xmm4
    +0x1031: pmuludq %xmm6,%xmm2
    +0x1035: pshufd  $0xe8,%xmm2,%xmm2
    +0x103a: pmuludq %xmm6,%xmm4
    +0x103e: pshufd  $0xe8,%xmm4,%xmm4
    +0x1043: punpckldq %xmm4,%xmm2
    +0x1047: pshufd  $0xf5,%xmm3,%xmm4
    +0x104c: pmuludq %xmm6,%xmm3
    +0x1050: pshufd  $0xe8,%xmm3,%xmm3
    +0x1055: pmuludq %xmm6,%xmm4
    +0x1059: pshufd  $0xe8,%xmm4,%xmm4
    +0x105e: punpckldq %xmm4,%xmm3
    +0x1062: paddd   %xmm0,%xmm2
    +0x1066: paddd   %xmm1,%xmm3
    +0x106a: movdqa  %xmm2,0x14f0(%rsp,%rax,4)
    +0x1073: movdqa  %xmm3,0x1500(%rsp,%rax,4)
    +0x107c: add     $0x8,%rax
    +0x1080: cmp     $0x104,%rax
    +0x1086: jne     <mldsa65_signature_internal+0x1000>
    +0x108c: mov     $0x104,%eax
    +0x1091: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x10a0: movdqa  0x14f0(%rsp,%rax,4),%xmm0
    +0x10a9: movdqa  0x1500(%rsp,%rax,4),%xmm1
    +0x10b2: movdqa  %xmm0,%xmm2
    +0x10b6: paddd   %xmm5,%xmm2
    +0x10ba: movdqa  %xmm1,%xmm3
    +0x10be: paddd   %xmm5,%xmm3
    +0x10c2: psrad   $0x17,%xmm2
    +0x10c7: psrad   $0x17,%xmm3
    +0x10cc: pshufd  $0xf5,%xmm2,%xmm4
    +0x10d1: pmuludq %xmm6,%xmm2
    +0x10d5: pshufd  $0xe8,%xmm2,%xmm2
    +0x10da: pmuludq %xmm6,%xmm4
    +0x10de: pshufd  $0xe8,%xmm4,%xmm4
    +0x10e3: punpckldq %xmm4,%xmm2
    +0x10e7: pshufd  $0xf5,%xmm3,%xmm4
    +0x10ec: pmuludq %xmm6,%xmm3
    +0x10f0: pshufd  $0xe8,%xmm3,%xmm3
    +0x10f5: pmuludq %xmm6,%xmm4
    +0x10f9: pshufd  $0xe8,%xmm4,%xmm4
    +0x10fe: punpckldq %xmm4,%xmm3
    +0x1102: paddd   %xmm0,%xmm2
    +0x1106: paddd   %xmm1,%xmm3
    +0x110a: movdqa  %xmm2,0x14f0(%rsp,%rax,4)
    +0x1113: movdqa  %xmm3,0x1500(%rsp,%rax,4)
    +0x111c: add     $0x8,%rax
    +0x1120: cmp     $0x204,%rax
    +0x1126: jne     <mldsa65_signature_internal+0x10a0>
    +0x112c: mov     $0x204,%eax
    +0x1131: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1140: movdqa  0x14f0(%rsp,%rax,4),%xmm0
    +0x1149: movdqa  0x1500(%rsp,%rax,4),%xmm1
    +0x1152: movdqa  %xmm0,%xmm2
    +0x1156: paddd   %xmm5,%xmm2
    +0x115a: movdqa  %xmm1,%xmm3
    +0x115e: paddd   %xmm5,%xmm3
    +0x1162: psrad   $0x17,%xmm2
    +0x1167: psrad   $0x17,%xmm3
    +0x116c: pshufd  $0xf5,%xmm2,%xmm4
    +0x1171: pmuludq %xmm6,%xmm2
    +0x1175: pshufd  $0xe8,%xmm2,%xmm2
    +0x117a: pmuludq %xmm6,%xmm4
    +0x117e: pshufd  $0xe8,%xmm4,%xmm4
    +0x1183: punpckldq %xmm4,%xmm2
    +0x1187: pshufd  $0xf5,%xmm3,%xmm4
    +0x118c: pmuludq %xmm6,%xmm3
    +0x1190: pshufd  $0xe8,%xmm3,%xmm3
    +0x1195: pmuludq %xmm6,%xmm4
    +0x1199: pshufd  $0xe8,%xmm4,%xmm4
    +0x119e: punpckldq %xmm4,%xmm3
    +0x11a2: paddd   %xmm0,%xmm2
    +0x11a6: paddd   %xmm1,%xmm3
    +0x11aa: movdqa  %xmm2,0x14f0(%rsp,%rax,4)
    +0x11b3: movdqa  %xmm3,0x1500(%rsp,%rax,4)
    +0x11bc: add     $0x8,%rax
    +0x11c0: cmp     $0x304,%rax
    +0x11c6: jne     <mldsa65_signature_internal+0x1140>
    +0x11cc: mov     $0x304,%eax
    +0x11d1: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x11e0: movdqa  0x14f0(%rsp,%rax,4),%xmm0
    +0x11e9: movdqa  0x1500(%rsp,%rax,4),%xmm1
    +0x11f2: movdqa  %xmm0,%xmm2
    +0x11f6: paddd   %xmm5,%xmm2
    +0x11fa: movdqa  %xmm1,%xmm3
    +0x11fe: paddd   %xmm5,%xmm3
    +0x1202: psrad   $0x17,%xmm2
    +0x1207: psrad   $0x17,%xmm3
    +0x120c: pshufd  $0xf5,%xmm2,%xmm4
    +0x1211: pmuludq %xmm6,%xmm2
    +0x1215: pshufd  $0xe8,%xmm2,%xmm2
    +0x121a: pmuludq %xmm6,%xmm4
    +0x121e: pshufd  $0xe8,%xmm4,%xmm4
    +0x1223: punpckldq %xmm4,%xmm2
    +0x1227: pshufd  $0xf5,%xmm3,%xmm4
    +0x122c: pmuludq %xmm6,%xmm3
    +0x1230: pshufd  $0xe8,%xmm3,%xmm3
    +0x1235: pmuludq %xmm6,%xmm4
    +0x1239: pshufd  $0xe8,%xmm4,%xmm4
    +0x123e: punpckldq %xmm4,%xmm3
    +0x1242: paddd   %xmm0,%xmm2
    +0x1246: paddd   %xmm1,%xmm3
    +0x124a: movdqa  %xmm2,0x14f0(%rsp,%rax,4)
    +0x1253: movdqa  %xmm3,0x1500(%rsp,%rax,4)
    +0x125c: add     $0x8,%rax
    +0x1260: cmp     $0x404,%rax
    +0x1266: jne     <mldsa65_signature_internal+0x11e0>
    +0x126c: mov     $0x404,%eax
    +0x1271: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1280: movdqa  0x14f0(%rsp,%rax,4),%xmm0
    +0x1289: movdqa  0x1500(%rsp,%rax,4),%xmm1
    +0x1292: movdqa  %xmm0,%xmm2
    +0x1296: paddd   %xmm5,%xmm2
    +0x129a: movdqa  %xmm1,%xmm3
    +0x129e: paddd   %xmm5,%xmm3
    +0x12a2: psrad   $0x17,%xmm2
    +0x12a7: psrad   $0x17,%xmm3
    +0x12ac: pshufd  $0xf5,%xmm2,%xmm4
    +0x12b1: pmuludq %xmm6,%xmm2
    +0x12b5: pshufd  $0xe8,%xmm2,%xmm2
    +0x12ba: pmuludq %xmm6,%xmm4
    +0x12be: pshufd  $0xe8,%xmm4,%xmm4
    +0x12c3: punpckldq %xmm4,%xmm2
    +0x12c7: pshufd  $0xf5,%xmm3,%xmm4
    +0x12cc: pmuludq %xmm6,%xmm3
    +0x12d0: pshufd  $0xe8,%xmm3,%xmm3
    +0x12d5: pmuludq %xmm6,%xmm4
    +0x12d9: pshufd  $0xe8,%xmm4,%xmm4
    +0x12de: punpckldq %xmm4,%xmm3
    +0x12e2: paddd   %xmm0,%xmm2
    +0x12e6: paddd   %xmm1,%xmm3
    +0x12ea: movdqa  %xmm2,0x14f0(%rsp,%rax,4)
    +0x12f3: movdqa  %xmm3,0x1500(%rsp,%rax,4)
    +0x12fc: add     $0x8,%rax
    +0x1300: cmp     $0x504,%rax
    +0x1306: jne     <mldsa65_signature_internal+0x1280>
    +0x130c: mov     $0x504,%eax
    +0x1311: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1320: movdqa  0x14f0(%rsp,%rax,4),%xmm0
    +0x1329: movdqa  0x1500(%rsp,%rax,4),%xmm1
    +0x1332: movdqa  %xmm0,%xmm2
    +0x1336: paddd   %xmm5,%xmm2
    +0x133a: movdqa  %xmm1,%xmm3
    +0x133e: paddd   %xmm5,%xmm3
    +0x1342: psrad   $0x17,%xmm2
    +0x1347: psrad   $0x17,%xmm3
    +0x134c: pshufd  $0xf5,%xmm2,%xmm4
    +0x1351: pmuludq %xmm6,%xmm2
    +0x1355: pshufd  $0xe8,%xmm2,%xmm2
    +0x135a: pmuludq %xmm6,%xmm4
    +0x135e: pshufd  $0xe8,%xmm4,%xmm4
    +0x1363: punpckldq %xmm4,%xmm2
    +0x1367: pshufd  $0xf5,%xmm3,%xmm4
    +0x136c: pmuludq %xmm6,%xmm3
    +0x1370: pshufd  $0xe8,%xmm3,%xmm3
    +0x1375: pmuludq %xmm6,%xmm4
    +0x1379: pshufd  $0xe8,%xmm4,%xmm4
    +0x137e: punpckldq %xmm4,%xmm3
    +0x1382: paddd   %xmm0,%xmm2
    +0x1386: paddd   %xmm1,%xmm3
    +0x138a: movdqa  %xmm2,0x14f0(%rsp,%rax,4)
    +0x1393: movdqa  %xmm3,0x1500(%rsp,%rax,4)
    +0x139c: add     $0x8,%rax
    +0x13a0: cmp     $0x604,%rax
    +0x13a6: jne     <mldsa65_signature_internal+0x1320>
    +0x13ac: lea     0x1500(%rsp),%rdi
    +0x13b4: call    <mldsa_poly_invntt_tomont>
    +0x13b9: lea     0x1900(%rsp),%rdi
    +0x13c1: call    <mldsa_poly_invntt_tomont>
    +0x13c6: lea     0x1d00(%rsp),%rdi
    +0x13ce: call    <mldsa_poly_invntt_tomont>
    +0x13d3: lea     0x2100(%rsp),%rdi
    +0x13db: call    <mldsa_poly_invntt_tomont>
    +0x13e0: lea     0x2500(%rsp),%rdi
    +0x13e8: call    <mldsa_poly_invntt_tomont>
    +0x13ed: lea     0x2900(%rsp),%rdi
    +0x13f5: call    <mldsa_poly_invntt_tomont>
    +0x13fa: xor     %eax,%eax
    +0x13fc: nopl    0x0(%rax)
    +0x1400: movslq  0x1500(%rsp,%rax,4),%rcx
    +0x1408: lea     0x7fe001(%rcx),%edx
    +0x140e: mov     %rcx,%rsi
    +0x1411: shr     $0x1f,%rsi
    +0x1415: xor     %ecx,%edx
    +0x1417: and     %esi,%edx
    +0x1419: xor     %ecx,%edx
    +0x141b: mov     %edx,0x1500(%rsp,%rax,4)
    +0x1422: inc     %rax
    +0x1425: cmp     $0x100,%rax
    +0x142b: jne     <mldsa65_signature_internal+0x1400>
    +0x142d: mov     $0x100,%eax
    +0x1432: lea     0x6a0(%rsp),%r8
    +0x143a: movdqa  0x1615e(%rip),%xmm6
    +0x1442: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1450: movslq  0x1500(%rsp,%rax,4),%rcx
    +0x1458: lea     0x7fe001(%rcx),%edx
    +0x145e: mov     %rcx,%rsi
    +0x1461: shr     $0x1f,%rsi
    +0x1465: xor     %ecx,%edx
    +0x1467: and     %esi,%edx
    +0x1469: xor     %ecx,%edx
    +0x146b: mov     %edx,0x1500(%rsp,%rax,4)
    +0x1472: inc     %rax
    +0x1475: cmp     $0x200,%rax
    +0x147b: jne     <mldsa65_signature_internal+0x1450>
    +0x147d: mov     $0x200,%eax
    +0x1482: pxor    %xmm5,%xmm5
    +0x1486: cs      nopw 0x0(%rax,%rax,1)
    +0x1490: movslq  0x1500(%rsp,%rax,4),%rcx
    +0x1498: lea     0x7fe001(%rcx),%edx
    +0x149e: mov     %rcx,%rsi
    +0x14a1: shr     $0x1f,%rsi
    +0x14a5: xor     %ecx,%edx
    +0x14a7: and     %esi,%edx
    +0x14a9: xor     %ecx,%edx
    +0x14ab: mov     %edx,0x1500(%rsp,%rax,4)
    +0x14b2: inc     %rax
    +0x14b5: cmp     $0x300,%rax
    +0x14bb: jne     <mldsa65_signature_internal+0x1490>
    +0x14bd: mov     $0x300,%eax
    +0x14c2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x14d0: movslq  0x1500(%rsp,%rax,4),%rcx
    +0x14d8: lea     0x7fe001(%rcx),%edx
    +0x14de: mov     %rcx,%rsi
    +0x14e1: shr     $0x1f,%rsi
    +0x14e5: xor     %ecx,%edx
    +0x14e7: and     %esi,%edx
    +0x14e9: xor     %ecx,%edx
    +0x14eb: mov     %edx,0x1500(%rsp,%rax,4)
    +0x14f2: inc     %rax
    +0x14f5: cmp     $0x400,%rax
    +0x14fb: jne     <mldsa65_signature_internal+0x14d0>
    +0x14fd: mov     $0x400,%eax
    +0x1502: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1510: movslq  0x1500(%rsp,%rax,4),%rcx
    +0x1518: lea     0x7fe001(%rcx),%edx
    +0x151e: mov     %rcx,%rsi
    +0x1521: shr     $0x1f,%rsi
    +0x1525: xor     %ecx,%edx
    +0x1527: and     %esi,%edx
    +0x1529: xor     %ecx,%edx
    +0x152b: mov     %edx,0x1500(%rsp,%rax,4)
    +0x1532: inc     %rax
    +0x1535: cmp     $0x500,%rax
    +0x153b: jne     <mldsa65_signature_internal+0x1510>
    +0x153d: mov     $0x500,%eax
    +0x1542: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1550: movslq  0x1500(%rsp,%rax,4),%rcx
    +0x1558: lea     0x7fe001(%rcx),%edx
    +0x155e: mov     %rcx,%rsi
    +0x1561: shr     $0x1f,%rsi
    +0x1565: xor     %ecx,%edx
    +0x1567: and     %esi,%edx
    +0x1569: xor     %ecx,%edx
    +0x156b: mov     %edx,0x1500(%rsp,%rax,4)
    +0x1572: inc     %rax
    +0x1575: cmp     $0x600,%rax
    +0x157b: jne     <mldsa65_signature_internal+0x1550>
    +0x157d: xor     %eax,%eax
    +0x157f: nop     
    +0x1580: mov     0x1500(%rsp,%rax,4),%ecx
    +0x1587: lea     0x7f(%rcx),%edx
    +0x158a: sar     $0x7,%edx
    +0x158d: mov     %edx,%esi
    +0x158f: shl     $0xa,%edx
    +0x1592: add     %esi,%edx
    +0x1594: add     $0x200000,%edx
    +0x159a: shr     $0x16,%edx
    +0x159d: and     $0xf,%edx
    +0x15a0: mov     %edx,0x220(%rsp,%rax,4)
    +0x15a7: imul    $0xfff80200,%edx,%edx
    +0x15ad: lea     (%rdx,%rcx,1),%esi
    +0x15b0: mov     %esi,0x1500(%rsp,%rax,4)
    +0x15b7: add     %edx,%ecx
    +0x15b9: add     $0xff801fff,%ecx
    +0x15bf: mov     $0x3ff000,%edx
    +0x15c4: sub     %esi,%edx
    +0x15c6: movslq  %edx,%rdx
    +0x15c9: shr     $0x1f,%rdx
    +0x15cd: xor     %esi,%ecx
    +0x15cf: and     %edx,%ecx
    +0x15d1: xor     %esi,%ecx
    +0x15d3: mov     %ecx,0x1500(%rsp,%rax,4)
    +0x15da: inc     %rax
    +0x15dd: cmp     $0x100,%rax
    +0x15e3: jne     <mldsa65_signature_internal+0x1580>
    +0x15e5: mov     $0x4,%eax
    +0x15ea: nopw    0x0(%rax,%rax,1)
    +0x15f0: movaps  0x200(%rsp,%rax,8),%xmm0
    +0x15f8: movaps  0x210(%rsp,%rax,8),%xmm1
    +0x1600: movaps  0x220(%rsp,%rax,8),%xmm2
    +0x1608: movaps  0x230(%rsp,%rax,8),%xmm3
    +0x1610: movaps  %xmm0,%xmm4
    +0x1613: shufps  $0x88,%xmm1,%xmm4
    +0x1617: shufps  $0xdd,%xmm1,%xmm0
    +0x161b: movaps  %xmm2,%xmm1
    +0x161e: shufps  $0x88,%xmm3,%xmm1
    +0x1622: shufps  $0xdd,%xmm3,%xmm2
    +0x1626: pslld   $0x4,%xmm0
    +0x162b: por     %xmm4,%xmm0
    +0x162f: pslld   $0x4,%xmm2
    +0x1634: por     %xmm1,%xmm2
    +0x1638: pand    %xmm6,%xmm0
    +0x163c: packuswb %xmm0,%xmm0
    +0x1640: packuswb %xmm0,%xmm0
    +0x1644: pand    %xmm6,%xmm2
    +0x1648: packuswb %xmm2,%xmm2
    +0x164c: packuswb %xmm2,%xmm2
    +0x1650: movd    %xmm0,0xb1c(%rsp,%rax,1)
    +0x1659: movd    %xmm2,0xb20(%rsp,%rax,1)
    +0x1662: add     $0x8,%rax
    +0x1666: cmp     $0x84,%rax
    +0x166c: jne     <mldsa65_signature_internal+0x15f0>
    +0x166e: mov     $0x100,%eax
    +0x1673: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1680: mov     0x1500(%rsp,%rax,4),%ecx
    +0x1687: lea     0x7f(%rcx),%edx
    +0x168a: sar     $0x7,%edx
    +0x168d: mov     %edx,%esi
    +0x168f: shl     $0xa,%edx
    +0x1692: add     %esi,%edx
    +0x1694: add     $0x200000,%edx
    +0x169a: shr     $0x16,%edx
    +0x169d: and     $0xf,%edx
    +0x16a0: mov     %edx,-0x1e0(%rsp,%rax,4)
    +0x16a7: imul    $0xfff80200,%edx,%edx
    +0x16ad: lea     (%rdx,%rcx,1),%esi
    +0x16b0: mov     %esi,0x1500(%rsp,%rax,4)
    +0x16b7: add     %edx,%ecx
    +0x16b9: add     $0xff801fff,%ecx
    +0x16bf: mov     $0x3ff000,%edx
    +0x16c4: sub     %esi,%edx
    +0x16c6: movslq  %edx,%rdx
    +0x16c9: shr     $0x1f,%rdx
    +0x16cd: xor     %esi,%ecx
    +0x16cf: and     %edx,%ecx
    +0x16d1: xor     %esi,%ecx
    +0x16d3: mov     %ecx,0x1500(%rsp,%rax,4)
    +0x16da: inc     %rax
    +0x16dd: cmp     $0x200,%rax
    +0x16e3: jne     <mldsa65_signature_internal+0x1680>
    +0x16e5: mov     $0x4,%eax
    +0x16ea: nopw    0x0(%rax,%rax,1)
    +0x16f0: movaps  0x200(%rsp,%rax,8),%xmm0
    +0x16f8: movaps  0x210(%rsp,%rax,8),%xmm1
    +0x1700: movaps  0x220(%rsp,%rax,8),%xmm2
    +0x1708: movaps  0x230(%rsp,%rax,8),%xmm3
    +0x1710: movaps  %xmm0,%xmm4
    +0x1713: shufps  $0x88,%xmm1,%xmm4
    +0x1717: shufps  $0xdd,%xmm1,%xmm0
    +0x171b: movaps  %xmm2,%xmm1
    +0x171e: shufps  $0x88,%xmm3,%xmm1
    +0x1722: shufps  $0xdd,%xmm3,%xmm2
    +0x1726: pslld   $0x4,%xmm0
    +0x172b: por     %xmm4,%xmm0
    +0x172f: pslld   $0x4,%xmm2
    +0x1734: por     %xmm1,%xmm2
    +0x1738: pand    %xmm6,%xmm0
    +0x173c: packuswb %xmm0,%xmm0
    +0x1740: packuswb %xmm0,%xmm0
    +0x1744: pand    %xmm6,%xmm2
    +0x1748: packuswb %xmm2,%xmm2
    +0x174c: packuswb %xmm2,%xmm2
    +0x1750: movd    %xmm0,0xb9c(%rsp,%rax,1)
    +0x1759: movd    %xmm2,0xba0(%rsp,%rax,1)
    +0x1762: add     $0x8,%rax
    +0x1766: cmp     $0x84,%rax
    +0x176c: jne     <mldsa65_signature_internal+0x16f0>
    +0x176e: mov     $0x200,%eax
    +0x1773: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1780: mov     0x1500(%rsp,%rax,4),%ecx
    +0x1787: lea     0x7f(%rcx),%edx
    +0x178a: sar     $0x7,%edx
    +0x178d: mov     %edx,%esi
    +0x178f: shl     $0xa,%edx
    +0x1792: add     %esi,%edx
    +0x1794: add     $0x200000,%edx
    +0x179a: shr     $0x16,%edx
    +0x179d: and     $0xf,%edx
    +0x17a0: mov     %edx,-0x5e0(%rsp,%rax,4)
    +0x17a7: imul    $0xfff80200,%edx,%edx
    +0x17ad: lea     (%rdx,%rcx,1),%esi
    +0x17b0: mov     %esi,0x1500(%rsp,%rax,4)
    +0x17b7: add     %edx,%ecx
    +0x17b9: add     $0xff801fff,%ecx
    +0x17bf: mov     $0x3ff000,%edx
    +0x17c4: sub     %esi,%edx
    +0x17c6: movslq  %edx,%rdx
    +0x17c9: shr     $0x1f,%rdx
    +0x17cd: xor     %esi,%ecx
    +0x17cf: and     %edx,%ecx
    +0x17d1: xor     %esi,%ecx
    +0x17d3: mov     %ecx,0x1500(%rsp,%rax,4)
    +0x17da: inc     %rax
    +0x17dd: cmp     $0x300,%rax
    +0x17e3: jne     <mldsa65_signature_internal+0x1780>
    +0x17e5: xor     %eax,%eax
    +0x17e7: nopw    0x0(%rax,%rax,1)
    +0x17f0: movaps  0x220(%rsp,%rax,8),%xmm0
    +0x17f8: movaps  0x230(%rsp,%rax,8),%xmm1
    +0x1800: movaps  0x240(%rsp,%rax,8),%xmm2
    +0x1808: movaps  0x250(%rsp,%rax,8),%xmm3
    +0x1810: movaps  %xmm0,%xmm4
    +0x1813: shufps  $0x88,%xmm1,%xmm4
    +0x1817: shufps  $0xdd,%xmm1,%xmm0
    +0x181b: movaps  %xmm2,%xmm1
    +0x181e: shufps  $0x88,%xmm3,%xmm1
    +0x1822: shufps  $0xdd,%xmm3,%xmm2
    +0x1826: pslld   $0x4,%xmm0
    +0x182b: por     %xmm4,%xmm0
    +0x182f: pslld   $0x4,%xmm2
    +0x1834: por     %xmm1,%xmm2
    +0x1838: pand    %xmm6,%xmm0
    +0x183c: packuswb %xmm0,%xmm0
    +0x1840: packuswb %xmm0,%xmm0
    +0x1844: pand    %xmm6,%xmm2
    +0x1848: packuswb %xmm2,%xmm2
    +0x184c: packuswb %xmm2,%xmm2
    +0x1850: movd    %xmm0,0xc20(%rsp,%rax,1)
    +0x1859: movd    %xmm2,0xc24(%rsp,%rax,1)
    +0x1862: add     $0x8,%rax
    +0x1866: cmp     $0x80,%rax
    +0x186c: jne     <mldsa65_signature_internal+0x17f0>
    +0x186e: mov     $0x300,%eax
    +0x1873: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1880: mov     0x1500(%rsp,%rax,4),%ecx
    +0x1887: lea     0x7f(%rcx),%edx
    +0x188a: sar     $0x7,%edx
    +0x188d: mov     %edx,%esi
    +0x188f: shl     $0xa,%edx
    +0x1892: add     %esi,%edx
    +0x1894: add     $0x200000,%edx
    +0x189a: shr     $0x16,%edx
    +0x189d: and     $0xf,%edx
    +0x18a0: mov     %edx,-0x9e0(%rsp,%rax,4)
    +0x18a7: imul    $0xfff80200,%edx,%edx
    +0x18ad: lea     (%rdx,%rcx,1),%esi
    +0x18b0: mov     %esi,0x1500(%rsp,%rax,4)
    +0x18b7: add     %edx,%ecx
    +0x18b9: add     $0xff801fff,%ecx
    +0x18bf: mov     $0x3ff000,%edx
    +0x18c4: sub     %esi,%edx
    +0x18c6: movslq  %edx,%rdx
    +0x18c9: shr     $0x1f,%rdx
    +0x18cd: xor     %esi,%ecx
    +0x18cf: and     %edx,%ecx
    +0x18d1: xor     %esi,%ecx
    +0x18d3: mov     %ecx,0x1500(%rsp,%rax,4)
    +0x18da: inc     %rax
    +0x18dd: cmp     $0x400,%rax
    +0x18e3: jne     <mldsa65_signature_internal+0x1880>
    +0x18e5: xor     %eax,%eax
    +0x18e7: nopw    0x0(%rax,%rax,1)
    +0x18f0: movaps  0x220(%rsp,%rax,8),%xmm0
    +0x18f8: movaps  0x230(%rsp,%rax,8),%xmm1
    +0x1900: movaps  0x240(%rsp,%rax,8),%xmm2
    +0x1908: movaps  0x250(%rsp,%rax,8),%xmm3
    +0x1910: movaps  %xmm0,%xmm4
    +0x1913: shufps  $0x88,%xmm1,%xmm4
    +0x1917: shufps  $0xdd,%xmm1,%xmm0
    +0x191b: movaps  %xmm2,%xmm1
    +0x191e: shufps  $0x88,%xmm3,%xmm1
    +0x1922: shufps  $0xdd,%xmm3,%xmm2
    +0x1926: pslld   $0x4,%xmm0
    +0x192b: por     %xmm4,%xmm0
    +0x192f: pslld   $0x4,%xmm2
    +0x1934: por     %xmm1,%xmm2
    +0x1938: pand    %xmm6,%xmm0
    +0x193c: packuswb %xmm0,%xmm0
    +0x1940: packuswb %xmm0,%xmm0
    +0x1944: pand    %xmm6,%xmm2
    +0x1948: packuswb %xmm2,%xmm2
    +0x194c: packuswb %xmm2,%xmm2
    +0x1950: movd    %xmm0,0xca0(%rsp,%rax,1)
    +0x1959: movd    %xmm2,0xca4(%rsp,%rax,1)
    +0x1962: add     $0x8,%rax
    +0x1966: cmp     $0x80,%rax
    +0x196c: jne     <mldsa65_signature_internal+0x18f0>
    +0x196e: mov     $0x400,%eax
    +0x1973: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1980: mov     0x1500(%rsp,%rax,4),%ecx
    +0x1987: lea     0x7f(%rcx),%edx
    +0x198a: sar     $0x7,%edx
    +0x198d: mov     %edx,%esi
    +0x198f: shl     $0xa,%edx
    +0x1992: add     %esi,%edx
    +0x1994: add     $0x200000,%edx
    +0x199a: shr     $0x16,%edx
    +0x199d: and     $0xf,%edx
    +0x19a0: mov     %edx,-0xde0(%rsp,%rax,4)
    +0x19a7: imul    $0xfff80200,%edx,%edx
    +0x19ad: lea     (%rdx,%rcx,1),%esi
    +0x19b0: mov     %esi,0x1500(%rsp,%rax,4)
    +0x19b7: add     %edx,%ecx
    +0x19b9: add     $0xff801fff,%ecx
    +0x19bf: mov     $0x3ff000,%edx
    +0x19c4: sub     %esi,%edx
    +0x19c6: movslq  %edx,%rdx
    +0x19c9: shr     $0x1f,%rdx
    +0x19cd: xor     %esi,%ecx
    +0x19cf: and     %edx,%ecx
    +0x19d1: xor     %esi,%ecx
    +0x19d3: mov     %ecx,0x1500(%rsp,%rax,4)
    +0x19da: inc     %rax
    +0x19dd: cmp     $0x500,%rax
    +0x19e3: jne     <mldsa65_signature_internal+0x1980>
    +0x19e5: xor     %eax,%eax
    +0x19e7: nopw    0x0(%rax,%rax,1)
    +0x19f0: movaps  0x220(%rsp,%rax,8),%xmm0
    +0x19f8: movaps  0x230(%rsp,%rax,8),%xmm1
    +0x1a00: movaps  0x240(%rsp,%rax,8),%xmm2
    +0x1a08: movaps  0x250(%rsp,%rax,8),%xmm3
    +0x1a10: movaps  %xmm0,%xmm4
    +0x1a13: shufps  $0x88,%xmm1,%xmm4
    +0x1a17: shufps  $0xdd,%xmm1,%xmm0
    +0x1a1b: movaps  %xmm2,%xmm1
    +0x1a1e: shufps  $0x88,%xmm3,%xmm1
    +0x1a22: shufps  $0xdd,%xmm3,%xmm2
    +0x1a26: pslld   $0x4,%xmm0
    +0x1a2b: por     %xmm4,%xmm0
    +0x1a2f: pslld   $0x4,%xmm2
    +0x1a34: por     %xmm1,%xmm2
    +0x1a38: pand    %xmm6,%xmm0
    +0x1a3c: packuswb %xmm0,%xmm0
    +0x1a40: packuswb %xmm0,%xmm0
    +0x1a44: pand    %xmm6,%xmm2
    +0x1a48: packuswb %xmm2,%xmm2
    +0x1a4c: packuswb %xmm2,%xmm2
    +0x1a50: movd    %xmm0,0xd20(%rsp,%rax,1)
    +0x1a59: movd    %xmm2,0xd24(%rsp,%rax,1)
    +0x1a62: add     $0x8,%rax
    +0x1a66: cmp     $0x80,%rax
    +0x1a6c: jne     <mldsa65_signature_internal+0x19f0>
    +0x1a6e: mov     $0x500,%eax
    +0x1a73: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1a80: mov     0x1500(%rsp,%rax,4),%ecx
    +0x1a87: lea     0x7f(%rcx),%edx
    +0x1a8a: sar     $0x7,%edx
    +0x1a8d: mov     %edx,%esi
    +0x1a8f: shl     $0xa,%edx
    +0x1a92: add     %esi,%edx
    +0x1a94: add     $0x200000,%edx
    +0x1a9a: shr     $0x16,%edx
    +0x1a9d: and     $0xf,%edx
    +0x1aa0: mov     %edx,-0x11e0(%rsp,%rax,4)
    +0x1aa7: imul    $0xfff80200,%edx,%edx
    +0x1aad: lea     (%rdx,%rcx,1),%esi
    +0x1ab0: mov     %esi,0x1500(%rsp,%rax,4)
    +0x1ab7: add     %edx,%ecx
    +0x1ab9: add     $0xff801fff,%ecx
    +0x1abf: mov     $0x3ff000,%edx
    +0x1ac4: sub     %esi,%edx
    +0x1ac6: movslq  %edx,%rdx
    +0x1ac9: shr     $0x1f,%rdx
    +0x1acd: xor     %esi,%ecx
    +0x1acf: and     %edx,%ecx
    +0x1ad1: xor     %esi,%ecx
    +0x1ad3: mov     %ecx,0x1500(%rsp,%rax,4)
    +0x1ada: inc     %rax
    +0x1add: cmp     $0x600,%rax
    +0x1ae3: jne     <mldsa65_signature_internal+0x1a80>
    +0x1ae5: xor     %eax,%eax
    +0x1ae7: nopw    0x0(%rax,%rax,1)
    +0x1af0: movaps  0x220(%rsp,%rax,8),%xmm0
    +0x1af8: movaps  0x230(%rsp,%rax,8),%xmm1
    +0x1b00: movaps  0x240(%rsp,%rax,8),%xmm2
    +0x1b08: movaps  0x250(%rsp,%rax,8),%xmm3
    +0x1b10: movaps  %xmm0,%xmm4
    +0x1b13: shufps  $0x88,%xmm1,%xmm4
    +0x1b17: shufps  $0xdd,%xmm1,%xmm0
    +0x1b1b: movaps  %xmm2,%xmm1
    +0x1b1e: shufps  $0x88,%xmm3,%xmm1
    +0x1b22: shufps  $0xdd,%xmm3,%xmm2
    +0x1b26: pslld   $0x4,%xmm0
    +0x1b2b: por     %xmm4,%xmm0
    +0x1b2f: pslld   $0x4,%xmm2
    +0x1b34: por     %xmm1,%xmm2
    +0x1b38: pand    %xmm6,%xmm0
    +0x1b3c: packuswb %xmm0,%xmm0
    +0x1b40: packuswb %xmm0,%xmm0
    +0x1b44: pand    %xmm6,%xmm2
    +0x1b48: packuswb %xmm2,%xmm2
    +0x1b4c: packuswb %xmm2,%xmm2
    +0x1b50: movd    %xmm0,0xda0(%rsp,%rax,1)
    +0x1b59: movd    %xmm2,0xda4(%rsp,%rax,1)
    +0x1b62: add     $0x8,%rax
    +0x1b66: cmp     $0x80,%rax
    +0x1b6c: jne     <mldsa65_signature_internal+0x1af0>
    +0x1b6e: sub     $0x10,%rsp
    +0x1b72: movdqu  %xmm5,(%rsp)
    +0x1b77: mov     $0x30,%esi
    +0x1b7c: mov     $0x40,%ecx
    +0x1b81: mov     $0x300,%r9d
    +0x1b87: lea     0x1f0(%rsp),%r15
    +0x1b8f: mov     %r15,%rdi
    +0x1b92: mov     %r8,%rdx
    +0x1b95: lea     0xb30(%rsp),%r8
    +0x1b9d: call    <mld_H65>
    +0x1ba2: add     $0x10,%rsp
    +0x1ba6: lea     0x2d00(%rsp),%r14
    +0x1bae: mov     %r14,%rdi
    +0x1bb1: mov     %r15,%rsi
    +0x1bb4: call    <mldsa65_poly_challenge>
    +0x1bb9: mov     %r14,%rdi
    +0x1bbc: call    <mldsa_poly_ntt>
    +0x1bc1: mov     0xa8(%rsp),%r8
    +0x1bc9: xor     %ecx,%ecx
    +0x1bcb: xor     %r15d,%r15d
    +0x1bce: xchg    %ax,%ax
    +0x1bd0: mov     0x60(%rsp),%rax
    +0x1bd5: mov     %rcx,0xa0(%rsp)
    +0x1bdd: add     %rcx,%rax
    +0x1be0: xor     %ecx,%ecx
    +0x1be2: lea     0x110(%rsp),%r14
    +0x1bea: nopw    0x0(%rax,%rax,1)
    +0x1bf0: movzbl  (%rax,%rcx,1),%edx
    +0x1bf4: and     $0xf,%edx
    +0x1bf7: mov     %edx,0x720(%rsp,%rcx,8)
    +0x1bfe: movzbl  (%rax,%rcx,1),%esi
    +0x1c02: shr     $0x4,%esi
    +0x1c05: mov     $0x4,%edi
    +0x1c0a: sub     %edx,%edi
    +0x1c0c: mov     %edi,0x720(%rsp,%rcx,8)
    +0x1c13: mov     $0x4,%edx
    +0x1c18: sub     %esi,%edx
    +0x1c1a: mov     %edx,0x724(%rsp,%rcx,8)
    +0x1c21: inc     %rcx
    +0x1c24: cmp     $0x80,%rcx
    +0x1c2b: jne     <mldsa65_signature_internal+0x1bf0>
    +0x1c2d: mov     %r8,0x18(%rsp)
    +0x1c32: lea     0x720(%rsp),%rdi
    +0x1c3a: call    <mldsa_poly_ntt>
    +0x1c3f: mov     $0x1,%eax
    +0x1c44: data16  data16 cs nopw 0x0(%rax,%rax,1)
    +0x1c50: movslq  0x71c(%rsp,%rax,4),%rcx
    +0x1c58: movslq  0x2cfc(%rsp,%rax,4),%rdx
    +0x1c60: imul    %rcx,%rdx
    +0x1c64: mov     %rdx,%rcx
    +0x1c67: imul    %rbx,%rcx
    +0x1c6b: sar     $0x20,%rcx
    +0x1c6f: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x1c76: add     %rdx,%rcx
    +0x1c79: shr     $0x20,%rcx
    +0x1c7d: mov     %ecx,0x71c(%rsp,%rax,4)
    +0x1c84: movslq  0x720(%rsp,%rax,4),%rcx
    +0x1c8c: movslq  0x2d00(%rsp,%rax,4),%rdx
    +0x1c94: imul    %rcx,%rdx
    +0x1c98: mov     %rdx,%rcx
    +0x1c9b: imul    %rbx,%rcx
    +0x1c9f: sar     $0x20,%rcx
    +0x1ca3: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x1caa: add     %rdx,%rcx
    +0x1cad: shr     $0x20,%rcx
    +0x1cb1: mov     %ecx,0x720(%rsp,%rax,4)
    +0x1cb8: add     $0x2,%rax
    +0x1cbc: cmp     $0x101,%rax
    +0x1cc2: jne     <mldsa65_signature_internal+0x1c50>
    +0x1cc4: lea     0x720(%rsp),%rdi
    +0x1ccc: call    <mldsa_poly_invntt_tomont>
    +0x1cd1: mov     0x80(%rsp),%rax
    +0x1cd9: movzwl  0x88(%rsp),%ecx
    +0x1ce1: mov     %r15,0xb8(%rsp)
    +0x1ce9: add     %r15w,%cx
    +0x1ced: movups  (%rax),%xmm0
    +0x1cf0: movups  0x10(%rax),%xmm1
    +0x1cf4: movups  0x20(%rax),%xmm2
    +0x1cf8: movdqu  0x30(%rax),%xmm3
    +0x1cfd: movaps  %xmm0,0xc0(%rsp)
    +0x1d05: movaps  %xmm1,0xd0(%rsp)
    +0x1d0d: movaps  %xmm2,0xe0(%rsp)
    +0x1d15: movdqa  %xmm3,0xf0(%rsp)
    +0x1d1e: mov     %cx,0x100(%rsp)
    +0x1d26: xorps   %xmm0,%xmm0
    +0x1d29: movaps  %xmm0,0x110(%rsp)
    +0x1d31: movaps  %xmm0,0x120(%rsp)
    +0x1d39: movaps  %xmm0,0x130(%rsp)
    +0x1d41: movaps  %xmm0,0x140(%rsp)
    +0x1d49: movaps  %xmm0,0x150(%rsp)
    +0x1d51: movaps  %xmm0,0x160(%rsp)
    +0x1d59: movaps  %xmm0,0x170(%rsp)
    +0x1d61: movaps  %xmm0,0x180(%rsp)
    +0x1d69: movaps  %xmm0,0x190(%rsp)
    +0x1d71: movaps  %xmm0,0x1a0(%rsp)
    +0x1d79: movaps  %xmm0,0x1b0(%rsp)
    +0x1d81: movaps  %xmm0,0x1c0(%rsp)
    +0x1d89: movups  %xmm0,0x1cc(%rsp)
    +0x1d91: movaps  0xc0(%rsp),%xmm0
    +0x1d99: movaps  0x120(%rsp),%xmm1
    +0x1da1: xorps   0xd0(%rsp),%xmm1
    +0x1da9: movaps  %xmm0,0x110(%rsp)
    +0x1db1: movaps  %xmm1,0x120(%rsp)
    +0x1db9: movdqa  0x130(%rsp),%xmm0
    +0x1dc2: movdqa  0x140(%rsp),%xmm1
    +0x1dcb: pxor    0xe0(%rsp),%xmm0
    +0x1dd4: movdqa  0x150(%rsp),%xmm2
    +0x1ddd: pxor    0xf0(%rsp),%xmm1
    +0x1de6: movdqa  %xmm0,0x130(%rsp)
    +0x1def: movdqa  %xmm1,0x140(%rsp)
    +0x1df8: pxor    0x100(%rsp),%xmm2
    +0x1e01: movd    %xmm2,%eax
    +0x1e05: mov     %ax,0x150(%rsp)
    +0x1e0d: xorb    $0x1f,0x152(%rsp)
    +0x1e15: xorb    $0x80,0x197(%rsp)
    +0x1e1d: movl    $0x88,0x1d8(%rsp)
    +0x1e28: mov     $0x88,%r12d
    +0x1e2e: mov     $0x2a8,%r15d
    +0x1e34: xor     %ebx,%ebx
    +0x1e36: jmp     <mldsa65_signature_internal+0x1e7c>
    +0x1e38: nopl    0x0(%rax,%rax,1)
    +0x1e40: mov     $0x88,%r13d
    +0x1e46: sub     %r12d,%r13d
    +0x1e49: cmp     %r13,%r15
    +0x1e4c: cmovb   %r15,%r13
    +0x1e50: mov     %r12d,%eax
    +0x1e53: lea     (%rsp,%rax,1),%rsi
    +0x1e57: add     $0x110,%rsi
    +0x1e5e: lea     (%rsp,%rbx,1),%rdi
    +0x1e62: add     $0x1240,%rdi
    +0x1e69: mov     %r13,%rdx
    +0x1e6c: call    <memcpy>
    +0x1e71: add     %r13d,%r12d
    +0x1e74: add     %r13,%rbx
    +0x1e77: sub     %r13,%r15
    +0x1e7a: je      <mldsa65_signature_internal+0x1eb0>
    +0x1e7c: cmp     $0x88,%r12d
    +0x1e83: jne     <mldsa65_signature_internal+0x1e40>
    +0x1e85: mov     %r14,%rdi
    +0x1e88: call    <mldsa_keccakf1600_permute>
    +0x1e8d: cmp     $0x88,%r15
    +0x1e94: mov     $0x88,%r13d
    +0x1e9a: cmovb   %r15,%r13
    +0x1e9e: xor     %r12d,%r12d
    +0x1ea1: mov     %r14,%rsi
    +0x1ea4: jmp     <mldsa65_signature_internal+0x1e5e>
    +0x1ea6: cs      nopw 0x0(%rax,%rax,1)
    +0x1eb0: lea     0x1244(%rsp),%rax
    +0x1eb8: xor     %ecx,%ecx
    +0x1eba: nopw    0x0(%rax,%rax,1)
    +0x1ec0: movzwl  -0x4(%rax),%edx
    +0x1ec4: movzbl  -0x2(%rax),%esi
    +0x1ec8: mov     %esi,%edi
    +0x1eca: and     $0xf,%edi
    +0x1ecd: shl     $0x10,%edi
    +0x1ed0: or      %edx,%edi
    +0x1ed2: shr     $0x4,%esi
    +0x1ed5: movzbl  -0x1(%rax),%edx
    +0x1ed9: movzbl  (%rax),%r8d
    +0x1edd: mov     $0x80000,%r9d
    +0x1ee3: sub     %edi,%r9d
    +0x1ee6: mov     %r9d,0x220(%rsp,%rcx,8)
    +0x1eee: shl     $0xc,%r8d
    +0x1ef2: shl     $0x4,%edx
    +0x1ef5: or      %esi,%edx
    +0x1ef7: or      %r8d,%edx
    +0x1efa: mov     $0x80000,%esi
    +0x1eff: sub     %edx,%esi
    +0x1f01: mov     %esi,0x224(%rsp,%rcx,8)
    +0x1f08: inc     %rcx
    +0x1f0b: add     $0x5,%rax
    +0x1f0f: cmp     $0x80,%rcx
    +0x1f16: jne     <mldsa65_signature_internal+0x1ec0>
    +0x1f18: pxor    %xmm0,%xmm0
    +0x1f1c: movdqa  %xmm0,0x1d0(%rsp)
    +0x1f25: movdqa  %xmm0,0x1c0(%rsp)
    +0x1f2e: movdqa  %xmm0,0x1b0(%rsp)
    +0x1f37: movdqa  %xmm0,0x1a0(%rsp)
    +0x1f40: movdqa  %xmm0,0x190(%rsp)
    +0x1f49: movdqa  %xmm0,0x180(%rsp)
    +0x1f52: movdqa  %xmm0,0x170(%rsp)
    +0x1f5b: movdqa  %xmm0,0x160(%rsp)
    +0x1f64: movdqa  %xmm0,0x150(%rsp)
    +0x1f6d: movdqa  %xmm0,0x140(%rsp)
    +0x1f76: movdqa  %xmm0,0x130(%rsp)
    +0x1f7f: movdqa  %xmm0,0x120(%rsp)
    +0x1f88: movdqa  %xmm0,0x110(%rsp)
    +0x1f91: mov     $0x2a8,%edx
    +0x1f96: lea     0x1240(%rsp),%r14
    +0x1f9e: mov     %r14,%rdi
    +0x1fa1: xor     %esi,%esi
    +0x1fa3: call    <memset>
    +0x1fa8: pxor    %xmm5,%xmm5
    +0x1fac: movdqa  %xmm5,0xf0(%rsp)
    +0x1fb5: movdqa  %xmm5,0xe0(%rsp)
    +0x1fbe: movdqa  %xmm5,0xd0(%rsp)
    +0x1fc7: movdqa  %xmm5,0xc0(%rsp)
    +0x1fd0: movw    $0x0,0x100(%rsp)
    +0x1fda: lea     0xc0(%rsp),%rax
    +0x1fe2: mov     $0xc,%eax
    +0x1fe7: movabs  $0x380200100000000,%rbx
    +0x1ff1: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x2000: movdqa  0x1f0(%rsp,%rax,4),%xmm0
    +0x2009: movdqa  0x200(%rsp,%rax,4),%xmm1
    +0x2012: movdqa  0x210(%rsp,%rax,4),%xmm2
    +0x201b: movdqa  0x220(%rsp,%rax,4),%xmm3
    +0x2024: paddd   0x6f0(%rsp,%rax,4),%xmm0
    +0x202d: paddd   0x700(%rsp,%rax,4),%xmm1
    +0x2036: movdqa  %xmm0,0x6f0(%rsp,%rax,4)
    +0x203f: movdqa  %xmm1,0x700(%rsp,%rax,4)
    +0x2048: paddd   0x710(%rsp,%rax,4),%xmm2
    +0x2051: paddd   0x720(%rsp,%rax,4),%xmm3
    +0x205a: movdqa  %xmm2,0x710(%rsp,%rax,4)
    +0x2063: movdqa  %xmm3,0x720(%rsp,%rax,4)
    +0x206c: add     $0x10,%rax
    +0x2070: cmp     $0x10c,%rax
    +0x2076: jne     <mldsa65_signature_internal+0x2000>
    +0x2078: mov     $0x4,%eax
    +0x207d: movdqa  0x1521b(%rip),%xmm6
    +0x2085: movdqa  0x15223(%rip),%xmm7
    +0x208d: nopl    (%rax)
    +0x2090: movdqa  0x710(%rsp,%rax,4),%xmm0
    +0x2099: movdqa  0x720(%rsp,%rax,4),%xmm1
    +0x20a2: movdqa  %xmm0,%xmm2
    +0x20a6: paddd   %xmm6,%xmm2
    +0x20aa: movdqa  %xmm1,%xmm3
    +0x20ae: paddd   %xmm6,%xmm3
    +0x20b2: psrad   $0x17,%xmm2
    +0x20b7: psrad   $0x17,%xmm3
    +0x20bc: pshufd  $0xf5,%xmm2,%xmm4
    +0x20c1: pmuludq %xmm7,%xmm2
    +0x20c5: pshufd  $0xe8,%xmm2,%xmm2
    +0x20ca: pmuludq %xmm7,%xmm4
    +0x20ce: pshufd  $0xe8,%xmm4,%xmm4
    +0x20d3: punpckldq %xmm4,%xmm2
    +0x20d7: pshufd  $0xf5,%xmm3,%xmm4
    +0x20dc: pmuludq %xmm7,%xmm3
    +0x20e0: pshufd  $0xe8,%xmm3,%xmm3
    +0x20e5: pmuludq %xmm7,%xmm4
    +0x20e9: pshufd  $0xe8,%xmm4,%xmm4
    +0x20ee: punpckldq %xmm4,%xmm3
    +0x20f2: paddd   %xmm0,%xmm2
    +0x20f6: paddd   %xmm1,%xmm3
    +0x20fa: movdqa  %xmm2,0x710(%rsp,%rax,4)
    +0x2103: movdqa  %xmm3,0x720(%rsp,%rax,4)
    +0x210c: add     $0x8,%rax
    +0x2110: cmp     $0x104,%rax
    +0x2116: jne     <mldsa65_signature_internal+0x2090>
    +0x211c: xor     %eax,%eax
    +0x211e: xor     %ecx,%ecx
    +0x2120: movslq  0x720(%rsp,%rcx,4),%rdx
    +0x2128: mov     %edx,%esi
    +0x212a: neg     %esi
    +0x212c: mov     %rdx,%rdi
    +0x212f: shr     $0x1f,%rdi
    +0x2133: xor     %edx,%esi
    +0x2135: and     %edi,%esi
    +0x2137: xor     %edx,%esi
    +0x2139: mov     $0x7ff3b,%edx
    +0x213e: sub     %esi,%edx
    +0x2140: movslq  %edx,%rdx
    +0x2143: shr     $0x1f,%rdx
    +0x2147: or      %edx,%eax
    +0x2149: inc     %rcx
    +0x214c: cmp     $0x100,%rcx
    +0x2153: jne     <mldsa65_signature_internal+0x2120>
    +0x2155: xor     %r15d,%r15d
    +0x2158: test    %eax,%eax
    +0x215a: jne     <mldsa65_signature_internal+0x2db0>
    +0x2160: mov     0x18(%rsp),%r8
    +0x2165: mov     %r8,%rax
    +0x2168: xor     %ecx,%ecx
    +0x216a: nopw    0x0(%rax,%rax,1)
    +0x2170: mov     $0x80000,%edx
    +0x2175: sub     0x720(%rsp,%rcx,8),%edx
    +0x217c: mov     $0x80000,%esi
    +0x2181: sub     0x724(%rsp,%rcx,8),%esi
    +0x2188: mov     %dx,-0x3(%rax)
    +0x218c: shr     $0x10,%edx
    +0x218f: mov     %esi,%edi
    +0x2191: shl     $0x4,%edi
    +0x2194: or      %edx,%edi
    +0x2196: mov     %dil,-0x1(%rax)
    +0x219a: shr     $0x4,%esi
    +0x219d: mov     %si,(%rax)
    +0x21a0: inc     %rcx
    +0x21a3: add     $0x5,%rax
    +0x21a7: cmp     $0x80,%rcx
    +0x21ae: jne     <mldsa65_signature_internal+0x2170>
    +0x21b0: movdqa  %xmm5,0x1240(%rsp)
    +0x21b9: mov     0xb8(%rsp),%r15
    +0x21c1: inc     %r15
    +0x21c4: mov     0xa0(%rsp),%rcx
    +0x21cc: sub     $0xffffffffffffff80,%rcx
    +0x21d0: add     $0x280,%r8
    +0x21d7: cmp     $0x5,%r15
    +0x21db: jne     <mldsa65_signature_internal+0x1bd0>
    +0x21e1: mov     $0xc,%r14d
    +0x21e7: lea     0x1500(%rsp),%r13
    +0x21ef: xor     %r15d,%r15d
    +0x21f2: xor     %r12d,%r12d
    +0x21f5: data16  cs nopw 0x0(%rax,%rax,1)
    +0x2200: mov     0x20(%rsp),%rax
    +0x2205: add     %r15,%rax
    +0x2208: xor     %ecx,%ecx
    +0x220a: nopw    0x0(%rax,%rax,1)
    +0x2210: movzbl  (%rax,%rcx,1),%edx
    +0x2214: and     $0xf,%edx
    +0x2217: mov     %edx,0x220(%rsp,%rcx,8)
    +0x221e: movzbl  (%rax,%rcx,1),%esi
    +0x2222: shr     $0x4,%esi
    +0x2225: mov     $0x4,%edi
    +0x222a: sub     %edx,%edi
    +0x222c: mov     %edi,0x220(%rsp,%rcx,8)
    +0x2233: mov     $0x4,%edx
    +0x2238: sub     %esi,%edx
    +0x223a: mov     %edx,0x224(%rsp,%rcx,8)
    +0x2241: inc     %rcx
    +0x2244: cmp     $0x80,%rcx
    +0x224b: jne     <mldsa65_signature_internal+0x2210>
    +0x224d: lea     0x220(%rsp),%rdi
    +0x2255: call    <mldsa_poly_ntt>
    +0x225a: mov     $0x1,%eax
    +0x225f: nop     
    +0x2260: movslq  0x21c(%rsp,%rax,4),%rcx
    +0x2268: movslq  0x2cfc(%rsp,%rax,4),%rdx
    +0x2270: imul    %rcx,%rdx
    +0x2274: mov     %rdx,%rcx
    +0x2277: imul    %rbx,%rcx
    +0x227b: sar     $0x20,%rcx
    +0x227f: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x2286: add     %rdx,%rcx
    +0x2289: shr     $0x20,%rcx
    +0x228d: mov     %ecx,0x21c(%rsp,%rax,4)
    +0x2294: movslq  0x220(%rsp,%rax,4),%rcx
    +0x229c: movslq  0x2d00(%rsp,%rax,4),%rdx
    +0x22a4: imul    %rcx,%rdx
    +0x22a8: mov     %rdx,%rcx
    +0x22ab: imul    %rbx,%rcx
    +0x22af: sar     $0x20,%rcx
    +0x22b3: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x22ba: add     %rdx,%rcx
    +0x22bd: shr     $0x20,%rcx
    +0x22c1: mov     %ecx,0x220(%rsp,%rax,4)
    +0x22c8: add     $0x2,%rax
    +0x22cc: cmp     $0x101,%rax
    +0x22d2: jne     <mldsa65_signature_internal+0x2260>
    +0x22d4: lea     0x220(%rsp),%rdi
    +0x22dc: call    <mldsa_poly_invntt_tomont>
    +0x22e1: mov     $0xc,%eax
    +0x22e6: cs      nopw 0x0(%rax,%rax,1)
    +0x22f0: movdqa  -0x30(%r13,%rax,4),%xmm0
    +0x22f7: movdqa  -0x20(%r13,%rax,4),%xmm1
    +0x22fe: movdqa  -0x10(%r13,%rax,4),%xmm2
    +0x2305: movdqa  0x0(%r13,%rax,4),%xmm3
    +0x230c: psubd   0x1f0(%rsp,%rax,4),%xmm0
    +0x2315: psubd   0x200(%rsp,%rax,4),%xmm1
    +0x231e: movdqa  %xmm0,-0x30(%r13,%rax,4)
    +0x2325: movdqa  %xmm1,-0x20(%r13,%rax,4)
    +0x232c: psubd   0x210(%rsp,%rax,4),%xmm2
    +0x2335: psubd   0x220(%rsp,%rax,4),%xmm3
    +0x233e: movdqa  %xmm2,-0x10(%r13,%rax,4)
    +0x2345: movdqa  %xmm3,0x0(%r13,%rax,4)
    +0x234c: add     $0x10,%rax
    +0x2350: cmp     $0x10c,%rax
    +0x2356: jne     <mldsa65_signature_internal+0x22f0>
    +0x2358: mov     $0x4,%eax
    +0x235d: movdqa  0x14f3b(%rip),%xmm5
    +0x2365: movdqa  0x14f43(%rip),%xmm6
    +0x236d: nopl    (%rax)
    +0x2370: movdqa  -0x10(%r13,%rax,4),%xmm0
    +0x2377: movdqa  0x0(%r13,%rax,4),%xmm1
    +0x237e: movdqa  %xmm0,%xmm2
    +0x2382: paddd   %xmm5,%xmm2
    +0x2386: movdqa  %xmm1,%xmm3
    +0x238a: paddd   %xmm5,%xmm3
    +0x238e: psrad   $0x17,%xmm2
    +0x2393: psrad   $0x17,%xmm3
    +0x2398: pshufd  $0xf5,%xmm2,%xmm4
    +0x239d: pmuludq %xmm6,%xmm2
    +0x23a1: pshufd  $0xe8,%xmm2,%xmm2
    +0x23a6: pmuludq %xmm6,%xmm4
    +0x23aa: pshufd  $0xe8,%xmm4,%xmm4
    +0x23af: punpckldq %xmm4,%xmm2
    +0x23b3: pshufd  $0xf5,%xmm3,%xmm4
    +0x23b8: pmuludq %xmm6,%xmm3
    +0x23bc: pshufd  $0xe8,%xmm3,%xmm3
    +0x23c1: pmuludq %xmm6,%xmm4
    +0x23c5: pshufd  $0xe8,%xmm4,%xmm4
    +0x23ca: punpckldq %xmm4,%xmm3
    +0x23ce: paddd   %xmm0,%xmm2
    +0x23d2: paddd   %xmm1,%xmm3
    +0x23d6: movdqa  %xmm2,-0x10(%r13,%rax,4)
    +0x23dd: movdqa  %xmm3,0x0(%r13,%rax,4)
    +0x23e4: add     $0x8,%rax
    +0x23e8: cmp     $0x104,%rax
    +0x23ee: jne     <mldsa65_signature_internal+0x2370>
    +0x23f0: xor     %eax,%eax
    +0x23f2: xor     %ecx,%ecx
    +0x23f4: data16  data16 cs nopw 0x0(%rax,%rax,1)
    +0x2400: movslq  0x0(%r13,%rcx,4),%rdx
    +0x2405: mov     %edx,%esi
    +0x2407: neg     %esi
    +0x2409: mov     %rdx,%rdi
    +0x240c: shr     $0x1f,%rdi
    +0x2410: xor     %edx,%esi
    +0x2412: and     %edi,%esi
    +0x2414: xor     %edx,%esi
    +0x2416: mov     $0x3fe3b,%edx
    +0x241b: sub     %esi,%edx
    +0x241d: movslq  %edx,%rdx
    +0x2420: shr     $0x1f,%rdx
    +0x2424: or      %edx,%eax
    +0x2426: inc     %rcx
    +0x2429: cmp     $0x100,%rcx
    +0x2430: jne     <mldsa65_signature_internal+0x2400>
    +0x2432: test    %eax,%eax
    +0x2434: jne     <mldsa65_signature_internal+0x2990>
    +0x243a: mov     %r12,0xa0(%rsp)
    +0x2442: mov     %r15,0x18(%rsp)
    +0x2447: mov     0x40(%rsp),%rax
    +0x244c: add     %r14,%rax
    +0x244f: mov     $0x1c,%ecx
    +0x2454: data16  data16 cs nopw 0x0(%rax,%rax,1)
    +0x2460: movzbl  -0xc(%rax),%esi
    +0x2464: mov     %esi,0x204(%rsp,%rcx,1)
    +0x246b: movzbl  -0xb(%rax),%edx
    +0x246f: and     $0x1f,%edx
    +0x2472: shl     $0x8,%edx
    +0x2475: or      %esi,%edx
    +0x2477: mov     %edx,0x204(%rsp,%rcx,1)
    +0x247e: movzbl  -0xb(%rax),%esi
    +0x2482: shr     $0x5,%esi
    +0x2485: mov     %esi,0x208(%rsp,%rcx,1)
    +0x248c: movzbl  -0xa(%rax),%edi
    +0x2490: lea     (%rsi,%rdi,8),%edi
    +0x2493: mov     %edi,0x208(%rsp,%rcx,1)
    +0x249a: movzbl  -0x9(%rax),%esi
    +0x249e: and     $0x3,%esi
    +0x24a1: shl     $0xb,%esi
    +0x24a4: or      %edi,%esi
    +0x24a6: mov     %esi,0x208(%rsp,%rcx,1)
    +0x24ad: movzbl  -0x9(%rax),%r8d
    +0x24b2: shr     $0x2,%r8d
    +0x24b6: mov     %r8d,0x20c(%rsp,%rcx,1)
    +0x24be: movzbl  -0x8(%rax),%edi
    +0x24c2: and     $0x7f,%edi
    +0x24c5: shl     $0x6,%edi
    +0x24c8: or      %r8d,%edi
    +0x24cb: mov     %edi,0x20c(%rsp,%rcx,1)
    +0x24d2: movzbl  -0x8(%rax),%r8d
    +0x24d7: shr     $0x7,%r8d
    +0x24db: mov     %r8d,0x210(%rsp,%rcx,1)
    +0x24e3: movzbl  -0x7(%rax),%r9d
    +0x24e8: lea     (%r8,%r9,2),%r9d
    +0x24ec: mov     %r9d,0x210(%rsp,%rcx,1)
    +0x24f4: movzbl  -0x6(%rax),%r8d
    +0x24f9: and     $0xf,%r8d
    +0x24fd: shl     $0x9,%r8d
    +0x2501: or      %r9d,%r8d
    +0x2504: mov     %r8d,0x210(%rsp,%rcx,1)
    +0x250c: movzbl  -0x6(%rax),%r9d
    +0x2511: shr     $0x4,%r9d
    +0x2515: mov     %r9d,0x214(%rsp,%rcx,1)
    +0x251d: movzbl  -0x5(%rax),%r10d
    +0x2522: shl     $0x4,%r10d
    +0x2526: or      %r9d,%r10d
    +0x2529: mov     %r10d,0x214(%rsp,%rcx,1)
    +0x2531: movzbl  -0x4(%rax),%r9d
    +0x2536: and     $0x1,%r9d
    +0x253a: shl     $0xc,%r9d
    +0x253e: or      %r10d,%r9d
    +0x2541: mov     %r9d,0x214(%rsp,%rcx,1)
    +0x2549: movzbl  -0x4(%rax),%r11d
    +0x254e: shr     $1,%r11d
    +0x2551: mov     %r11d,0x218(%rsp,%rcx,1)
    +0x2559: movzbl  -0x3(%rax),%r10d
    +0x255e: and     $0x3f,%r10d
    +0x2562: shl     $0x7,%r10d
    +0x2566: or      %r11d,%r10d
    +0x2569: mov     %r10d,0x218(%rsp,%rcx,1)
    +0x2571: movzbl  -0x3(%rax),%r11d
    +0x2576: shr     $0x6,%r11d
    +0x257a: mov     %r11d,0x21c(%rsp,%rcx,1)
    +0x2582: movzbl  -0x2(%rax),%r15d
    +0x2587: lea     (%r11,%r15,4),%r15d
    +0x258b: mov     %r15d,0x21c(%rsp,%rcx,1)
    +0x2593: movzbl  -0x1(%rax),%r11d
    +0x2598: and     $0x7,%r11d
    +0x259c: shl     $0xa,%r11d
    +0x25a0: or      %r15d,%r11d
    +0x25a3: mov     %r11d,0x21c(%rsp,%rcx,1)
    +0x25ab: movzbl  -0x1(%rax),%r15d
    +0x25b0: shr     $0x3,%r15d
    +0x25b4: mov     %r15d,0x220(%rsp,%rcx,1)
    +0x25bc: movzbl  (%rax),%r12d
    +0x25c0: shl     $0x5,%r12d
    +0x25c4: mov     $0x1000,%ebx
    +0x25c9: sub     %edx,%ebx
    +0x25cb: mov     %ebx,0x204(%rsp,%rcx,1)
    +0x25d2: mov     $0x1000,%edx
    +0x25d7: sub     %esi,%edx
    +0x25d9: mov     %edx,0x208(%rsp,%rcx,1)
    +0x25e0: mov     $0x1000,%edx
    +0x25e5: sub     %edi,%edx
    +0x25e7: mov     %edx,0x20c(%rsp,%rcx,1)
    +0x25ee: mov     $0x1000,%edx
    +0x25f3: sub     %r8d,%edx
    +0x25f6: mov     %edx,0x210(%rsp,%rcx,1)
    +0x25fd: mov     $0x1000,%edx
    +0x2602: sub     %r9d,%edx
    +0x2605: mov     %edx,0x214(%rsp,%rcx,1)
    +0x260c: mov     $0x1000,%edx
    +0x2611: sub     %r10d,%edx
    +0x2614: mov     %edx,0x218(%rsp,%rcx,1)
    +0x261b: mov     $0x1000,%edx
    +0x2620: sub     %r11d,%edx
    +0x2623: mov     %edx,0x21c(%rsp,%rcx,1)
    +0x262a: or      %r15d,%r12d
    +0x262d: mov     $0x1000,%edx
    +0x2632: sub     %r12d,%edx
    +0x2635: mov     %edx,0x220(%rsp,%rcx,1)
    +0x263c: add     $0x20,%rcx
    +0x2640: add     $0xd,%rax
    +0x2644: cmp     $0x41c,%rcx
    +0x264b: jne     <mldsa65_signature_internal+0x2460>
    +0x2651: lea     0x220(%rsp),%rdi
    +0x2659: call    <mldsa_poly_ntt>
    +0x265e: mov     $0x1,%eax
    +0x2663: movabs  $0x380200100000000,%rbx
    +0x266d: nopl    (%rax)
    +0x2670: movslq  0x21c(%rsp,%rax,4),%rcx
    +0x2678: movslq  0x2cfc(%rsp,%rax,4),%rdx
    +0x2680: imul    %rcx,%rdx
    +0x2684: mov     %rdx,%rcx
    +0x2687: imul    %rbx,%rcx
    +0x268b: sar     $0x20,%rcx
    +0x268f: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x2696: add     %rdx,%rcx
    +0x2699: shr     $0x20,%rcx
    +0x269d: mov     %ecx,0x21c(%rsp,%rax,4)
    +0x26a4: movslq  0x220(%rsp,%rax,4),%rcx
    +0x26ac: movslq  0x2d00(%rsp,%rax,4),%rdx
    +0x26b4: imul    %rcx,%rdx
    +0x26b8: mov     %rdx,%rcx
    +0x26bb: imul    %rbx,%rcx
    +0x26bf: sar     $0x20,%rcx
    +0x26c3: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x26ca: add     %rdx,%rcx
    +0x26cd: shr     $0x20,%rcx
    +0x26d1: mov     %ecx,0x220(%rsp,%rax,4)
    +0x26d8: add     $0x2,%rax
    +0x26dc: cmp     $0x101,%rax
    +0x26e2: jne     <mldsa65_signature_internal+0x2670>
    +0x26e4: lea     0x220(%rsp),%rdi
    +0x26ec: call    <mldsa_poly_invntt_tomont>
    +0x26f1: xor     %eax,%eax
    +0x26f3: movdqa  0x14ba5(%rip),%xmm5
    +0x26fb: movdqa  0x14bad(%rip),%xmm6
    +0x2703: mov     0x18(%rsp),%r15
    +0x2708: mov     0xa0(%rsp),%r12
    +0x2710: movdqa  0x220(%rsp,%rax,4),%xmm0
    +0x2719: movdqa  0x230(%rsp,%rax,4),%xmm1
    +0x2722: movdqa  %xmm0,%xmm2
    +0x2726: paddd   %xmm5,%xmm2
    +0x272a: movdqa  %xmm1,%xmm3
    +0x272e: paddd   %xmm5,%xmm3
    +0x2732: psrad   $0x17,%xmm2
    +0x2737: psrad   $0x17,%xmm3
    +0x273c: pshufd  $0xf5,%xmm2,%xmm4
    +0x2741: pmuludq %xmm6,%xmm2
    +0x2745: pshufd  $0xe8,%xmm2,%xmm2
    +0x274a: pmuludq %xmm6,%xmm4
    +0x274e: pshufd  $0xe8,%xmm4,%xmm4
    +0x2753: punpckldq %xmm4,%xmm2
    +0x2757: pshufd  $0xf5,%xmm3,%xmm4
    +0x275c: pmuludq %xmm6,%xmm3
    +0x2760: pshufd  $0xe8,%xmm3,%xmm3
    +0x2765: pmuludq %xmm6,%xmm4
    +0x2769: pshufd  $0xe8,%xmm4,%xmm4
    +0x276e: punpckldq %xmm4,%xmm3
    +0x2772: paddd   %xmm0,%xmm2
    +0x2776: paddd   %xmm1,%xmm3
    +0x277a: movdqa  %xmm2,0x220(%rsp,%rax,4)
    +0x2783: movdqa  %xmm3,0x230(%rsp,%rax,4)
    +0x278c: add     $0x8,%rax
    +0x2790: cmp     $0x100,%rax
    +0x2796: jne     <mldsa65_signature_internal+0x2710>
    +0x279c: xor     %eax,%eax
    +0x279e: xor     %ecx,%ecx
    +0x27a0: pxor    %xmm4,%xmm4
    +0x27a4: data16  data16 cs nopw 0x0(%rax,%rax,1)
    +0x27b0: movslq  0x220(%rsp,%rcx,4),%rdx
    +0x27b8: mov     %edx,%esi
    +0x27ba: neg     %esi
    +0x27bc: mov     %rdx,%rdi
    +0x27bf: shr     $0x1f,%rdi
    +0x27c3: xor     %edx,%esi
    +0x27c5: and     %edi,%esi
    +0x27c7: xor     %edx,%esi
    +0x27c9: mov     $0x3feff,%edx
    +0x27ce: sub     %esi,%edx
    +0x27d0: movslq  %edx,%rdx
    +0x27d3: shr     $0x1f,%rdx
    +0x27d7: or      %edx,%eax
    +0x27d9: inc     %rcx
    +0x27dc: cmp     $0x100,%rcx
    +0x27e3: jne     <mldsa65_signature_internal+0x27b0>
    +0x27e5: test    %eax,%eax
    +0x27e7: movdqa  0x14d91(%rip),%xmm5
    +0x27ef: jne     <mldsa65_signature_internal+0x2990>
    +0x27f5: mov     $0xc,%eax
    +0x27fa: nopw    0x0(%rax,%rax,1)
    +0x2800: movdqa  0x1f0(%rsp,%rax,4),%xmm0
    +0x2809: movdqa  0x200(%rsp,%rax,4),%xmm1
    +0x2812: paddd   -0x30(%r13,%rax,4),%xmm0
    +0x2819: paddd   -0x20(%r13,%rax,4),%xmm1
    +0x2820: movdqa  %xmm0,-0x30(%r13,%rax,4)
    +0x2827: movdqa  %xmm1,-0x20(%r13,%rax,4)
    +0x282e: movdqa  0x210(%rsp,%rax,4),%xmm0
    +0x2837: movdqa  0x220(%rsp,%rax,4),%xmm1
    +0x2840: paddd   -0x10(%r13,%rax,4),%xmm0
    +0x2847: paddd   0x0(%r13,%rax,4),%xmm1
    +0x284e: movdqa  %xmm0,-0x10(%r13,%rax,4)
    +0x2855: movdqa  %xmm1,0x0(%r13,%rax,4)
    +0x285c: add     $0x10,%rax
    +0x2860: cmp     $0x10c,%rax
    +0x2866: jne     <mldsa65_signature_internal+0x2800>
    +0x2868: inc     %r12
    +0x286b: sub     $0xffffffffffffff80,%r15
    +0x286f: add     $0x400,%r13
    +0x2876: add     $0x1a0,%r14
    +0x287d: cmp     $0x6,%r12
    +0x2881: jne     <mldsa65_signature_internal+0x2200>
    +0x2887: movaps  0x1e0(%rsp),%xmm0
    +0x288f: movaps  0x1f0(%rsp),%xmm1
    +0x2897: movaps  0x200(%rsp),%xmm2
    +0x289f: mov     0x8(%rsp),%rax
    +0x28a4: movups  %xmm2,0x20(%rax)
    +0x28a8: movups  %xmm1,0x10(%rax)
    +0x28ac: movups  %xmm0,(%rax)
    +0x28af: mov     0x10(%rsp),%rax
    +0x28b4: movdqu  %xmm4,0x2d(%rax)
    +0x28b9: movdqu  %xmm4,0x20(%rax)
    +0x28be: movdqu  %xmm4,0x10(%rax)
    +0x28c3: movdqu  %xmm4,(%rax)
    +0x28c7: xor     %eax,%eax
    +0x28c9: nopl    0x0(%rax)
    +0x28d0: movd    0xb20(%rsp,%rax,1),%xmm0
    +0x28d9: movzwl  0xb22(%rsp,%rax,1),%ecx
    +0x28e1: movd    %ecx,%xmm1
    +0x28e5: movdqa  %xmm0,%xmm2
    +0x28e9: psrlw   $0x4,%xmm2
    +0x28ee: movdqa  %xmm1,%xmm3
    +0x28f2: psrlw   $0x4,%xmm3
    +0x28f7: punpcklbw %xmm2,%xmm0
    +0x28fb: pand    %xmm5,%xmm0
    +0x28ff: punpcklbw %xmm4,%xmm0
    +0x2903: punpcklwd %xmm4,%xmm0
    +0x2907: movdqa  %xmm0,0x220(%rsp,%rax,8)
    +0x2910: punpcklbw %xmm3,%xmm1
    +0x2914: pand    %xmm5,%xmm1
    +0x2918: punpcklbw %xmm4,%xmm1
    +0x291c: punpcklwd %xmm4,%xmm1
    +0x2920: movdqa  %xmm1,0x230(%rsp,%rax,8)
    +0x2929: add     $0x4,%rax
    +0x292d: cmp     $0x80,%rax
    +0x2933: jne     <mldsa65_signature_internal+0x28d0>
    +0x2935: xor     %eax,%eax
    +0x2937: xor     %ecx,%ecx
    +0x2939: xor     %r15d,%r15d
    +0x293c: jmp     <mldsa65_signature_internal+0x294c>
    +0x293e: xchg    %ax,%ax
    +0x2940: inc     %rcx
    +0x2943: cmp     $0x100,%rcx
    +0x294a: je      <mldsa65_signature_internal+0x299a>
    +0x294c: mov     0x1500(%rsp,%rcx,4),%edi
    +0x2953: sub     $0xfffc0100,%edi
    +0x2959: setne   %dl
    +0x295c: cmpl    $0x0,0x220(%rsp,%rcx,4)
    +0x2964: sete    %sil
    +0x2968: cmp     $0x7fe00,%edi
    +0x296e: ja      <mldsa65_signature_internal+0x2975>
    +0x2970: or      %sil,%dl
    +0x2973: jne     <mldsa65_signature_internal+0x2940>
    +0x2975: cmp     $0x37,%eax
    +0x2978: je      <mldsa65_signature_internal+0x2db0>
    +0x297e: mov     %eax,%edx
    +0x2980: mov     0x10(%rsp),%rsi
    +0x2985: mov     %cl,(%rsi,%rdx,1)
    +0x2988: inc     %eax
    +0x298a: jmp     <mldsa65_signature_internal+0x2940>
    +0x298c: nopl    0x0(%rax)
    +0x2990: xor     %ebx,%ebx
    +0x2992: xor     %r15d,%r15d
    +0x2995: jmp     <mldsa65_signature_internal+0x2db2>
    +0x299a: mov     0x8(%rsp),%rcx
    +0x299f: mov     %al,0xce7(%rcx)
    +0x29a5: xor     %ecx,%ecx
    +0x29a7: nopw    0x0(%rax,%rax,1)
    +0x29b0: movd    0xba0(%rsp,%rcx,1),%xmm0
    +0x29b9: movzwl  0xba2(%rsp,%rcx,1),%edx
    +0x29c1: movd    %edx,%xmm1
    +0x29c5: movdqa  %xmm0,%xmm2
    +0x29c9: psrlw   $0x4,%xmm2
    +0x29ce: movdqa  %xmm1,%xmm3
    +0x29d2: psrlw   $0x4,%xmm3
    +0x29d7: punpcklbw %xmm2,%xmm0
    +0x29db: pand    %xmm5,%xmm0
    +0x29df: punpcklbw %xmm4,%xmm0
    +0x29e3: punpcklwd %xmm4,%xmm0
    +0x29e7: movdqa  %xmm0,0x220(%rsp,%rcx,8)
    +0x29f0: punpcklbw %xmm3,%xmm1
    +0x29f4: pand    %xmm5,%xmm1
    +0x29f8: punpcklbw %xmm4,%xmm1
    +0x29fc: punpcklwd %xmm4,%xmm1
    +0x2a00: movdqa  %xmm1,0x230(%rsp,%rcx,8)
    +0x2a09: add     $0x4,%rcx
    +0x2a0d: cmp     $0x80,%rcx
    +0x2a14: jne     <mldsa65_signature_internal+0x29b0>
    +0x2a16: xor     %ecx,%ecx
    +0x2a18: jmp     <mldsa65_signature_internal+0x2a41>
    +0x2a1a: nopw    0x0(%rax,%rax,1)
    +0x2a20: cmp     $0x37,%eax
    +0x2a23: je      <mldsa65_signature_internal+0x2db0>
    +0x2a29: mov     %eax,%edx
    +0x2a2b: mov     0x10(%rsp),%rsi
    +0x2a30: mov     %cl,(%rsi,%rdx,1)
    +0x2a33: inc     %eax
    +0x2a35: inc     %rcx
    +0x2a38: cmp     $0x100,%rcx
    +0x2a3f: je      <mldsa65_signature_internal+0x2a6c>
    +0x2a41: mov     0x1900(%rsp,%rcx,4),%edi
    +0x2a48: sub     $0xfffc0100,%edi
    +0x2a4e: setne   %dl
    +0x2a51: cmpl    $0x0,0x220(%rsp,%rcx,4)
    +0x2a59: sete    %sil
    +0x2a5d: cmp     $0x7fe00,%edi
    +0x2a63: ja      <mldsa65_signature_internal+0x2a20>
    +0x2a65: or      %sil,%dl
    +0x2a68: jne     <mldsa65_signature_internal+0x2a35>
    +0x2a6a: jmp     <mldsa65_signature_internal+0x2a20>
    +0x2a6c: mov     0x8(%rsp),%rcx
    +0x2a71: mov     %al,0xce8(%rcx)
    +0x2a77: xor     %ecx,%ecx
    +0x2a79: nopl    0x0(%rax)
    +0x2a80: movd    0xc20(%rsp,%rcx,1),%xmm0
    +0x2a89: movzwl  0xc22(%rsp,%rcx,1),%edx
    +0x2a91: movd    %edx,%xmm1
    +0x2a95: movdqa  %xmm0,%xmm2
    +0x2a99: psrlw   $0x4,%xmm2
    +0x2a9e: movdqa  %xmm1,%xmm3
    +0x2aa2: psrlw   $0x4,%xmm3
    +0x2aa7: punpcklbw %xmm2,%xmm0
    +0x2aab: pand    %xmm5,%xmm0
    +0x2aaf: punpcklbw %xmm4,%xmm0
    +0x2ab3: punpcklwd %xmm4,%xmm0
    +0x2ab7: movdqa  %xmm0,0x220(%rsp,%rcx,8)
    +0x2ac0: punpcklbw %xmm3,%xmm1
    +0x2ac4: pand    %xmm5,%xmm1
    +0x2ac8: punpcklbw %xmm4,%xmm1
    +0x2acc: punpcklwd %xmm4,%xmm1
    +0x2ad0: movdqa  %xmm1,0x230(%rsp,%rcx,8)
    +0x2ad9: add     $0x4,%rcx
    +0x2add: cmp     $0x80,%rcx
    +0x2ae4: jne     <mldsa65_signature_internal+0x2a80>
    +0x2ae6: xor     %ecx,%ecx
    +0x2ae8: jmp     <mldsa65_signature_internal+0x2afc>
    +0x2aea: nopw    0x0(%rax,%rax,1)
    +0x2af0: inc     %rcx
    +0x2af3: cmp     $0x100,%rcx
    +0x2afa: je      <mldsa65_signature_internal+0x2b3c>
    +0x2afc: mov     0x1d00(%rsp,%rcx,4),%edi
    +0x2b03: sub     $0xfffc0100,%edi
    +0x2b09: setne   %dl
    +0x2b0c: cmpl    $0x0,0x220(%rsp,%rcx,4)
    +0x2b14: sete    %sil
    +0x2b18: cmp     $0x7fe00,%edi
    +0x2b1e: ja      <mldsa65_signature_internal+0x2b25>
    +0x2b20: or      %sil,%dl
    +0x2b23: jne     <mldsa65_signature_internal+0x2af0>
    +0x2b25: cmp     $0x37,%eax
    +0x2b28: je      <mldsa65_signature_internal+0x2db0>
    +0x2b2e: mov     %eax,%edx
    +0x2b30: mov     0x10(%rsp),%rsi
    +0x2b35: mov     %cl,(%rsi,%rdx,1)
    +0x2b38: inc     %eax
    +0x2b3a: jmp     <mldsa65_signature_internal+0x2af0>
    +0x2b3c: mov     0x8(%rsp),%rcx
    +0x2b41: mov     %al,0xce9(%rcx)
    +0x2b47: xor     %ecx,%ecx
    +0x2b49: nopl    0x0(%rax)
    +0x2b50: movd    0xca0(%rsp,%rcx,1),%xmm0
    +0x2b59: movzwl  0xca2(%rsp,%rcx,1),%edx
    +0x2b61: movd    %edx,%xmm1
    +0x2b65: movdqa  %xmm0,%xmm2
    +0x2b69: psrlw   $0x4,%xmm2
    +0x2b6e: movdqa  %xmm1,%xmm3
    +0x2b72: psrlw   $0x4,%xmm3
    +0x2b77: punpcklbw %xmm2,%xmm0
    +0x2b7b: pand    %xmm5,%xmm0
    +0x2b7f: punpcklbw %xmm4,%xmm0
    +0x2b83: punpcklwd %xmm4,%xmm0
    +0x2b87: movdqa  %xmm0,0x220(%rsp,%rcx,8)
    +0x2b90: punpcklbw %xmm3,%xmm1
    +0x2b94: pand    %xmm5,%xmm1
    +0x2b98: punpcklbw %xmm4,%xmm1
    +0x2b9c: punpcklwd %xmm4,%xmm1
    +0x2ba0: movdqa  %xmm1,0x230(%rsp,%rcx,8)
    +0x2ba9: add     $0x4,%rcx
    +0x2bad: cmp     $0x80,%rcx
    +0x2bb4: jne     <mldsa65_signature_internal+0x2b50>
    +0x2bb6: xor     %ecx,%ecx
    +0x2bb8: jmp     <mldsa65_signature_internal+0x2be1>
    +0x2bba: nopw    0x0(%rax,%rax,1)
    +0x2bc0: cmp     $0x37,%eax
    +0x2bc3: je      <mldsa65_signature_internal+0x2db0>
    +0x2bc9: mov     %eax,%edx
    +0x2bcb: mov     0x10(%rsp),%rsi
    +0x2bd0: mov     %cl,(%rsi,%rdx,1)
    +0x2bd3: inc     %eax
    +0x2bd5: inc     %rcx
    +0x2bd8: cmp     $0x100,%rcx
    +0x2bdf: je      <mldsa65_signature_internal+0x2c0c>
    +0x2be1: mov     0x2100(%rsp,%rcx,4),%edi
    +0x2be8: sub     $0xfffc0100,%edi
    +0x2bee: setne   %dl
    +0x2bf1: cmpl    $0x0,0x220(%rsp,%rcx,4)
    +0x2bf9: sete    %sil
    +0x2bfd: cmp     $0x7fe00,%edi
    +0x2c03: ja      <mldsa65_signature_internal+0x2bc0>
    +0x2c05: or      %sil,%dl
    +0x2c08: jne     <mldsa65_signature_internal+0x2bd5>
    +0x2c0a: jmp     <mldsa65_signature_internal+0x2bc0>
    +0x2c0c: mov     0x8(%rsp),%rcx
    +0x2c11: mov     %al,0xcea(%rcx)
    +0x2c17: xor     %ecx,%ecx
    +0x2c19: nopl    0x0(%rax)
    +0x2c20: movd    0xd20(%rsp,%rcx,1),%xmm0
    +0x2c29: movzwl  0xd22(%rsp,%rcx,1),%edx
    +0x2c31: movd    %edx,%xmm1
    +0x2c35: movdqa  %xmm0,%xmm2
    +0x2c39: psrlw   $0x4,%xmm2
    +0x2c3e: movdqa  %xmm1,%xmm3
    +0x2c42: psrlw   $0x4,%xmm3
    +0x2c47: punpcklbw %xmm2,%xmm0
    +0x2c4b: pand    %xmm5,%xmm0
    +0x2c4f: punpcklbw %xmm4,%xmm0
    +0x2c53: punpcklwd %xmm4,%xmm0
    +0x2c57: movdqa  %xmm0,0x220(%rsp,%rcx,8)
    +0x2c60: punpcklbw %xmm3,%xmm1
    +0x2c64: pand    %xmm5,%xmm1
    +0x2c68: punpcklbw %xmm4,%xmm1
    +0x2c6c: punpcklwd %xmm4,%xmm1
    +0x2c70: movdqa  %xmm1,0x230(%rsp,%rcx,8)
    +0x2c79: add     $0x4,%rcx
    +0x2c7d: cmp     $0x80,%rcx
    +0x2c84: jne     <mldsa65_signature_internal+0x2c20>
    +0x2c86: xor     %ecx,%ecx
    +0x2c88: jmp     <mldsa65_signature_internal+0x2c9c>
    +0x2c8a: nopw    0x0(%rax,%rax,1)
    +0x2c90: inc     %rcx
    +0x2c93: cmp     $0x100,%rcx
    +0x2c9a: je      <mldsa65_signature_internal+0x2cdc>
    +0x2c9c: mov     0x2500(%rsp,%rcx,4),%edi
    +0x2ca3: sub     $0xfffc0100,%edi
    +0x2ca9: setne   %dl
    +0x2cac: cmpl    $0x0,0x220(%rsp,%rcx,4)
    +0x2cb4: sete    %sil
    +0x2cb8: cmp     $0x7fe00,%edi
    +0x2cbe: ja      <mldsa65_signature_internal+0x2cc5>
    +0x2cc0: or      %sil,%dl
    +0x2cc3: jne     <mldsa65_signature_internal+0x2c90>
    +0x2cc5: cmp     $0x37,%eax
    +0x2cc8: je      <mldsa65_signature_internal+0x2db0>
    +0x2cce: mov     %eax,%edx
    +0x2cd0: mov     0x10(%rsp),%rsi
    +0x2cd5: mov     %cl,(%rsi,%rdx,1)
    +0x2cd8: inc     %eax
    +0x2cda: jmp     <mldsa65_signature_internal+0x2c90>
    +0x2cdc: mov     0x8(%rsp),%rcx
    +0x2ce1: mov     %al,0xceb(%rcx)
    +0x2ce7: xor     %ecx,%ecx
    +0x2ce9: nopl    0x0(%rax)
    +0x2cf0: movd    0xda0(%rsp,%rcx,1),%xmm0
    +0x2cf9: movzwl  0xda2(%rsp,%rcx,1),%edx
    +0x2d01: movd    %edx,%xmm1
    +0x2d05: movdqa  %xmm0,%xmm2
    +0x2d09: psrlw   $0x4,%xmm2
    +0x2d0e: movdqa  %xmm1,%xmm3
    +0x2d12: psrlw   $0x4,%xmm3
    +0x2d17: punpcklbw %xmm2,%xmm0
    +0x2d1b: pand    %xmm5,%xmm0
    +0x2d1f: punpcklbw %xmm4,%xmm0
    +0x2d23: punpcklwd %xmm4,%xmm0
    +0x2d27: movdqa  %xmm0,0x220(%rsp,%rcx,8)
    +0x2d30: punpcklbw %xmm3,%xmm1
    +0x2d34: pand    %xmm5,%xmm1
    +0x2d38: punpcklbw %xmm4,%xmm1
    +0x2d3c: punpcklwd %xmm4,%xmm1
    +0x2d40: movdqa  %xmm1,0x230(%rsp,%rcx,8)
    +0x2d49: add     $0x4,%rcx
    +0x2d4d: cmp     $0x80,%rcx
    +0x2d54: jne     <mldsa65_signature_internal+0x2cf0>
    +0x2d56: xor     %ecx,%ecx
    +0x2d58: jmp     <mldsa65_signature_internal+0x2d70>
    +0x2d5a: nopw    0x0(%rax,%rax,1)
    +0x2d60: inc     %rcx
    +0x2d63: cmp     $0x100,%rcx
    +0x2d6a: je      <mldsa65_signature_internal+0x2e7b>
    +0x2d70: mov     0x2900(%rsp,%rcx,4),%edi
    +0x2d77: sub     $0xfffc0100,%edi
    +0x2d7d: setne   %dl
    +0x2d80: cmpl    $0x0,0x220(%rsp,%rcx,4)
    +0x2d88: sete    %sil
    +0x2d8c: cmp     $0x7fe00,%edi
    +0x2d92: ja      <mldsa65_signature_internal+0x2d99>
    +0x2d94: or      %sil,%dl
    +0x2d97: jne     <mldsa65_signature_internal+0x2d60>
    +0x2d99: cmp     $0x37,%eax
    +0x2d9c: je      <mldsa65_signature_internal+0x2db0>
    +0x2d9e: mov     %eax,%edx
    +0x2da0: mov     0x10(%rsp),%rsi
    +0x2da5: mov     %cl,(%rsi,%rdx,1)
    +0x2da8: inc     %eax
    +0x2daa: jmp     <mldsa65_signature_internal+0x2d60>
    +0x2dac: nopl    0x0(%rax)
    +0x2db0: xor     %ebx,%ebx
    +0x2db2: mov     $0x400,%edx
    +0x2db7: lea     0x720(%rsp),%r14
    +0x2dbf: mov     %r14,%rdi
    +0x2dc2: xor     %esi,%esi
    +0x2dc4: call    <memset>
    +0x2dc9: mov     $0x400,%edx
    +0x2dce: lea     0x2d00(%rsp),%r14
    +0x2dd6: mov     %r14,%rdi
    +0x2dd9: xor     %esi,%esi
    +0x2ddb: call    <memset>
    +0x2de0: mov     $0x1800,%edx
    +0x2de5: lea     0x1500(%rsp),%r14
    +0x2ded: mov     %r14,%rdi
    +0x2df0: xor     %esi,%esi
    +0x2df2: call    <memset>
    +0x2df7: mov     $0x300,%edx
    +0x2dfc: lea     0xb20(%rsp),%r14
    +0x2e04: mov     %r14,%rdi
    +0x2e07: xor     %esi,%esi
    +0x2e09: call    <memset>
    +0x2e0e: mov     $0x400,%edx
    +0x2e13: lea     0x220(%rsp),%r14
    +0x2e1b: mov     %r14,%rdi
    +0x2e1e: xor     %esi,%esi
    +0x2e20: call    <memset>
    +0x2e25: pxor    %xmm4,%xmm4
    +0x2e29: movdqa  %xmm4,0x80(%rsp)
    +0x2e32: lea     0x80(%rsp),%rax
    +0x2e3a: movdqa  %xmm4,0x200(%rsp)
    +0x2e43: movdqa  %xmm4,0x1f0(%rsp)
    +0x2e4c: movdqa  %xmm4,0x1e0(%rsp)
    +0x2e55: lea     0x1e0(%rsp),%rax
    +0x2e5d: test    %bl,%bl
    +0x2e5f: jne     <mldsa65_signature_internal+0x2ea7>
    +0x2e61: mov     0xb0(%rsp),%rcx
    +0x2e69: inc     %ecx
    +0x2e6b: movzwl  %cx,%eax
    +0x2e6e: cmp     $0x3332,%eax
    +0x2e73: jne     <mldsa65_signature_internal+0x1c0>
    +0x2e79: jmp     <mldsa65_signature_internal+0x2e8d>
    +0x2e7b: mov     0x8(%rsp),%rcx
    +0x2e80: mov     %al,0xcec(%rcx)
    +0x2e86: mov     $0x1,%bl
    +0x2e88: jmp     <mldsa65_signature_internal+0x2db2>
    +0x2e8d: mov     $0xced,%edx
    +0x2e92: mov     0x8(%rsp),%rbx
    +0x2e97: mov     %rbx,%rdi
    +0x2e9a: xor     %esi,%esi
    +0x2e9c: call    <memset>
    +0x2ea1: mov     $0xfffffffc,%r15d
    +0x2ea7: movq    $0x0,0x20(%rsp)
    +0x2eb0: lea     0x20(%rsp),%rax
    +0x2eb5: movq    $0x0,0x40(%rsp)
    +0x2ebe: lea     0x40(%rsp),%rax
    +0x2ec3: movq    $0x0,0x60(%rsp)
    +0x2ecc: lea     0x60(%rsp),%rax
    +0x2ed1: lea     0xe20(%rsp),%rbx
    +0x2ed9: mov     $0x420,%edx
    +0x2ede: mov     %rbx,%rdi
    +0x2ee1: xor     %esi,%esi
    +0x2ee3: call    <memset>
    +0x2ee8: pxor    %xmm0,%xmm0
    +0x2eec: movdqa  %xmm0,0x710(%rsp)
    +0x2ef5: movdqa  %xmm0,0x700(%rsp)
    +0x2efe: movdqa  %xmm0,0x6f0(%rsp)
    +0x2f07: movdqa  %xmm0,0x6e0(%rsp)
    +0x2f10: movdqa  %xmm0,0x6d0(%rsp)
    +0x2f19: movdqa  %xmm0,0x6c0(%rsp)
    +0x2f22: movdqa  %xmm0,0x6b0(%rsp)
    +0x2f2b: movdqa  %xmm0,0x6a0(%rsp)
    +0x2f34: movdqa  %xmm0,0x690(%rsp)
    +0x2f3d: movdqa  %xmm0,0x680(%rsp)
    +0x2f46: movdqa  %xmm0,0x670(%rsp)
    +0x2f4f: movdqa  %xmm0,0x660(%rsp)
    +0x2f58: movdqa  %xmm0,0x650(%rsp)
    +0x2f61: movdqa  %xmm0,0x640(%rsp)
    +0x2f6a: movdqa  %xmm0,0x630(%rsp)
    +0x2f73: movdqa  %xmm0,0x620(%rsp)
    +0x2f7c: lea     0x620(%rsp),%rax
    +0x2f84: mov     %r15d,%eax
    +0x2f87: lea     -0x28(%rbp),%rsp
    +0x2f8b: pop     %rbx
    +0x2f8c: pop     %r12
    +0x2f8e: pop     %r13
    +0x2f90: pop     %r14
    +0x2f92: pop     %r15
    +0x2f94: pop     %rbp
    +0x2f95: xor     %ecx,%ecx
    +0x2f97: xor     %edi,%edi
    +0x2f99: xor     %edx,%edx
    +0x2f9b: xor     %esi,%esi
    +0x2f9d: xor     %r8d,%r8d
    +0x2fa0: xor     %r9d,%r9d
    +0x2fa3: xor     %r10d,%r10d
    +0x2fa6: xor     %r11d,%r11d
    +0x2fa9: ret     
 ***)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa65_signature_internal";
    layout_range "plt_memcpy";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* secret key skb at sk (4032 bytes), the message M of mlen bytes at m and   *)
(* the prefix PRE of prelen bytes at pre (or, if ext is nonzero as a 32-bit  *)
(* integer, mu in the first 64 bytes at m), and the 32 bytes RND at rnd,     *)
(* with MU the mu that the code uses: the result is 0, with the signature    *)
(* mld_sign_sig_65 at sig (3309 bytes), if one of the 16382 attempts         *)
(* succeeds (mld_sign_ok_65), and -4 with the signature zeroed otherwise.    *)
(* The last two arguments, sk and ext, are on the stack above the return     *)
(* address, sk as a 64-bit word and ext as a 32-bit one. The function aligns *)
(* the stack pointer down to a multiple of 32, which may lower it by up to   *)
(* 31 bytes, saves RBP, the frame pointer, and five more registers, and      *)
(* reserves its buffers, below which the callees use theirs: 14126 bytes of  *)
(* stack below the return address in all (the figure of stackx.py, which     *)
(* counts the red zone that mldsa_keccakf1600_permute writes below RSP). The *)
(* GOT entries of memset and memcpy, which the PLT stubs read, and the       *)
(* region (ea,el) that they may read are apart from the signature and the    *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
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
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          mld_sign_terminates_65 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 14126),14126)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 14126),14126)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,3309) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa65_signature_internal) /\
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
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mld_sign_ok_65 skb MU RND
                     then word 0 else word 4294967292) /\
                    (!t. t < 3309
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             mld_sign_sig_65 skb MU RND t))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 14126),14126)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

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

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
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
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          mld_sign_terminates_65 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 14126),14126)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 14126),14126)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,3309) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa65_signature_internal) /\
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
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mld_sign_ok_65 skb MU RND
                     then word 0 else word 4294967292) /\
                    (!t. t < 3309
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             mld_sign_sig_65 skb MU RND t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen rnd sk ext
                             (mld_sk_rho skb)
                             (mld_sign_declass_65 skb MU RND)
                             mf mc pc (word_sub stackpointer (word 14126))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; rnd,32; sk,4032;
                         word_sub stackpointer (word 14126),14126;
                         stackpointer,8; word_add stackpointer (word 8),16;
                         word(pc + got_memset),8;
                          word(pc + got_memcpy),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa65_poly_challenge_consts),48;
                          word(pc + mldsa65_signature_internal_consts),784;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448]
                        [sig,3309;
                         word_sub stackpointer (word 14126),14126]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 14126),14126)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
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
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          mld_sign_terminates_65 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 14126),14126)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 14126),14126)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,3309) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa65_signature_internal) /\
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
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen rnd sk ext
                             (mld_sk_rho skb)
                             (mld_sign_declass_65 skb MU RND)
                             mf mc pc (word_sub stackpointer (word 14126))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; rnd,32; sk,4032;
                         word_sub stackpointer (word 14126),14126;
                         stackpointer,8; word_add stackpointer (word 8),16;
                         word(pc + got_memset),8;
                          word(pc + got_memcpy),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa65_poly_challenge_consts),48;
                          word(pc + mldsa65_signature_internal_consts),784;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448]
                        [sig,3309;
                         word_sub stackpointer (word 14126),14126]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 14126),14126)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
