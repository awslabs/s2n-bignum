(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing: the statement. This is the code for mldsa44_signature_internal   *)
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
(* still calls mld_H44, mldsa44_poly_challenge, mldsa_poly_uniform,          *)
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
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/H_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_challenge_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_signature_internal:
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
      +0x2f: sub     $0x940,%rsp
      +0x36: mov     %r9,%rbx
      +0x39: mov     %r8,%r9
      +0x3c: mov     %rcx,%r8
      +0x3f: mov     %rdx,%r10
      +0x42: mov     %rsi,%rax
      +0x45: mov     %rdi,0x8(%rsp)
      +0x4a: mov     0x10(%rbp),%rcx
      +0x4e: lea     0x280(%rsp),%r14
      +0x56: lea     0x2a0(%rsp),%r11
      +0x5e: movups  (%rcx),%xmm0
      +0x61: movups  0x10(%rcx),%xmm1
      +0x65: movaps  %xmm1,0x230(%rsp)
      +0x6d: movaps  %xmm0,0x220(%rsp)
      +0x75: movups  0x20(%rcx),%xmm0
      +0x79: movups  0x30(%rcx),%xmm1
      +0x7d: movaps  %xmm0,0x280(%rsp)
      +0x85: movaps  %xmm1,0x290(%rsp)
      +0x8d: movups  0x40(%rcx),%xmm0
      +0x91: movups  0x50(%rcx),%xmm1
      +0x95: movdqu  0x60(%rcx),%xmm2
      +0x9a: movdqu  0x70(%rcx),%xmm3
      +0x9f: movdqa  %xmm2,0x260(%rsp)
      +0xa8: movaps  %xmm1,0x250(%rsp)
      +0xb0: movaps  %xmm0,0x240(%rsp)
      +0xb8: movdqa  %xmm3,0x270(%rsp)
      +0xc1: lea     0x80(%rcx),%rdx
      +0xc8: mov     %rdx,0x60(%rsp)
      +0xcd: lea     0x200(%rcx),%rdx
      +0xd4: mov     %rdx,0x20(%rsp)
      +0xd9: add     $0x380,%rcx
      +0xe0: mov     %rcx,0x40(%rsp)
      +0xe5: cmpl    $0x0,0x18(%rbp)
      +0xe9: je      <mldsa44_signature_internal+0x113>
      +0xeb: movups  (%rax),%xmm0
      +0xee: movups  0x10(%rax),%xmm1
      +0xf2: movdqu  0x20(%rax),%xmm2
      +0xf7: movdqu  0x30(%rax),%xmm3
      +0xfc: movdqa  %xmm3,0x30(%r11)
     +0x102: movdqa  %xmm2,0x20(%r11)
     +0x108: movaps  %xmm1,0x10(%r11)
     +0x10d: movaps  %xmm0,(%r11)
     +0x111: jmp     <mldsa44_signature_internal+0x13c>
     +0x113: lea     0x240(%rsp),%rdx
     +0x11b: mov     $0x40,%esi
     +0x120: mov     $0x40,%ecx
     +0x125: mov     %r11,%rdi
     +0x128: push    %r10
     +0x12a: push    %rax
     +0x12b: call    <mld_H44>
     +0x130: lea     0x2b0(%rsp),%r11
     +0x138: add     $0x10,%rsp
     +0x13c: mov     $0x40,%esi
     +0x141: mov     $0x20,%ecx
     +0x146: mov     $0x20,%r9d
     +0x14c: lea     0x2e0(%rsp),%rdi
     +0x154: mov     %r14,%rdx
     +0x157: mov     %rbx,%r8
     +0x15a: push    $0x40
     +0x15c: push    %r11
     +0x15e: call    <mld_H44>
     +0x163: add     $0x10,%rsp
     +0x167: movdqa  0x220(%rsp),%xmm0
     +0x170: movdqa  0x230(%rsp),%xmm1
     +0x179: movdqa  %xmm1,0x14f0(%rsp)
     +0x182: movdqa  %xmm0,0x14e0(%rsp)
     +0x18b: mov     0x8(%rsp),%rax
     +0x190: lea     0x920(%rax),%rcx
     +0x197: mov     %rcx,0x18(%rsp)
     +0x19c: add     $0x27,%rax
     +0x1a0: mov     %rax,0x188(%rsp)
     +0x1a8: xor     %ecx,%ecx
     +0x1aa: nopw    0x0(%rax,%rax,1)
     +0x1b0: mov     %rcx,0x190(%rsp)
     +0x1b8: lea     0x0(,%rcx,4),%eax
     +0x1bf: lea     0x2e0(%rsp),%rcx
     +0x1c7: mov     %rcx,0x80(%rsp)
     +0x1cf: mov     %ax,0x88(%rsp)
     +0x1d7: lea     0x14e0(%rsp),%rax
     +0x1df: movaps  (%rax),%xmm0
     +0x1e2: movaps  0x10(%rax),%xmm1
     +0x1e6: movaps  %xmm1,0xb0(%rsp)
     +0x1ee: movaps  %xmm0,0xa0(%rsp)
     +0x1f6: xor     %r14d,%r14d
     +0x1f9: jmp     <mldsa44_signature_internal+0x20d>
     +0x1fb: nopl    0x0(%rax,%rax,1)
     +0x200: inc     %r14d
     +0x203: cmp     $0x4,%r14d
     +0x207: je      <mldsa44_signature_internal+0xd00>
     +0x20d: mov     0x80(%rsp),%rax
     +0x215: movzwl  0x88(%rsp),%ecx
     +0x21d: mov     %r14d,0x10(%rsp)
     +0x222: add     %r14w,%cx
     +0x226: movups  (%rax),%xmm0
     +0x229: movups  0x10(%rax),%xmm1
     +0x22d: movups  0x20(%rax),%xmm2
     +0x231: movups  0x30(%rax),%xmm3
     +0x235: movaps  %xmm0,0xa20(%rsp)
     +0x23d: movaps  %xmm1,0xa30(%rsp)
     +0x245: movaps  %xmm2,0xa40(%rsp)
     +0x24d: movaps  %xmm3,0xa50(%rsp)
     +0x255: mov     %cx,0xa60(%rsp)
     +0x25d: xorps   %xmm0,%xmm0
     +0x260: movaps  %xmm0,0x720(%rsp)
     +0x268: movaps  %xmm0,0x730(%rsp)
     +0x270: movaps  %xmm0,0x740(%rsp)
     +0x278: movaps  %xmm0,0x750(%rsp)
     +0x280: movaps  %xmm0,0x760(%rsp)
     +0x288: movaps  %xmm0,0x770(%rsp)
     +0x290: movaps  %xmm0,0x780(%rsp)
     +0x298: movaps  %xmm0,0x790(%rsp)
     +0x2a0: movaps  %xmm0,0x7a0(%rsp)
     +0x2a8: movaps  %xmm0,0x7b0(%rsp)
     +0x2b0: movaps  %xmm0,0x7c0(%rsp)
     +0x2b8: movaps  %xmm0,0x7d0(%rsp)
     +0x2c0: movups  %xmm0,0x7dc(%rsp)
     +0x2c8: movdqa  0xa20(%rsp),%xmm0
     +0x2d1: movdqa  0x730(%rsp),%xmm1
     +0x2da: movdqa  0x740(%rsp),%xmm2
     +0x2e3: movdqa  0x750(%rsp),%xmm3
     +0x2ec: pxor    0xa30(%rsp),%xmm1
     +0x2f5: movdqa  0x760(%rsp),%xmm4
     +0x2fe: movdqa  %xmm0,0x720(%rsp)
     +0x307: pxor    0xa40(%rsp),%xmm2
     +0x310: movdqa  %xmm1,0x730(%rsp)
     +0x319: pxor    0xa50(%rsp),%xmm3
     +0x322: movdqa  %xmm2,0x740(%rsp)
     +0x32b: movdqa  %xmm3,0x750(%rsp)
     +0x334: pxor    0xa60(%rsp),%xmm4
     +0x33d: movd    %xmm4,%eax
     +0x341: mov     %ax,0x760(%rsp)
     +0x349: xorb    $0x1f,0x762(%rsp)
     +0x351: xorb    $0x80,0x7a7(%rsp)
     +0x359: movl    $0x88,0x7e8(%rsp)
     +0x364: mov     $0x88,%r13d
     +0x36a: mov     $0x2a8,%r14d
     +0x370: xor     %r15d,%r15d
     +0x373: jmp     <mldsa44_signature_internal+0x3bb>
     +0x375: data16  cs nopw 0x0(%rax,%rax,1)
     +0x380: mov     $0x88,%ebx
     +0x385: sub     %r13d,%ebx
     +0x388: cmp     %rbx,%r14
     +0x38b: cmovb   %r14,%rbx
     +0x38f: mov     %r13d,%eax
     +0x392: lea     (%rsp,%rax,1),%rsi
     +0x396: add     $0x720,%rsi
     +0x39d: lea     (%rsp,%r15,1),%rdi
     +0x3a1: add     $0x2500,%rdi
     +0x3a8: mov     %rbx,%rdx
     +0x3ab: call    <memcpy>
     +0x3b0: add     %ebx,%r13d
     +0x3b3: add     %rbx,%r15
     +0x3b6: sub     %rbx,%r14
     +0x3b9: je      <mldsa44_signature_internal+0x3f0>
     +0x3bb: cmp     $0x88,%r13d
     +0x3c2: jne     <mldsa44_signature_internal+0x380>
     +0x3c4: lea     0x720(%rsp),%r12
     +0x3cc: mov     %r12,%rdi
     +0x3cf: call    <mldsa_keccakf1600_permute>
     +0x3d4: cmp     $0x88,%r14
     +0x3db: mov     $0x88,%ebx
     +0x3e0: cmovb   %r14,%rbx
     +0x3e4: xor     %r13d,%r13d
     +0x3e7: mov     %r12,%rsi
     +0x3ea: jmp     <mldsa44_signature_internal+0x39d>
     +0x3ec: nopl    0x0(%rax)
     +0x3f0: mov     $0x8,%eax
     +0x3f5: lea     0x32c(%rsp),%rcx
     +0x3fd: nopl    (%rax)
     +0x400: movzwl  0x24f8(%rsp,%rax,1),%esi
     +0x408: movzbl  0x24fa(%rsp,%rax,1),%edi
     +0x410: mov     %edi,%edx
     +0x412: and     $0x3,%edx
     +0x415: shl     $0x10,%edx
     +0x418: or      %esi,%edx
     +0x41a: shr     $0x2,%edi
     +0x41d: movzbl  0x24fb(%rsp,%rax,1),%r8d
     +0x426: shl     $0x6,%r8d
     +0x42a: or      %edi,%r8d
     +0x42d: movzbl  0x24fc(%rsp,%rax,1),%edi
     +0x435: mov     %edi,%esi
     +0x437: and     $0xf,%esi
     +0x43a: shl     $0xe,%esi
     +0x43d: or      %r8d,%esi
     +0x440: shr     $0x4,%edi
     +0x443: movzbl  0x24fd(%rsp,%rax,1),%r8d
     +0x44c: shl     $0x4,%r8d
     +0x450: or      %edi,%r8d
     +0x453: movzbl  0x24fe(%rsp,%rax,1),%edi
     +0x45b: mov     %edi,%r9d
     +0x45e: and     $0x3f,%r9d
     +0x462: shl     $0xc,%r9d
     +0x466: or      %r8d,%r9d
     +0x469: shr     $0x6,%edi
     +0x46c: movzbl  0x24ff(%rsp,%rax,1),%r8d
     +0x475: lea     (%rdi,%r8,4),%edi
     +0x479: movzbl  0x2500(%rsp,%rax,1),%r8d
     +0x482: shl     $0xa,%r8d
     +0x486: or      %edi,%r8d
     +0x489: mov     $0x20000,%edi
     +0x48e: sub     %edx,%edi
     +0x490: mov     %edi,-0xc(%rcx)
     +0x493: mov     $0x20000,%edx
     +0x498: sub     %esi,%edx
     +0x49a: mov     %edx,-0x8(%rcx)
     +0x49d: mov     $0x20000,%edx
     +0x4a2: sub     %r9d,%edx
     +0x4a5: mov     %edx,-0x4(%rcx)
     +0x4a8: mov     $0x20000,%edx
     +0x4ad: sub     %r8d,%edx
     +0x4b0: mov     %edx,(%rcx)
     +0x4b2: add     $0x9,%rax
     +0x4b6: add     $0x10,%rcx
     +0x4ba: cmp     $0x248,%rax
     +0x4c0: jne     <mldsa44_signature_internal+0x400>
     +0x4c6: pxor    %xmm0,%xmm0
     +0x4ca: movdqa  %xmm0,0x7e0(%rsp)
     +0x4d3: movdqa  %xmm0,0x7d0(%rsp)
     +0x4dc: movdqa  %xmm0,0x7c0(%rsp)
     +0x4e5: movdqa  %xmm0,0x7b0(%rsp)
     +0x4ee: movdqa  %xmm0,0x7a0(%rsp)
     +0x4f7: movdqa  %xmm0,0x790(%rsp)
     +0x500: movdqa  %xmm0,0x780(%rsp)
     +0x509: movdqa  %xmm0,0x770(%rsp)
     +0x512: movdqa  %xmm0,0x760(%rsp)
     +0x51b: movdqa  %xmm0,0x750(%rsp)
     +0x524: movdqa  %xmm0,0x740(%rsp)
     +0x52d: movdqa  %xmm0,0x730(%rsp)
     +0x536: movdqa  %xmm0,0x720(%rsp)
     +0x53f: lea     0x720(%rsp),%rax
     +0x547: mov     $0x2a8,%edx
     +0x54c: lea     0x2500(%rsp),%rbx
     +0x554: mov     %rbx,%rdi
     +0x557: xor     %esi,%esi
     +0x559: call    <memset>
     +0x55e: pxor    %xmm0,%xmm0
     +0x562: movdqa  %xmm0,0xa50(%rsp)
     +0x56b: movdqa  %xmm0,0xa40(%rsp)
     +0x574: movdqa  %xmm0,0xa30(%rsp)
     +0x57d: movdqa  %xmm0,0xa20(%rsp)
     +0x586: movw    $0x0,0xa60(%rsp)
     +0x590: lea     0xa20(%rsp),%rax
     +0x598: lea     0x320(%rsp),%rdi
     +0x5a0: call    <mldsa_poly_ntt>
     +0x5a5: mov     0x10(%rsp),%r14d
     +0x5aa: test    %r14d,%r14d
     +0x5ad: movabs  $0x380200100000000,%r12
     +0x5b7: je      <mldsa44_signature_internal+0xa60>
     +0x5bd: mov     %r14b,0xc0(%rsp)
     +0x5c5: movb    $0x0,0xc1(%rsp)
     +0x5cd: lea     0x10e0(%rsp),%rbx
     +0x5d5: mov     %rbx,%rdi
     +0x5d8: lea     0xa0(%rsp),%rsi
     +0x5e0: call    <mldsa_poly_uniform>
     +0x5e5: mov     $0x1,%eax
     +0x5ea: nopw    0x0(%rax,%rax,1)
     +0x5f0: movslq  0x10dc(%rsp,%rax,4),%rcx
     +0x5f8: movslq  0x31c(%rsp,%rax,4),%rdx
     +0x600: imul    %rcx,%rdx
     +0x604: mov     %rdx,%rcx
     +0x607: imul    %r12,%rcx
     +0x60b: sar     $0x20,%rcx
     +0x60f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x616: add     %rdx,%rcx
     +0x619: shr     $0x20,%rcx
     +0x61d: mov     %ecx,0x10dc(%rsp,%rax,4)
     +0x624: movslq  0x10e0(%rsp,%rax,4),%rcx
     +0x62c: movslq  0x320(%rsp,%rax,4),%rdx
     +0x634: imul    %rcx,%rdx
     +0x638: mov     %rdx,%rcx
     +0x63b: imul    %r12,%rcx
     +0x63f: sar     $0x20,%rcx
     +0x643: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x64a: add     %rdx,%rcx
     +0x64d: shr     $0x20,%rcx
     +0x651: mov     %ecx,0x10e0(%rsp,%rax,4)
     +0x658: add     $0x2,%rax
     +0x65c: cmp     $0x101,%rax
     +0x662: jne     <mldsa44_signature_internal+0x5f0>
     +0x664: mov     $0xc,%eax
     +0x669: nopl    0x0(%rax)
     +0x670: movdqa  0x10b0(%rsp,%rax,4),%xmm0
     +0x679: movdqa  0x10c0(%rsp,%rax,4),%xmm1
     +0x682: movdqa  0x10d0(%rsp,%rax,4),%xmm2
     +0x68b: movdqa  0x10e0(%rsp,%rax,4),%xmm3
     +0x694: paddd   0x14d0(%rsp,%rax,4),%xmm0
     +0x69d: paddd   0x14e0(%rsp,%rax,4),%xmm1
     +0x6a6: movdqa  %xmm0,0x14d0(%rsp,%rax,4)
     +0x6af: movdqa  %xmm1,0x14e0(%rsp,%rax,4)
     +0x6b8: paddd   0x14f0(%rsp,%rax,4),%xmm2
     +0x6c1: paddd   0x1500(%rsp,%rax,4),%xmm3
     +0x6ca: movdqa  %xmm2,0x14f0(%rsp,%rax,4)
     +0x6d3: movdqa  %xmm3,0x1500(%rsp,%rax,4)
     +0x6dc: add     $0x10,%rax
     +0x6e0: cmp     $0x10c,%rax
     +0x6e6: jne     <mldsa44_signature_internal+0x670>
     +0x6e8: mov     %r14b,0xc0(%rsp)
     +0x6f0: movb    $0x1,0xc1(%rsp)
     +0x6f8: mov     %rbx,%rdi
     +0x6fb: lea     0xa0(%rsp),%rsi
     +0x703: call    <mldsa_poly_uniform>
     +0x708: mov     $0x1,%eax
     +0x70d: nopl    (%rax)
     +0x710: movslq  0x10dc(%rsp,%rax,4),%rcx
     +0x718: movslq  0x31c(%rsp,%rax,4),%rdx
     +0x720: imul    %rcx,%rdx
     +0x724: mov     %rdx,%rcx
     +0x727: imul    %r12,%rcx
     +0x72b: sar     $0x20,%rcx
     +0x72f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x736: add     %rdx,%rcx
     +0x739: shr     $0x20,%rcx
     +0x73d: mov     %ecx,0x10dc(%rsp,%rax,4)
     +0x744: movslq  0x10e0(%rsp,%rax,4),%rcx
     +0x74c: movslq  0x320(%rsp,%rax,4),%rdx
     +0x754: imul    %rcx,%rdx
     +0x758: mov     %rdx,%rcx
     +0x75b: imul    %r12,%rcx
     +0x75f: sar     $0x20,%rcx
     +0x763: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x76a: add     %rdx,%rcx
     +0x76d: shr     $0x20,%rcx
     +0x771: mov     %ecx,0x10e0(%rsp,%rax,4)
     +0x778: add     $0x2,%rax
     +0x77c: cmp     $0x101,%rax
     +0x782: jne     <mldsa44_signature_internal+0x710>
     +0x784: mov     $0xc,%eax
     +0x789: nopl    0x0(%rax)
     +0x790: movdqa  0x10b0(%rsp,%rax,4),%xmm0
     +0x799: movdqa  0x10c0(%rsp,%rax,4),%xmm1
     +0x7a2: movdqa  0x10d0(%rsp,%rax,4),%xmm2
     +0x7ab: movdqa  0x10e0(%rsp,%rax,4),%xmm3
     +0x7b4: paddd   0x18d0(%rsp,%rax,4),%xmm0
     +0x7bd: paddd   0x18e0(%rsp,%rax,4),%xmm1
     +0x7c6: movdqa  %xmm0,0x18d0(%rsp,%rax,4)
     +0x7cf: movdqa  %xmm1,0x18e0(%rsp,%rax,4)
     +0x7d8: paddd   0x18f0(%rsp,%rax,4),%xmm2
     +0x7e1: paddd   0x1900(%rsp,%rax,4),%xmm3
     +0x7ea: movdqa  %xmm2,0x18f0(%rsp,%rax,4)
     +0x7f3: movdqa  %xmm3,0x1900(%rsp,%rax,4)
     +0x7fc: add     $0x10,%rax
     +0x800: cmp     $0x10c,%rax
     +0x806: jne     <mldsa44_signature_internal+0x790>
     +0x808: mov     %r14b,0xc0(%rsp)
     +0x810: movb    $0x2,0xc1(%rsp)
     +0x818: mov     %rbx,%rdi
     +0x81b: lea     0xa0(%rsp),%rsi
     +0x823: call    <mldsa_poly_uniform>
     +0x828: mov     $0x1,%eax
     +0x82d: nopl    (%rax)
     +0x830: movslq  0x10dc(%rsp,%rax,4),%rcx
     +0x838: movslq  0x31c(%rsp,%rax,4),%rdx
     +0x840: imul    %rcx,%rdx
     +0x844: mov     %rdx,%rcx
     +0x847: imul    %r12,%rcx
     +0x84b: sar     $0x20,%rcx
     +0x84f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x856: add     %rdx,%rcx
     +0x859: shr     $0x20,%rcx
     +0x85d: mov     %ecx,0x10dc(%rsp,%rax,4)
     +0x864: movslq  0x10e0(%rsp,%rax,4),%rcx
     +0x86c: movslq  0x320(%rsp,%rax,4),%rdx
     +0x874: imul    %rcx,%rdx
     +0x878: mov     %rdx,%rcx
     +0x87b: imul    %r12,%rcx
     +0x87f: sar     $0x20,%rcx
     +0x883: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x88a: add     %rdx,%rcx
     +0x88d: shr     $0x20,%rcx
     +0x891: mov     %ecx,0x10e0(%rsp,%rax,4)
     +0x898: add     $0x2,%rax
     +0x89c: cmp     $0x101,%rax
     +0x8a2: jne     <mldsa44_signature_internal+0x830>
     +0x8a4: xor     %eax,%eax
     +0x8a6: cs      nopw 0x0(%rax,%rax,1)
     +0x8b0: movdqa  0x10e0(%rsp,%rax,4),%xmm0
     +0x8b9: movdqa  0x10f0(%rsp,%rax,4),%xmm1
     +0x8c2: movdqa  0x1100(%rsp,%rax,4),%xmm2
     +0x8cb: movdqa  0x1110(%rsp,%rax,4),%xmm3
     +0x8d4: paddd   0x1d00(%rsp,%rax,4),%xmm0
     +0x8dd: paddd   0x1d10(%rsp,%rax,4),%xmm1
     +0x8e6: movdqa  %xmm0,0x1d00(%rsp,%rax,4)
     +0x8ef: movdqa  %xmm1,0x1d10(%rsp,%rax,4)
     +0x8f8: paddd   0x1d20(%rsp,%rax,4),%xmm2
     +0x901: paddd   0x1d30(%rsp,%rax,4),%xmm3
     +0x90a: movdqa  %xmm2,0x1d20(%rsp,%rax,4)
     +0x913: movdqa  %xmm3,0x1d30(%rsp,%rax,4)
     +0x91c: add     $0x10,%rax
     +0x920: cmp     $0x100,%rax
     +0x926: jne     <mldsa44_signature_internal+0x8b0>
     +0x928: mov     %r14b,0xc0(%rsp)
     +0x930: movb    $0x3,0xc1(%rsp)
     +0x938: mov     %rbx,%rdi
     +0x93b: lea     0xa0(%rsp),%rsi
     +0x943: call    <mldsa_poly_uniform>
     +0x948: xor     %eax,%eax
     +0x94a: nopw    0x0(%rax,%rax,1)
     +0x950: movslq  0x10e0(%rsp,%rax,4),%rcx
     +0x958: movslq  0x320(%rsp,%rax,4),%rdx
     +0x960: imul    %rcx,%rdx
     +0x964: mov     %rdx,%rcx
     +0x967: imul    %r12,%rcx
     +0x96b: sar     $0x20,%rcx
     +0x96f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x976: add     %rdx,%rcx
     +0x979: shr     $0x20,%rcx
     +0x97d: mov     %ecx,0x10e0(%rsp,%rax,4)
     +0x984: movslq  0x10e4(%rsp,%rax,4),%rcx
     +0x98c: movslq  0x324(%rsp,%rax,4),%rdx
     +0x994: imul    %rcx,%rdx
     +0x998: mov     %rdx,%rcx
     +0x99b: imul    %r12,%rcx
     +0x99f: sar     $0x20,%rcx
     +0x9a3: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x9aa: add     %rdx,%rcx
     +0x9ad: shr     $0x20,%rcx
     +0x9b1: mov     %ecx,0x10e4(%rsp,%rax,4)
     +0x9b8: add     $0x2,%rax
     +0x9bc: cmp     $0x100,%rax
     +0x9c2: jne     <mldsa44_signature_internal+0x950>
     +0x9c4: xor     %eax,%eax
     +0x9c6: movdqa  0x22022(%rip),%xmm5
     +0x9ce: movdqa  0x2202a(%rip),%xmm6
     +0x9d6: cs      nopw 0x0(%rax,%rax,1)
     +0x9e0: movdqa  0x10e0(%rsp,%rax,4),%xmm0
     +0x9e9: movdqa  0x10f0(%rsp,%rax,4),%xmm1
     +0x9f2: movdqa  0x1100(%rsp,%rax,4),%xmm2
     +0x9fb: movdqa  0x1110(%rsp,%rax,4),%xmm3
     +0xa04: paddd   0x2100(%rsp,%rax,4),%xmm0
     +0xa0d: paddd   0x2110(%rsp,%rax,4),%xmm1
     +0xa16: movdqa  %xmm0,0x2100(%rsp,%rax,4)
     +0xa1f: movdqa  %xmm1,0x2110(%rsp,%rax,4)
     +0xa28: paddd   0x2120(%rsp,%rax,4),%xmm2
     +0xa31: paddd   0x2130(%rsp,%rax,4),%xmm3
     +0xa3a: movdqa  %xmm2,0x2120(%rsp,%rax,4)
     +0xa43: movdqa  %xmm3,0x2130(%rsp,%rax,4)
     +0xa4c: add     $0x10,%rax
     +0xa50: cmp     $0x100,%rax
     +0xa56: jne     <mldsa44_signature_internal+0x9e0>
     +0xa58: jmp     <mldsa44_signature_internal+0x200>
     +0xa5d: nopl    (%rax)
     +0xa60: movw    $0x0,0xc0(%rsp)
     +0xa6a: lea     0x1500(%rsp),%rdi
     +0xa72: lea     0xa0(%rsp),%rsi
     +0xa7a: call    <mldsa_poly_uniform>
     +0xa7f: xor     %eax,%eax
     +0xa81: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0xa90: movslq  0x1500(%rsp,%rax,4),%rcx
     +0xa98: movslq  0x320(%rsp,%rax,4),%rdx
     +0xaa0: imul    %rcx,%rdx
     +0xaa4: mov     %rdx,%rcx
     +0xaa7: imul    %r12,%rcx
     +0xaab: sar     $0x20,%rcx
     +0xaaf: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xab6: add     %rdx,%rcx
     +0xab9: shr     $0x20,%rcx
     +0xabd: mov     %ecx,0x1500(%rsp,%rax,4)
     +0xac4: movslq  0x1504(%rsp,%rax,4),%rcx
     +0xacc: movslq  0x324(%rsp,%rax,4),%rdx
     +0xad4: imul    %rcx,%rdx
     +0xad8: mov     %rdx,%rcx
     +0xadb: imul    %r12,%rcx
     +0xadf: sar     $0x20,%rcx
     +0xae3: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xaea: add     %rdx,%rcx
     +0xaed: shr     $0x20,%rcx
     +0xaf1: mov     %ecx,0x1504(%rsp,%rax,4)
     +0xaf8: add     $0x2,%rax
     +0xafc: cmp     $0x100,%rax
     +0xb02: jne     <mldsa44_signature_internal+0xa90>
     +0xb04: movw    $0x100,0xc0(%rsp)
     +0xb0e: lea     0x1900(%rsp),%rdi
     +0xb16: lea     0xa0(%rsp),%rsi
     +0xb1e: call    <mldsa_poly_uniform>
     +0xb23: xor     %eax,%eax
     +0xb25: data16  cs nopw 0x0(%rax,%rax,1)
     +0xb30: movslq  0x1900(%rsp,%rax,4),%rcx
     +0xb38: movslq  0x320(%rsp,%rax,4),%rdx
     +0xb40: imul    %rcx,%rdx
     +0xb44: mov     %rdx,%rcx
     +0xb47: imul    %r12,%rcx
     +0xb4b: sar     $0x20,%rcx
     +0xb4f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xb56: add     %rdx,%rcx
     +0xb59: shr     $0x20,%rcx
     +0xb5d: mov     %ecx,0x1900(%rsp,%rax,4)
     +0xb64: movslq  0x1904(%rsp,%rax,4),%rcx
     +0xb6c: movslq  0x324(%rsp,%rax,4),%rdx
     +0xb74: imul    %rcx,%rdx
     +0xb78: mov     %rdx,%rcx
     +0xb7b: imul    %r12,%rcx
     +0xb7f: sar     $0x20,%rcx
     +0xb83: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xb8a: add     %rdx,%rcx
     +0xb8d: shr     $0x20,%rcx
     +0xb91: mov     %ecx,0x1904(%rsp,%rax,4)
     +0xb98: add     $0x2,%rax
     +0xb9c: cmp     $0x100,%rax
     +0xba2: jne     <mldsa44_signature_internal+0xb30>
     +0xba4: movw    $0x200,0xc0(%rsp)
     +0xbae: lea     0x1d00(%rsp),%rdi
     +0xbb6: lea     0xa0(%rsp),%rsi
     +0xbbe: call    <mldsa_poly_uniform>
     +0xbc3: xor     %eax,%eax
     +0xbc5: data16  cs nopw 0x0(%rax,%rax,1)
     +0xbd0: movslq  0x1d00(%rsp,%rax,4),%rcx
     +0xbd8: movslq  0x320(%rsp,%rax,4),%rdx
     +0xbe0: imul    %rcx,%rdx
     +0xbe4: mov     %rdx,%rcx
     +0xbe7: imul    %r12,%rcx
     +0xbeb: sar     $0x20,%rcx
     +0xbef: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xbf6: add     %rdx,%rcx
     +0xbf9: shr     $0x20,%rcx
     +0xbfd: mov     %ecx,0x1d00(%rsp,%rax,4)
     +0xc04: movslq  0x1d04(%rsp,%rax,4),%rcx
     +0xc0c: movslq  0x324(%rsp,%rax,4),%rdx
     +0xc14: imul    %rcx,%rdx
     +0xc18: mov     %rdx,%rcx
     +0xc1b: imul    %r12,%rcx
     +0xc1f: sar     $0x20,%rcx
     +0xc23: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xc2a: add     %rdx,%rcx
     +0xc2d: shr     $0x20,%rcx
     +0xc31: mov     %ecx,0x1d04(%rsp,%rax,4)
     +0xc38: add     $0x2,%rax
     +0xc3c: cmp     $0x100,%rax
     +0xc42: jne     <mldsa44_signature_internal+0xbd0>
     +0xc44: movw    $0x300,0xc0(%rsp)
     +0xc4e: lea     0x2100(%rsp),%rdi
     +0xc56: lea     0xa0(%rsp),%rsi
     +0xc5e: call    <mldsa_poly_uniform>
     +0xc63: xor     %eax,%eax
     +0xc65: movdqa  0x21d83(%rip),%xmm5
     +0xc6d: movdqa  0x21d8b(%rip),%xmm6
     +0xc75: data16  cs nopw 0x0(%rax,%rax,1)
     +0xc80: movslq  0x2100(%rsp,%rax,4),%rcx
     +0xc88: movslq  0x320(%rsp,%rax,4),%rdx
     +0xc90: imul    %rcx,%rdx
     +0xc94: mov     %rdx,%rcx
     +0xc97: imul    %r12,%rcx
     +0xc9b: sar     $0x20,%rcx
     +0xc9f: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xca6: add     %rdx,%rcx
     +0xca9: shr     $0x20,%rcx
     +0xcad: mov     %ecx,0x2100(%rsp,%rax,4)
     +0xcb4: movslq  0x2104(%rsp,%rax,4),%rcx
     +0xcbc: movslq  0x324(%rsp,%rax,4),%rdx
     +0xcc4: imul    %rcx,%rdx
     +0xcc8: mov     %rdx,%rcx
     +0xccb: imul    %r12,%rcx
     +0xccf: sar     $0x20,%rcx
     +0xcd3: imul    $0xffffffffff801fff,%rcx,%rcx
     +0xcda: add     %rdx,%rcx
     +0xcdd: shr     $0x20,%rcx
     +0xce1: mov     %ecx,0x2104(%rsp,%rax,4)
     +0xce8: add     $0x2,%rax
     +0xcec: cmp     $0x100,%rax
     +0xcf2: jne     <mldsa44_signature_internal+0xc80>
     +0xcf4: jmp     <mldsa44_signature_internal+0x200>
     +0xcf9: nopl    0x0(%rax)
     +0xd00: pxor    %xmm0,%xmm0
     +0xd04: movdqa  %xmm0,0xd0(%rsp)
     +0xd0d: movdqa  %xmm0,0xc0(%rsp)
     +0xd16: movdqa  %xmm0,0xb0(%rsp)
     +0xd1f: movdqa  %xmm0,0xa0(%rsp)
     +0xd28: lea     0xa0(%rsp),%rax
     +0xd30: mov     $0x4,%eax
     +0xd35: data16  cs nopw 0x0(%rax,%rax,1)
     +0xd40: movdqa  0x14f0(%rsp,%rax,4),%xmm0
     +0xd49: movdqa  0x1500(%rsp,%rax,4),%xmm1
     +0xd52: movdqa  %xmm0,%xmm2
     +0xd56: paddd   %xmm5,%xmm2
     +0xd5a: movdqa  %xmm1,%xmm3
     +0xd5e: paddd   %xmm5,%xmm3
     +0xd62: psrad   $0x17,%xmm2
     +0xd67: psrad   $0x17,%xmm3
     +0xd6c: pshufd  $0xf5,%xmm2,%xmm4
     +0xd71: pmuludq %xmm6,%xmm2
     +0xd75: pshufd  $0xe8,%xmm2,%xmm2
     +0xd7a: pmuludq %xmm6,%xmm4
     +0xd7e: pshufd  $0xe8,%xmm4,%xmm4
     +0xd83: punpckldq %xmm4,%xmm2
     +0xd87: pshufd  $0xf5,%xmm3,%xmm4
     +0xd8c: pmuludq %xmm6,%xmm3
     +0xd90: pshufd  $0xe8,%xmm3,%xmm3
     +0xd95: pmuludq %xmm6,%xmm4
     +0xd99: pshufd  $0xe8,%xmm4,%xmm4
     +0xd9e: punpckldq %xmm4,%xmm3
     +0xda2: paddd   %xmm0,%xmm2
     +0xda6: paddd   %xmm1,%xmm3
     +0xdaa: movdqa  %xmm2,0x14f0(%rsp,%rax,4)
     +0xdb3: movdqa  %xmm3,0x1500(%rsp,%rax,4)
     +0xdbc: add     $0x8,%rax
     +0xdc0: cmp     $0x104,%rax
     +0xdc6: jne     <mldsa44_signature_internal+0xd40>
     +0xdcc: mov     $0x104,%eax
     +0xdd1: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0xde0: movdqa  0x14f0(%rsp,%rax,4),%xmm0
     +0xde9: movdqa  0x1500(%rsp,%rax,4),%xmm1
     +0xdf2: movdqa  %xmm0,%xmm2
     +0xdf6: paddd   %xmm5,%xmm2
     +0xdfa: movdqa  %xmm1,%xmm3
     +0xdfe: paddd   %xmm5,%xmm3
     +0xe02: psrad   $0x17,%xmm2
     +0xe07: psrad   $0x17,%xmm3
     +0xe0c: pshufd  $0xf5,%xmm2,%xmm4
     +0xe11: pmuludq %xmm6,%xmm2
     +0xe15: pshufd  $0xe8,%xmm2,%xmm2
     +0xe1a: pmuludq %xmm6,%xmm4
     +0xe1e: pshufd  $0xe8,%xmm4,%xmm4
     +0xe23: punpckldq %xmm4,%xmm2
     +0xe27: pshufd  $0xf5,%xmm3,%xmm4
     +0xe2c: pmuludq %xmm6,%xmm3
     +0xe30: pshufd  $0xe8,%xmm3,%xmm3
     +0xe35: pmuludq %xmm6,%xmm4
     +0xe39: pshufd  $0xe8,%xmm4,%xmm4
     +0xe3e: punpckldq %xmm4,%xmm3
     +0xe42: paddd   %xmm0,%xmm2
     +0xe46: paddd   %xmm1,%xmm3
     +0xe4a: movdqa  %xmm2,0x14f0(%rsp,%rax,4)
     +0xe53: movdqa  %xmm3,0x1500(%rsp,%rax,4)
     +0xe5c: add     $0x8,%rax
     +0xe60: cmp     $0x204,%rax
     +0xe66: jne     <mldsa44_signature_internal+0xde0>
     +0xe6c: mov     $0x204,%eax
     +0xe71: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0xe80: movdqa  0x14f0(%rsp,%rax,4),%xmm0
     +0xe89: movdqa  0x1500(%rsp,%rax,4),%xmm1
     +0xe92: movdqa  %xmm0,%xmm2
     +0xe96: paddd   %xmm5,%xmm2
     +0xe9a: movdqa  %xmm1,%xmm3
     +0xe9e: paddd   %xmm5,%xmm3
     +0xea2: psrad   $0x17,%xmm2
     +0xea7: psrad   $0x17,%xmm3
     +0xeac: pshufd  $0xf5,%xmm2,%xmm4
     +0xeb1: pmuludq %xmm6,%xmm2
     +0xeb5: pshufd  $0xe8,%xmm2,%xmm2
     +0xeba: pmuludq %xmm6,%xmm4
     +0xebe: pshufd  $0xe8,%xmm4,%xmm4
     +0xec3: punpckldq %xmm4,%xmm2
     +0xec7: pshufd  $0xf5,%xmm3,%xmm4
     +0xecc: pmuludq %xmm6,%xmm3
     +0xed0: pshufd  $0xe8,%xmm3,%xmm3
     +0xed5: pmuludq %xmm6,%xmm4
     +0xed9: pshufd  $0xe8,%xmm4,%xmm4
     +0xede: punpckldq %xmm4,%xmm3
     +0xee2: paddd   %xmm0,%xmm2
     +0xee6: paddd   %xmm1,%xmm3
     +0xeea: movdqa  %xmm2,0x14f0(%rsp,%rax,4)
     +0xef3: movdqa  %xmm3,0x1500(%rsp,%rax,4)
     +0xefc: add     $0x8,%rax
     +0xf00: cmp     $0x304,%rax
     +0xf06: jne     <mldsa44_signature_internal+0xe80>
     +0xf0c: mov     $0x304,%eax
     +0xf11: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0xf20: movdqa  0x14f0(%rsp,%rax,4),%xmm0
     +0xf29: movdqa  0x1500(%rsp,%rax,4),%xmm1
     +0xf32: movdqa  %xmm0,%xmm2
     +0xf36: paddd   %xmm5,%xmm2
     +0xf3a: movdqa  %xmm1,%xmm3
     +0xf3e: paddd   %xmm5,%xmm3
     +0xf42: psrad   $0x17,%xmm2
     +0xf47: psrad   $0x17,%xmm3
     +0xf4c: pshufd  $0xf5,%xmm2,%xmm4
     +0xf51: pmuludq %xmm6,%xmm2
     +0xf55: pshufd  $0xe8,%xmm2,%xmm2
     +0xf5a: pmuludq %xmm6,%xmm4
     +0xf5e: pshufd  $0xe8,%xmm4,%xmm4
     +0xf63: punpckldq %xmm4,%xmm2
     +0xf67: pshufd  $0xf5,%xmm3,%xmm4
     +0xf6c: pmuludq %xmm6,%xmm3
     +0xf70: pshufd  $0xe8,%xmm3,%xmm3
     +0xf75: pmuludq %xmm6,%xmm4
     +0xf79: pshufd  $0xe8,%xmm4,%xmm4
     +0xf7e: punpckldq %xmm4,%xmm3
     +0xf82: paddd   %xmm0,%xmm2
     +0xf86: paddd   %xmm1,%xmm3
     +0xf8a: movdqa  %xmm2,0x14f0(%rsp,%rax,4)
     +0xf93: movdqa  %xmm3,0x1500(%rsp,%rax,4)
     +0xf9c: add     $0x8,%rax
     +0xfa0: cmp     $0x404,%rax
     +0xfa6: jne     <mldsa44_signature_internal+0xf20>
     +0xfac: lea     0x1500(%rsp),%rdi
     +0xfb4: call    <mldsa_poly_invntt_tomont>
     +0xfb9: lea     0x1900(%rsp),%rdi
     +0xfc1: call    <mldsa_poly_invntt_tomont>
     +0xfc6: lea     0x1d00(%rsp),%rdi
     +0xfce: call    <mldsa_poly_invntt_tomont>
     +0xfd3: lea     0x2100(%rsp),%rdi
     +0xfdb: call    <mldsa_poly_invntt_tomont>
     +0xfe0: xor     %eax,%eax
     +0xfe2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0xff0: movslq  0x1500(%rsp,%rax,4),%rcx
     +0xff8: lea     0x7fe001(%rcx),%edx
     +0xffe: mov     %rcx,%rsi
    +0x1001: shr     $0x1f,%rsi
    +0x1005: xor     %ecx,%edx
    +0x1007: and     %esi,%edx
    +0x1009: xor     %ecx,%edx
    +0x100b: mov     %edx,0x1500(%rsp,%rax,4)
    +0x1012: inc     %rax
    +0x1015: cmp     $0x100,%rax
    +0x101b: jne     <mldsa44_signature_internal+0xff0>
    +0x101d: mov     $0x100,%eax
    +0x1022: lea     0x2a0(%rsp),%r8
    +0x102a: nopw    0x0(%rax,%rax,1)
    +0x1030: movslq  0x1500(%rsp,%rax,4),%rcx
    +0x1038: lea     0x7fe001(%rcx),%edx
    +0x103e: mov     %rcx,%rsi
    +0x1041: shr     $0x1f,%rsi
    +0x1045: xor     %ecx,%edx
    +0x1047: and     %esi,%edx
    +0x1049: xor     %ecx,%edx
    +0x104b: mov     %edx,0x1500(%rsp,%rax,4)
    +0x1052: inc     %rax
    +0x1055: cmp     $0x200,%rax
    +0x105b: jne     <mldsa44_signature_internal+0x1030>
    +0x105d: mov     $0x200,%eax
    +0x1062: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1070: movslq  0x1500(%rsp,%rax,4),%rcx
    +0x1078: lea     0x7fe001(%rcx),%edx
    +0x107e: mov     %rcx,%rsi
    +0x1081: shr     $0x1f,%rsi
    +0x1085: xor     %ecx,%edx
    +0x1087: and     %esi,%edx
    +0x1089: xor     %ecx,%edx
    +0x108b: mov     %edx,0x1500(%rsp,%rax,4)
    +0x1092: inc     %rax
    +0x1095: cmp     $0x300,%rax
    +0x109b: jne     <mldsa44_signature_internal+0x1070>
    +0x109d: mov     $0x300,%eax
    +0x10a2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x10b0: movslq  0x1500(%rsp,%rax,4),%rcx
    +0x10b8: lea     0x7fe001(%rcx),%edx
    +0x10be: mov     %rcx,%rsi
    +0x10c1: shr     $0x1f,%rsi
    +0x10c5: xor     %ecx,%edx
    +0x10c7: and     %esi,%edx
    +0x10c9: xor     %ecx,%edx
    +0x10cb: mov     %edx,0x1500(%rsp,%rax,4)
    +0x10d2: inc     %rax
    +0x10d5: cmp     $0x400,%rax
    +0x10db: jne     <mldsa44_signature_internal+0x10b0>
    +0x10dd: xor     %eax,%eax
    +0x10df: nop     
    +0x10e0: mov     0x1500(%rsp,%rax,4),%ecx
    +0x10e7: lea     0x7f(%rcx),%edx
    +0x10ea: sar     $0x7,%edx
    +0x10ed: imul    $0x2c0b,%edx,%edx
    +0x10f3: add     $0x800000,%edx
    +0x10f9: sar     $0x18,%edx
    +0x10fc: mov     %edx,0x320(%rsp,%rax,4)
    +0x1103: mov     $0x2b,%esi
    +0x1108: sub     %edx,%esi
    +0x110a: movslq  %esi,%rsi
    +0x110d: shr     $0x1f,%rsi
    +0x1111: not     %esi
    +0x1113: and     %edx,%esi
    +0x1115: mov     %esi,0x320(%rsp,%rax,4)
    +0x111c: imul    $0xfffd1800,%esi,%edx
    +0x1122: lea     (%rdx,%rcx,1),%esi
    +0x1125: mov     %esi,0x1500(%rsp,%rax,4)
    +0x112c: add     %edx,%ecx
    +0x112e: add     $0xff801fff,%ecx
    +0x1134: mov     $0x3ff000,%edx
    +0x1139: sub     %esi,%edx
    +0x113b: movslq  %edx,%rdx
    +0x113e: shr     $0x1f,%rdx
    +0x1142: xor     %esi,%ecx
    +0x1144: and     %edx,%ecx
    +0x1146: xor     %esi,%ecx
    +0x1148: mov     %ecx,0x1500(%rsp,%rax,4)
    +0x114f: inc     %rax
    +0x1152: cmp     $0x100,%rax
    +0x1158: jne     <mldsa44_signature_internal+0x10e0>
    +0x115a: mov     $0x2,%eax
    +0x115f: lea     0x32c(%rsp),%rcx
    +0x1167: nopw    0x0(%rax,%rax,1)
    +0x1170: mov     -0x8(%rcx),%edx
    +0x1173: mov     %edx,%esi
    +0x1175: shl     $0x6,%esi
    +0x1178: or      -0xc(%rcx),%esi
    +0x117b: mov     %sil,0x71e(%rsp,%rax,1)
    +0x1183: shr     $0x2,%edx
    +0x1186: mov     -0x4(%rcx),%esi
    +0x1189: mov     %esi,%edi
    +0x118b: shl     $0x4,%edi
    +0x118e: or      %edx,%edi
    +0x1190: mov     %dil,0x71f(%rsp,%rax,1)
    +0x1198: shr     $0x4,%esi
    +0x119b: mov     (%rcx),%edx
    +0x119d: shl     $0x2,%edx
    +0x11a0: or      %esi,%edx
    +0x11a2: mov     %dl,0x720(%rsp,%rax,1)
    +0x11a9: add     $0x3,%rax
    +0x11ad: add     $0x10,%rcx
    +0x11b1: cmp     $0xc2,%rax
    +0x11b7: jne     <mldsa44_signature_internal+0x1170>
    +0x11b9: mov     $0x100,%eax
    +0x11be: xchg    %ax,%ax
    +0x11c0: mov     0x1500(%rsp,%rax,4),%ecx
    +0x11c7: lea     0x7f(%rcx),%edx
    +0x11ca: sar     $0x7,%edx
    +0x11cd: imul    $0x2c0b,%edx,%edx
    +0x11d3: add     $0x800000,%edx
    +0x11d9: sar     $0x18,%edx
    +0x11dc: mov     %edx,-0xe0(%rsp,%rax,4)
    +0x11e3: mov     $0x2b,%esi
    +0x11e8: sub     %edx,%esi
    +0x11ea: movslq  %esi,%rsi
    +0x11ed: shr     $0x1f,%rsi
    +0x11f1: not     %esi
    +0x11f3: and     %edx,%esi
    +0x11f5: mov     %esi,-0xe0(%rsp,%rax,4)
    +0x11fc: imul    $0xfffd1800,%esi,%edx
    +0x1202: lea     (%rdx,%rcx,1),%esi
    +0x1205: mov     %esi,0x1500(%rsp,%rax,4)
    +0x120c: add     %edx,%ecx
    +0x120e: add     $0xff801fff,%ecx
    +0x1214: mov     $0x3ff000,%edx
    +0x1219: sub     %esi,%edx
    +0x121b: movslq  %edx,%rdx
    +0x121e: shr     $0x1f,%rdx
    +0x1222: xor     %esi,%ecx
    +0x1224: and     %edx,%ecx
    +0x1226: xor     %esi,%ecx
    +0x1228: mov     %ecx,0x1500(%rsp,%rax,4)
    +0x122f: inc     %rax
    +0x1232: cmp     $0x200,%rax
    +0x1238: jne     <mldsa44_signature_internal+0x11c0>
    +0x123a: mov     $0xc2,%eax
    +0x123f: lea     0x32c(%rsp),%rcx
    +0x1247: nopw    0x0(%rax,%rax,1)
    +0x1250: mov     -0x8(%rcx),%edx
    +0x1253: mov     %edx,%esi
    +0x1255: shl     $0x6,%esi
    +0x1258: or      -0xc(%rcx),%esi
    +0x125b: mov     %sil,0x71e(%rsp,%rax,1)
    +0x1263: shr     $0x2,%edx
    +0x1266: mov     -0x4(%rcx),%esi
    +0x1269: mov     %esi,%edi
    +0x126b: shl     $0x4,%edi
    +0x126e: or      %edx,%edi
    +0x1270: mov     %dil,0x71f(%rsp,%rax,1)
    +0x1278: shr     $0x4,%esi
    +0x127b: mov     (%rcx),%edx
    +0x127d: shl     $0x2,%edx
    +0x1280: or      %esi,%edx
    +0x1282: mov     %dl,0x720(%rsp,%rax,1)
    +0x1289: add     $0x3,%rax
    +0x128d: add     $0x10,%rcx
    +0x1291: cmp     $0x182,%rax
    +0x1297: jne     <mldsa44_signature_internal+0x1250>
    +0x1299: mov     $0x200,%eax
    +0x129e: xchg    %ax,%ax
    +0x12a0: mov     0x1500(%rsp,%rax,4),%ecx
    +0x12a7: lea     0x7f(%rcx),%edx
    +0x12aa: sar     $0x7,%edx
    +0x12ad: imul    $0x2c0b,%edx,%edx
    +0x12b3: add     $0x800000,%edx
    +0x12b9: sar     $0x18,%edx
    +0x12bc: mov     %edx,-0x4e0(%rsp,%rax,4)
    +0x12c3: mov     $0x2b,%esi
    +0x12c8: sub     %edx,%esi
    +0x12ca: movslq  %esi,%rsi
    +0x12cd: shr     $0x1f,%rsi
    +0x12d1: not     %esi
    +0x12d3: and     %edx,%esi
    +0x12d5: mov     %esi,-0x4e0(%rsp,%rax,4)
    +0x12dc: imul    $0xfffd1800,%esi,%edx
    +0x12e2: lea     (%rdx,%rcx,1),%esi
    +0x12e5: mov     %esi,0x1500(%rsp,%rax,4)
    +0x12ec: add     %edx,%ecx
    +0x12ee: add     $0xff801fff,%ecx
    +0x12f4: mov     $0x3ff000,%edx
    +0x12f9: sub     %esi,%edx
    +0x12fb: movslq  %edx,%rdx
    +0x12fe: shr     $0x1f,%rdx
    +0x1302: xor     %esi,%ecx
    +0x1304: and     %edx,%ecx
    +0x1306: xor     %esi,%ecx
    +0x1308: mov     %ecx,0x1500(%rsp,%rax,4)
    +0x130f: inc     %rax
    +0x1312: cmp     $0x300,%rax
    +0x1318: jne     <mldsa44_signature_internal+0x12a0>
    +0x131a: mov     $0x182,%eax
    +0x131f: lea     0x32c(%rsp),%rcx
    +0x1327: nopw    0x0(%rax,%rax,1)
    +0x1330: mov     -0x8(%rcx),%edx
    +0x1333: mov     %edx,%esi
    +0x1335: shl     $0x6,%esi
    +0x1338: or      -0xc(%rcx),%esi
    +0x133b: mov     %sil,0x71e(%rsp,%rax,1)
    +0x1343: shr     $0x2,%edx
    +0x1346: mov     -0x4(%rcx),%esi
    +0x1349: mov     %esi,%edi
    +0x134b: shl     $0x4,%edi
    +0x134e: or      %edx,%edi
    +0x1350: mov     %dil,0x71f(%rsp,%rax,1)
    +0x1358: shr     $0x4,%esi
    +0x135b: mov     (%rcx),%edx
    +0x135d: shl     $0x2,%edx
    +0x1360: or      %esi,%edx
    +0x1362: mov     %dl,0x720(%rsp,%rax,1)
    +0x1369: add     $0x3,%rax
    +0x136d: add     $0x10,%rcx
    +0x1371: cmp     $0x242,%rax
    +0x1377: jne     <mldsa44_signature_internal+0x1330>
    +0x1379: mov     $0x300,%eax
    +0x137e: xchg    %ax,%ax
    +0x1380: mov     0x1500(%rsp,%rax,4),%ecx
    +0x1387: lea     0x7f(%rcx),%edx
    +0x138a: sar     $0x7,%edx
    +0x138d: imul    $0x2c0b,%edx,%edx
    +0x1393: add     $0x800000,%edx
    +0x1399: sar     $0x18,%edx
    +0x139c: mov     %edx,-0x8e0(%rsp,%rax,4)
    +0x13a3: mov     $0x2b,%esi
    +0x13a8: sub     %edx,%esi
    +0x13aa: movslq  %esi,%rsi
    +0x13ad: shr     $0x1f,%rsi
    +0x13b1: not     %esi
    +0x13b3: and     %edx,%esi
    +0x13b5: mov     %esi,-0x8e0(%rsp,%rax,4)
    +0x13bc: imul    $0xfffd1800,%esi,%edx
    +0x13c2: lea     (%rdx,%rcx,1),%esi
    +0x13c5: mov     %esi,0x1500(%rsp,%rax,4)
    +0x13cc: add     %edx,%ecx
    +0x13ce: add     $0xff801fff,%ecx
    +0x13d4: mov     $0x3ff000,%edx
    +0x13d9: sub     %esi,%edx
    +0x13db: movslq  %edx,%rdx
    +0x13de: shr     $0x1f,%rdx
    +0x13e2: xor     %esi,%ecx
    +0x13e4: and     %edx,%ecx
    +0x13e6: xor     %esi,%ecx
    +0x13e8: mov     %ecx,0x1500(%rsp,%rax,4)
    +0x13ef: inc     %rax
    +0x13f2: cmp     $0x400,%rax
    +0x13f8: jne     <mldsa44_signature_internal+0x1380>
    +0x13fa: mov     $0x242,%eax
    +0x13ff: lea     0x32c(%rsp),%rcx
    +0x1407: nopw    0x0(%rax,%rax,1)
    +0x1410: mov     -0x8(%rcx),%edx
    +0x1413: mov     %edx,%esi
    +0x1415: shl     $0x6,%esi
    +0x1418: or      -0xc(%rcx),%esi
    +0x141b: mov     %sil,0x71e(%rsp,%rax,1)
    +0x1423: shr     $0x2,%edx
    +0x1426: mov     -0x4(%rcx),%esi
    +0x1429: mov     %esi,%edi
    +0x142b: shl     $0x4,%edi
    +0x142e: or      %edx,%edi
    +0x1430: mov     %dil,0x71f(%rsp,%rax,1)
    +0x1438: shr     $0x4,%esi
    +0x143b: mov     (%rcx),%edx
    +0x143d: shl     $0x2,%edx
    +0x1440: or      %esi,%edx
    +0x1442: mov     %dl,0x720(%rsp,%rax,1)
    +0x1449: add     $0x3,%rax
    +0x144d: add     $0x10,%rcx
    +0x1451: cmp     $0x302,%rax
    +0x1457: jne     <mldsa44_signature_internal+0x1410>
    +0x1459: sub     $0x10,%rsp
    +0x145d: pxor    %xmm0,%xmm0
    +0x1461: movdqu  %xmm0,(%rsp)
    +0x1466: mov     $0x20,%esi
    +0x146b: mov     $0x40,%ecx
    +0x1470: mov     $0x300,%r9d
    +0x1476: lea     0x210(%rsp),%r14
    +0x147e: mov     %r14,%rdi
    +0x1481: mov     %r8,%rdx
    +0x1484: lea     0x730(%rsp),%r8
    +0x148c: call    <mld_H44>
    +0x1491: add     $0x10,%rsp
    +0x1495: lea     0x2500(%rsp),%rbx
    +0x149d: mov     %rbx,%rdi
    +0x14a0: mov     %r14,%rsi
    +0x14a3: call    <mldsa44_poly_challenge>
    +0x14a8: mov     %rbx,%rdi
    +0x14ab: call    <mldsa_poly_ntt>
    +0x14b0: mov     $0x2,%ecx
    +0x14b5: mov     0x188(%rsp),%r10
    +0x14bd: xor     %r13d,%r13d
    +0x14c0: mov     %r10,0x10(%rsp)
    +0x14c5: mov     0x60(%rsp),%rax
    +0x14ca: mov     %rcx,0x198(%rsp)
    +0x14d2: add     %rcx,%rax
    +0x14d5: xor     %ecx,%ecx
    +0x14d7: nopw    0x0(%rax,%rax,1)
    +0x14e0: movzbl  -0x2(%rax),%edx
    +0x14e4: and     $0x7,%edx
    +0x14e7: mov     %edx,0xce0(%rsp,%rcx,1)
    +0x14ee: movzbl  -0x2(%rax),%esi
    +0x14f2: shr     $0x3,%esi
    +0x14f5: and     $0x7,%esi
    +0x14f8: mov     %esi,0xce4(%rsp,%rcx,1)
    +0x14ff: movzbl  -0x2(%rax),%edi
    +0x1503: shr     $0x6,%edi
    +0x1506: movzbl  -0x1(%rax),%r8d
    +0x150b: and     $0x1,%r8d
    +0x150f: lea     (%rdi,%r8,4),%r8d
    +0x1513: mov     %r8d,0xce8(%rsp,%rcx,1)
    +0x151b: movzbl  -0x1(%rax),%edi
    +0x151f: shr     $1,%edi
    +0x1521: and     $0x7,%edi
    +0x1524: mov     %edi,0xcec(%rsp,%rcx,1)
    +0x152b: movzbl  -0x1(%rax),%r9d
    +0x1530: shr     $0x4,%r9d
    +0x1534: and     $0x7,%r9d
    +0x1538: mov     %r9d,0xcf0(%rsp,%rcx,1)
    +0x1540: movzbl  -0x1(%rax),%r10d
    +0x1545: shr     $0x7,%r10d
    +0x1549: movzbl  (%rax),%r11d
    +0x154d: and     $0x3,%r11d
    +0x1551: lea     (%r10,%r11,2),%r10d
    +0x1555: mov     %r10d,0xcf4(%rsp,%rcx,1)
    +0x155d: movzbl  (%rax),%r11d
    +0x1561: shr     $0x2,%r11d
    +0x1565: and     $0x7,%r11d
    +0x1569: mov     %r11d,0xcf8(%rsp,%rcx,1)
    +0x1571: movzbl  (%rax),%ebx
    +0x1574: shr     $0x5,%ebx
    +0x1577: mov     $0x2,%r14d
    +0x157d: sub     %edx,%r14d
    +0x1580: mov     %r14d,0xce0(%rsp,%rcx,1)
    +0x1588: mov     $0x2,%edx
    +0x158d: sub     %esi,%edx
    +0x158f: mov     %edx,0xce4(%rsp,%rcx,1)
    +0x1596: mov     $0x2,%edx
    +0x159b: sub     %r8d,%edx
    +0x159e: mov     %edx,0xce8(%rsp,%rcx,1)
    +0x15a5: mov     $0x2,%edx
    +0x15aa: sub     %edi,%edx
    +0x15ac: mov     %edx,0xcec(%rsp,%rcx,1)
    +0x15b3: mov     $0x2,%edx
    +0x15b8: sub     %r9d,%edx
    +0x15bb: mov     %edx,0xcf0(%rsp,%rcx,1)
    +0x15c2: mov     $0x2,%edx
    +0x15c7: sub     %r10d,%edx
    +0x15ca: mov     %edx,0xcf4(%rsp,%rcx,1)
    +0x15d1: mov     $0x2,%edx
    +0x15d6: sub     %r11d,%edx
    +0x15d9: mov     %edx,0xcf8(%rsp,%rcx,1)
    +0x15e0: mov     $0x2,%edx
    +0x15e5: sub     %ebx,%edx
    +0x15e7: mov     %edx,0xcfc(%rsp,%rcx,1)
    +0x15ee: add     $0x20,%rcx
    +0x15f2: add     $0x3,%rax
    +0x15f6: cmp     $0x400,%rcx
    +0x15fd: jne     <mldsa44_signature_internal+0x14e0>
    +0x1603: lea     0xce0(%rsp),%rdi
    +0x160b: call    <mldsa_poly_ntt>
    +0x1610: mov     $0x1,%eax
    +0x1615: data16  cs nopw 0x0(%rax,%rax,1)
    +0x1620: movslq  0xcdc(%rsp,%rax,4),%rcx
    +0x1628: movslq  0x24fc(%rsp,%rax,4),%rdx
    +0x1630: imul    %rcx,%rdx
    +0x1634: mov     %rdx,%rcx
    +0x1637: imul    %r12,%rcx
    +0x163b: sar     $0x20,%rcx
    +0x163f: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x1646: add     %rdx,%rcx
    +0x1649: shr     $0x20,%rcx
    +0x164d: mov     %ecx,0xcdc(%rsp,%rax,4)
    +0x1654: movslq  0xce0(%rsp,%rax,4),%rcx
    +0x165c: movslq  0x2500(%rsp,%rax,4),%rdx
    +0x1664: imul    %rcx,%rdx
    +0x1668: mov     %rdx,%rcx
    +0x166b: imul    %r12,%rcx
    +0x166f: sar     $0x20,%rcx
    +0x1673: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x167a: add     %rdx,%rcx
    +0x167d: shr     $0x20,%rcx
    +0x1681: mov     %ecx,0xce0(%rsp,%rax,4)
    +0x1688: add     $0x2,%rax
    +0x168c: cmp     $0x101,%rax
    +0x1692: jne     <mldsa44_signature_internal+0x1620>
    +0x1694: lea     0xce0(%rsp),%rdi
    +0x169c: call    <mldsa_poly_invntt_tomont>
    +0x16a1: mov     0x80(%rsp),%rax
    +0x16a9: movzwl  0x88(%rsp),%ecx
    +0x16b1: mov     %r13,0x98(%rsp)
    +0x16b9: add     %r13w,%cx
    +0x16bd: movups  (%rax),%xmm0
    +0x16c0: movups  0x10(%rax),%xmm1
    +0x16c4: movups  0x20(%rax),%xmm2
    +0x16c8: movdqu  0x30(%rax),%xmm3
    +0x16cd: movaps  %xmm0,0x1a0(%rsp)
    +0x16d5: movaps  %xmm1,0x1b0(%rsp)
    +0x16dd: movaps  %xmm2,0x1c0(%rsp)
    +0x16e5: movdqa  %xmm3,0x1d0(%rsp)
    +0x16ee: mov     %cx,0x1e0(%rsp)
    +0x16f6: xorps   %xmm0,%xmm0
    +0x16f9: movaps  %xmm0,0xa0(%rsp)
    +0x1701: movaps  %xmm0,0xb0(%rsp)
    +0x1709: movaps  %xmm0,0xc0(%rsp)
    +0x1711: movaps  %xmm0,0xd0(%rsp)
    +0x1719: movaps  %xmm0,0xe0(%rsp)
    +0x1721: movaps  %xmm0,0xf0(%rsp)
    +0x1729: movaps  %xmm0,0x100(%rsp)
    +0x1731: movaps  %xmm0,0x110(%rsp)
    +0x1739: movaps  %xmm0,0x120(%rsp)
    +0x1741: movaps  %xmm0,0x130(%rsp)
    +0x1749: movaps  %xmm0,0x140(%rsp)
    +0x1751: movaps  %xmm0,0x150(%rsp)
    +0x1759: movups  %xmm0,0x15c(%rsp)
    +0x1761: movaps  0x1a0(%rsp),%xmm0
    +0x1769: movaps  0xb0(%rsp),%xmm1
    +0x1771: xorps   0x1b0(%rsp),%xmm1
    +0x1779: movaps  %xmm0,0xa0(%rsp)
    +0x1781: movaps  %xmm1,0xb0(%rsp)
    +0x1789: movdqa  0xc0(%rsp),%xmm0
    +0x1792: movdqa  0xd0(%rsp),%xmm1
    +0x179b: pxor    0x1c0(%rsp),%xmm0
    +0x17a4: movdqa  0xe0(%rsp),%xmm2
    +0x17ad: pxor    0x1d0(%rsp),%xmm1
    +0x17b6: movdqa  %xmm0,0xc0(%rsp)
    +0x17bf: movdqa  %xmm1,0xd0(%rsp)
    +0x17c8: pxor    0x1e0(%rsp),%xmm2
    +0x17d1: movd    %xmm2,%eax
    +0x17d5: mov     %ax,0xe0(%rsp)
    +0x17dd: xorb    $0x1f,0xe2(%rsp)
    +0x17e5: xorb    $0x80,0x127(%rsp)
    +0x17ed: movl    $0x88,0x168(%rsp)
    +0x17f8: mov     $0x88,%r12d
    +0x17fe: mov     $0x2a8,%r13d
    +0x1804: xor     %r14d,%r14d
    +0x1807: jmp     <mldsa44_signature_internal+0x184b>
    +0x1809: nopl    0x0(%rax)
    +0x1810: mov     $0x88,%ebx
    +0x1815: sub     %r12d,%ebx
    +0x1818: cmp     %rbx,%r13
    +0x181b: cmovb   %r13,%rbx
    +0x181f: mov     %r12d,%eax
    +0x1822: lea     (%rsp,%rax,1),%rsi
    +0x1826: add     $0xa0,%rsi
    +0x182d: lea     (%rsp,%r14,1),%rdi
    +0x1831: add     $0xa20,%rdi
    +0x1838: mov     %rbx,%rdx
    +0x183b: call    <memcpy>
    +0x1840: add     %ebx,%r12d
    +0x1843: add     %rbx,%r14
    +0x1846: sub     %rbx,%r13
    +0x1849: je      <mldsa44_signature_internal+0x1880>
    +0x184b: cmp     $0x88,%r12d
    +0x1852: jne     <mldsa44_signature_internal+0x1810>
    +0x1854: lea     0xa0(%rsp),%r15
    +0x185c: mov     %r15,%rdi
    +0x185f: call    <mldsa_keccakf1600_permute>
    +0x1864: cmp     $0x88,%r13
    +0x186b: mov     $0x88,%ebx
    +0x1870: cmovb   %r13,%rbx
    +0x1874: xor     %r12d,%r12d
    +0x1877: mov     %r15,%rsi
    +0x187a: jmp     <mldsa44_signature_internal+0x182d>
    +0x187c: nopl    0x0(%rax)
    +0x1880: mov     $0x8,%eax
    +0x1885: lea     0x32c(%rsp),%rcx
    +0x188d: nopl    (%rax)
    +0x1890: movzwl  0xa18(%rsp,%rax,1),%esi
    +0x1898: movzbl  0xa1a(%rsp,%rax,1),%edi
    +0x18a0: mov     %edi,%edx
    +0x18a2: and     $0x3,%edx
    +0x18a5: shl     $0x10,%edx
    +0x18a8: or      %esi,%edx
    +0x18aa: shr     $0x2,%edi
    +0x18ad: movzbl  0xa1b(%rsp,%rax,1),%r8d
    +0x18b6: shl     $0x6,%r8d
    +0x18ba: or      %edi,%r8d
    +0x18bd: movzbl  0xa1c(%rsp,%rax,1),%edi
    +0x18c5: mov     %edi,%esi
    +0x18c7: and     $0xf,%esi
    +0x18ca: shl     $0xe,%esi
    +0x18cd: or      %r8d,%esi
    +0x18d0: shr     $0x4,%edi
    +0x18d3: movzbl  0xa1d(%rsp,%rax,1),%r8d
    +0x18dc: shl     $0x4,%r8d
    +0x18e0: or      %edi,%r8d
    +0x18e3: movzbl  0xa1e(%rsp,%rax,1),%edi
    +0x18eb: mov     %edi,%r9d
    +0x18ee: and     $0x3f,%r9d
    +0x18f2: shl     $0xc,%r9d
    +0x18f6: or      %r8d,%r9d
    +0x18f9: shr     $0x6,%edi
    +0x18fc: movzbl  0xa1f(%rsp,%rax,1),%r8d
    +0x1905: lea     (%rdi,%r8,4),%edi
    +0x1909: movzbl  0xa20(%rsp,%rax,1),%r8d
    +0x1912: shl     $0xa,%r8d
    +0x1916: or      %edi,%r8d
    +0x1919: mov     $0x20000,%edi
    +0x191e: sub     %edx,%edi
    +0x1920: mov     %edi,-0xc(%rcx)
    +0x1923: mov     $0x20000,%edx
    +0x1928: sub     %esi,%edx
    +0x192a: mov     %edx,-0x8(%rcx)
    +0x192d: mov     $0x20000,%edx
    +0x1932: sub     %r9d,%edx
    +0x1935: mov     %edx,-0x4(%rcx)
    +0x1938: mov     $0x20000,%edx
    +0x193d: sub     %r8d,%edx
    +0x1940: mov     %edx,(%rcx)
    +0x1942: add     $0x9,%rax
    +0x1946: add     $0x10,%rcx
    +0x194a: cmp     $0x248,%rax
    +0x1950: jne     <mldsa44_signature_internal+0x1890>
    +0x1956: pxor    %xmm0,%xmm0
    +0x195a: movdqa  %xmm0,0x160(%rsp)
    +0x1963: movdqa  %xmm0,0x150(%rsp)
    +0x196c: movdqa  %xmm0,0x140(%rsp)
    +0x1975: movdqa  %xmm0,0x130(%rsp)
    +0x197e: movdqa  %xmm0,0x120(%rsp)
    +0x1987: movdqa  %xmm0,0x110(%rsp)
    +0x1990: movdqa  %xmm0,0x100(%rsp)
    +0x1999: movdqa  %xmm0,0xf0(%rsp)
    +0x19a2: movdqa  %xmm0,0xe0(%rsp)
    +0x19ab: movdqa  %xmm0,0xd0(%rsp)
    +0x19b4: movdqa  %xmm0,0xc0(%rsp)
    +0x19bd: movdqa  %xmm0,0xb0(%rsp)
    +0x19c6: movdqa  %xmm0,0xa0(%rsp)
    +0x19cf: lea     0xa0(%rsp),%rax
    +0x19d7: mov     $0x2a8,%edx
    +0x19dc: lea     0xa20(%rsp),%rbx
    +0x19e4: mov     %rbx,%rdi
    +0x19e7: xor     %esi,%esi
    +0x19e9: call    <memset>
    +0x19ee: pxor    %xmm0,%xmm0
    +0x19f2: movdqa  %xmm0,0x1d0(%rsp)
    +0x19fb: movdqa  %xmm0,0x1c0(%rsp)
    +0x1a04: movdqa  %xmm0,0x1b0(%rsp)
    +0x1a0d: pxor    %xmm5,%xmm5
    +0x1a11: movdqa  %xmm0,0x1a0(%rsp)
    +0x1a1a: movw    $0x0,0x1e0(%rsp)
    +0x1a24: lea     0x1a0(%rsp),%rax
    +0x1a2c: mov     $0xc,%eax
    +0x1a31: movabs  $0x380200100000000,%r12
    +0x1a3b: mov     0x98(%rsp),%r13
    +0x1a43: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1a50: movdqa  0x2f0(%rsp,%rax,4),%xmm0
    +0x1a59: movdqa  0x300(%rsp,%rax,4),%xmm1
    +0x1a62: movdqa  0x310(%rsp,%rax,4),%xmm2
    +0x1a6b: movdqa  0x320(%rsp,%rax,4),%xmm3
    +0x1a74: paddd   0xcb0(%rsp,%rax,4),%xmm0
    +0x1a7d: paddd   0xcc0(%rsp,%rax,4),%xmm1
    +0x1a86: movdqa  %xmm0,0xcb0(%rsp,%rax,4)
    +0x1a8f: movdqa  %xmm1,0xcc0(%rsp,%rax,4)
    +0x1a98: paddd   0xcd0(%rsp,%rax,4),%xmm2
    +0x1aa1: paddd   0xce0(%rsp,%rax,4),%xmm3
    +0x1aaa: movdqa  %xmm2,0xcd0(%rsp,%rax,4)
    +0x1ab3: movdqa  %xmm3,0xce0(%rsp,%rax,4)
    +0x1abc: add     $0x10,%rax
    +0x1ac0: cmp     $0x10c,%rax
    +0x1ac6: jne     <mldsa44_signature_internal+0x1a50>
    +0x1ac8: mov     $0x4,%eax
    +0x1acd: movdqa  0x20f1b(%rip),%xmm6
    +0x1ad5: movdqa  0x20f23(%rip),%xmm7
    +0x1add: mov     0x10(%rsp),%r10
    +0x1ae2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1af0: movdqa  0xcd0(%rsp,%rax,4),%xmm0
    +0x1af9: movdqa  0xce0(%rsp,%rax,4),%xmm1
    +0x1b02: movdqa  %xmm0,%xmm2
    +0x1b06: paddd   %xmm6,%xmm2
    +0x1b0a: movdqa  %xmm1,%xmm3
    +0x1b0e: paddd   %xmm6,%xmm3
    +0x1b12: psrad   $0x17,%xmm2
    +0x1b17: psrad   $0x17,%xmm3
    +0x1b1c: pshufd  $0xf5,%xmm2,%xmm4
    +0x1b21: pmuludq %xmm7,%xmm2
    +0x1b25: pshufd  $0xe8,%xmm2,%xmm2
    +0x1b2a: pmuludq %xmm7,%xmm4
    +0x1b2e: pshufd  $0xe8,%xmm4,%xmm4
    +0x1b33: punpckldq %xmm4,%xmm2
    +0x1b37: pshufd  $0xf5,%xmm3,%xmm4
    +0x1b3c: pmuludq %xmm7,%xmm3
    +0x1b40: pshufd  $0xe8,%xmm3,%xmm3
    +0x1b45: pmuludq %xmm7,%xmm4
    +0x1b49: pshufd  $0xe8,%xmm4,%xmm4
    +0x1b4e: punpckldq %xmm4,%xmm3
    +0x1b52: paddd   %xmm0,%xmm2
    +0x1b56: paddd   %xmm1,%xmm3
    +0x1b5a: movdqa  %xmm2,0xcd0(%rsp,%rax,4)
    +0x1b63: movdqa  %xmm3,0xce0(%rsp,%rax,4)
    +0x1b6c: add     $0x8,%rax
    +0x1b70: cmp     $0x104,%rax
    +0x1b76: jne     <mldsa44_signature_internal+0x1af0>
    +0x1b7c: xor     %eax,%eax
    +0x1b7e: xor     %ecx,%ecx
    +0x1b80: movslq  0xce0(%rsp,%rcx,4),%rdx
    +0x1b88: mov     %edx,%esi
    +0x1b8a: neg     %esi
    +0x1b8c: mov     %rdx,%rdi
    +0x1b8f: shr     $0x1f,%rdi
    +0x1b93: xor     %edx,%esi
    +0x1b95: and     %edi,%esi
    +0x1b97: xor     %edx,%esi
    +0x1b99: mov     $0x1ffb1,%edx
    +0x1b9e: sub     %esi,%edx
    +0x1ba0: movslq  %edx,%rdx
    +0x1ba3: shr     $0x1f,%rdx
    +0x1ba7: or      %edx,%eax
    +0x1ba9: inc     %rcx
    +0x1bac: cmp     $0x100,%rcx
    +0x1bb3: jne     <mldsa44_signature_internal+0x1b80>
    +0x1bb5: xor     %r15d,%r15d
    +0x1bb8: test    %eax,%eax
    +0x1bba: jne     <mldsa44_signature_internal+0x2780>
    +0x1bc0: lea     0xcec(%rsp),%rax
    +0x1bc8: xor     %ecx,%ecx
    +0x1bca: nopw    0x0(%rax,%rax,1)
    +0x1bd0: mov     $0x20000,%edi
    +0x1bd5: sub     -0xc(%rax),%edi
    +0x1bd8: mov     $0x20000,%r8d
    +0x1bde: sub     -0x8(%rax),%r8d
    +0x1be2: mov     $0x20000,%esi
    +0x1be7: sub     -0x4(%rax),%esi
    +0x1bea: mov     $0x20000,%edx
    +0x1bef: sub     (%rax),%edx
    +0x1bf1: mov     %di,-0x7(%r10,%rcx,1)
    +0x1bf7: shr     $0x10,%edi
    +0x1bfa: lea     0x0(,%r8,4),%r9d
    +0x1c02: or      %edi,%r9d
    +0x1c05: mov     %r9b,-0x5(%r10,%rcx,1)
    +0x1c0a: mov     %r8d,%edi
    +0x1c0d: shr     $0x6,%edi
    +0x1c10: mov     %dil,-0x4(%r10,%rcx,1)
    +0x1c15: shr     $0xe,%r8d
    +0x1c19: mov     %esi,%edi
    +0x1c1b: shl     $0x4,%edi
    +0x1c1e: or      %r8d,%edi
    +0x1c21: mov     %dil,-0x3(%r10,%rcx,1)
    +0x1c26: mov     %esi,%edi
    +0x1c28: shr     $0x4,%edi
    +0x1c2b: mov     %dil,-0x2(%r10,%rcx,1)
    +0x1c30: shr     $0xc,%esi
    +0x1c33: mov     %edx,%edi
    +0x1c35: shl     $0x6,%edi
    +0x1c38: or      %esi,%edi
    +0x1c3a: mov     %dil,-0x1(%r10,%rcx,1)
    +0x1c3f: shr     $0x2,%edx
    +0x1c42: mov     %dx,(%r10,%rcx,1)
    +0x1c47: add     $0x9,%rcx
    +0x1c4b: add     $0x10,%rax
    +0x1c4f: cmp     $0x240,%rcx
    +0x1c56: jne     <mldsa44_signature_internal+0x1bd0>
    +0x1c5c: movdqa  %xmm5,0xa20(%rsp)
    +0x1c65: lea     0xa20(%rsp),%rax
    +0x1c6d: inc     %r13
    +0x1c70: mov     0x198(%rsp),%rcx
    +0x1c78: add     $0x60,%rcx
    +0x1c7c: add     $0x240,%r10
    +0x1c83: cmp     $0x4,%r13
    +0x1c87: jne     <mldsa44_signature_internal+0x14c0>
    +0x1c8d: mov     $0x2,%ecx
    +0x1c92: mov     $0xc,%eax
    +0x1c97: mov     %rax,0x10(%rsp)
    +0x1c9c: lea     0x1500(%rsp),%rbx
    +0x1ca4: xor     %r13d,%r13d
    +0x1ca7: nopw    0x0(%rax,%rax,1)
    +0x1cb0: mov     0x20(%rsp),%rax
    +0x1cb5: mov     %rcx,0x98(%rsp)
    +0x1cbd: add     %rcx,%rax
    +0x1cc0: xor     %ecx,%ecx
    +0x1cc2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1cd0: movzbl  -0x2(%rax),%edx
    +0x1cd4: and     $0x7,%edx
    +0x1cd7: mov     %edx,0x320(%rsp,%rcx,1)
    +0x1cde: movzbl  -0x2(%rax),%esi
    +0x1ce2: shr     $0x3,%esi
    +0x1ce5: and     $0x7,%esi
    +0x1ce8: mov     %esi,0x324(%rsp,%rcx,1)
    +0x1cef: movzbl  -0x2(%rax),%edi
    +0x1cf3: shr     $0x6,%edi
    +0x1cf6: movzbl  -0x1(%rax),%r8d
    +0x1cfb: and     $0x1,%r8d
    +0x1cff: lea     (%rdi,%r8,4),%r8d
    +0x1d03: mov     %r8d,0x328(%rsp,%rcx,1)
    +0x1d0b: movzbl  -0x1(%rax),%edi
    +0x1d0f: shr     $1,%edi
    +0x1d11: and     $0x7,%edi
    +0x1d14: mov     %edi,0x32c(%rsp,%rcx,1)
    +0x1d1b: movzbl  -0x1(%rax),%r9d
    +0x1d20: shr     $0x4,%r9d
    +0x1d24: and     $0x7,%r9d
    +0x1d28: mov     %r9d,0x330(%rsp,%rcx,1)
    +0x1d30: movzbl  -0x1(%rax),%r10d
    +0x1d35: shr     $0x7,%r10d
    +0x1d39: movzbl  (%rax),%r11d
    +0x1d3d: and     $0x3,%r11d
    +0x1d41: lea     (%r10,%r11,2),%r10d
    +0x1d45: mov     %r10d,0x334(%rsp,%rcx,1)
    +0x1d4d: movzbl  (%rax),%r11d
    +0x1d51: shr     $0x2,%r11d
    +0x1d55: and     $0x7,%r11d
    +0x1d59: mov     %r11d,0x338(%rsp,%rcx,1)
    +0x1d61: movzbl  (%rax),%r14d
    +0x1d65: shr     $0x5,%r14d
    +0x1d69: mov     $0x2,%r15d
    +0x1d6f: sub     %edx,%r15d
    +0x1d72: mov     %r15d,0x320(%rsp,%rcx,1)
    +0x1d7a: mov     $0x2,%edx
    +0x1d7f: sub     %esi,%edx
    +0x1d81: mov     %edx,0x324(%rsp,%rcx,1)
    +0x1d88: mov     $0x2,%edx
    +0x1d8d: sub     %r8d,%edx
    +0x1d90: mov     %edx,0x328(%rsp,%rcx,1)
    +0x1d97: mov     $0x2,%edx
    +0x1d9c: sub     %edi,%edx
    +0x1d9e: mov     %edx,0x32c(%rsp,%rcx,1)
    +0x1da5: mov     $0x2,%edx
    +0x1daa: sub     %r9d,%edx
    +0x1dad: mov     %edx,0x330(%rsp,%rcx,1)
    +0x1db4: mov     $0x2,%edx
    +0x1db9: sub     %r10d,%edx
    +0x1dbc: mov     %edx,0x334(%rsp,%rcx,1)
    +0x1dc3: mov     $0x2,%edx
    +0x1dc8: sub     %r11d,%edx
    +0x1dcb: mov     %edx,0x338(%rsp,%rcx,1)
    +0x1dd2: mov     $0x2,%edx
    +0x1dd7: sub     %r14d,%edx
    +0x1dda: mov     %edx,0x33c(%rsp,%rcx,1)
    +0x1de1: add     $0x20,%rcx
    +0x1de5: add     $0x3,%rax
    +0x1de9: cmp     $0x400,%rcx
    +0x1df0: jne     <mldsa44_signature_internal+0x1cd0>
    +0x1df6: lea     0x320(%rsp),%rdi
    +0x1dfe: call    <mldsa_poly_ntt>
    +0x1e03: mov     $0x1,%eax
    +0x1e08: nopl    0x0(%rax,%rax,1)
    +0x1e10: movslq  0x31c(%rsp,%rax,4),%rcx
    +0x1e18: movslq  0x24fc(%rsp,%rax,4),%rdx
    +0x1e20: imul    %rcx,%rdx
    +0x1e24: mov     %rdx,%rcx
    +0x1e27: imul    %r12,%rcx
    +0x1e2b: sar     $0x20,%rcx
    +0x1e2f: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x1e36: add     %rdx,%rcx
    +0x1e39: shr     $0x20,%rcx
    +0x1e3d: mov     %ecx,0x31c(%rsp,%rax,4)
    +0x1e44: movslq  0x320(%rsp,%rax,4),%rcx
    +0x1e4c: movslq  0x2500(%rsp,%rax,4),%rdx
    +0x1e54: imul    %rcx,%rdx
    +0x1e58: mov     %rdx,%rcx
    +0x1e5b: imul    %r12,%rcx
    +0x1e5f: sar     $0x20,%rcx
    +0x1e63: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x1e6a: add     %rdx,%rcx
    +0x1e6d: shr     $0x20,%rcx
    +0x1e71: mov     %ecx,0x320(%rsp,%rax,4)
    +0x1e78: add     $0x2,%rax
    +0x1e7c: cmp     $0x101,%rax
    +0x1e82: jne     <mldsa44_signature_internal+0x1e10>
    +0x1e84: lea     0x320(%rsp),%rdi
    +0x1e8c: call    <mldsa_poly_invntt_tomont>
    +0x1e91: mov     $0xc,%eax
    +0x1e96: cs      nopw 0x0(%rax,%rax,1)
    +0x1ea0: movdqa  -0x30(%rbx,%rax,4),%xmm0
    +0x1ea6: movdqa  -0x20(%rbx,%rax,4),%xmm1
    +0x1eac: movdqa  -0x10(%rbx,%rax,4),%xmm2
    +0x1eb2: movdqa  (%rbx,%rax,4),%xmm3
    +0x1eb7: psubd   0x2f0(%rsp,%rax,4),%xmm0
    +0x1ec0: psubd   0x300(%rsp,%rax,4),%xmm1
    +0x1ec9: movdqa  %xmm0,-0x30(%rbx,%rax,4)
    +0x1ecf: movdqa  %xmm1,-0x20(%rbx,%rax,4)
    +0x1ed5: psubd   0x310(%rsp,%rax,4),%xmm2
    +0x1ede: psubd   0x320(%rsp,%rax,4),%xmm3
    +0x1ee7: movdqa  %xmm2,-0x10(%rbx,%rax,4)
    +0x1eed: movdqa  %xmm3,(%rbx,%rax,4)
    +0x1ef2: add     $0x10,%rax
    +0x1ef6: cmp     $0x10c,%rax
    +0x1efc: jne     <mldsa44_signature_internal+0x1ea0>
    +0x1efe: mov     $0x4,%eax
    +0x1f03: movdqa  0x20ae5(%rip),%xmm5
    +0x1f0b: movdqa  0x20aed(%rip),%xmm6
    +0x1f13: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1f20: movdqa  -0x10(%rbx,%rax,4),%xmm0
    +0x1f26: movdqa  (%rbx,%rax,4),%xmm1
    +0x1f2b: movdqa  %xmm0,%xmm2
    +0x1f2f: paddd   %xmm5,%xmm2
    +0x1f33: movdqa  %xmm1,%xmm3
    +0x1f37: paddd   %xmm5,%xmm3
    +0x1f3b: psrad   $0x17,%xmm2
    +0x1f40: psrad   $0x17,%xmm3
    +0x1f45: pshufd  $0xf5,%xmm2,%xmm4
    +0x1f4a: pmuludq %xmm6,%xmm2
    +0x1f4e: pshufd  $0xe8,%xmm2,%xmm2
    +0x1f53: pmuludq %xmm6,%xmm4
    +0x1f57: pshufd  $0xe8,%xmm4,%xmm4
    +0x1f5c: punpckldq %xmm4,%xmm2
    +0x1f60: pshufd  $0xf5,%xmm3,%xmm4
    +0x1f65: pmuludq %xmm6,%xmm3
    +0x1f69: pshufd  $0xe8,%xmm3,%xmm3
    +0x1f6e: pmuludq %xmm6,%xmm4
    +0x1f72: pshufd  $0xe8,%xmm4,%xmm4
    +0x1f77: punpckldq %xmm4,%xmm3
    +0x1f7b: paddd   %xmm0,%xmm2
    +0x1f7f: paddd   %xmm1,%xmm3
    +0x1f83: movdqa  %xmm2,-0x10(%rbx,%rax,4)
    +0x1f89: movdqa  %xmm3,(%rbx,%rax,4)
    +0x1f8e: add     $0x8,%rax
    +0x1f92: cmp     $0x104,%rax
    +0x1f98: jne     <mldsa44_signature_internal+0x1f20>
    +0x1f9a: xor     %eax,%eax
    +0x1f9c: xor     %ecx,%ecx
    +0x1f9e: xchg    %ax,%ax
    +0x1fa0: movslq  (%rbx,%rcx,4),%rdx
    +0x1fa4: mov     %edx,%esi
    +0x1fa6: neg     %esi
    +0x1fa8: mov     %rdx,%rdi
    +0x1fab: shr     $0x1f,%rdi
    +0x1faf: xor     %edx,%esi
    +0x1fb1: and     %edi,%esi
    +0x1fb3: xor     %edx,%esi
    +0x1fb5: mov     $0x173b1,%edx
    +0x1fba: sub     %esi,%edx
    +0x1fbc: movslq  %edx,%rdx
    +0x1fbf: shr     $0x1f,%rdx
    +0x1fc3: or      %edx,%eax
    +0x1fc5: inc     %rcx
    +0x1fc8: cmp     $0x100,%rcx
    +0x1fcf: jne     <mldsa44_signature_internal+0x1fa0>
    +0x1fd1: test    %eax,%eax
    +0x1fd3: jne     <mldsa44_signature_internal+0x2510>
    +0x1fd9: mov     0x40(%rsp),%rax
    +0x1fde: add     0x10(%rsp),%rax
    +0x1fe3: mov     $0x1c,%ecx
    +0x1fe8: nopl    0x0(%rax,%rax,1)
    +0x1ff0: movzbl  -0xc(%rax),%esi
    +0x1ff4: mov     %esi,0x304(%rsp,%rcx,1)
    +0x1ffb: movzbl  -0xb(%rax),%edx
    +0x1fff: and     $0x1f,%edx
    +0x2002: shl     $0x8,%edx
    +0x2005: or      %esi,%edx
    +0x2007: mov     %edx,0x304(%rsp,%rcx,1)
    +0x200e: movzbl  -0xb(%rax),%esi
    +0x2012: shr     $0x5,%esi
    +0x2015: mov     %esi,0x308(%rsp,%rcx,1)
    +0x201c: movzbl  -0xa(%rax),%edi
    +0x2020: lea     (%rsi,%rdi,8),%edi
    +0x2023: mov     %edi,0x308(%rsp,%rcx,1)
    +0x202a: movzbl  -0x9(%rax),%esi
    +0x202e: and     $0x3,%esi
    +0x2031: shl     $0xb,%esi
    +0x2034: or      %edi,%esi
    +0x2036: mov     %esi,0x308(%rsp,%rcx,1)
    +0x203d: movzbl  -0x9(%rax),%r8d
    +0x2042: shr     $0x2,%r8d
    +0x2046: mov     %r8d,0x30c(%rsp,%rcx,1)
    +0x204e: movzbl  -0x8(%rax),%edi
    +0x2052: and     $0x7f,%edi
    +0x2055: shl     $0x6,%edi
    +0x2058: or      %r8d,%edi
    +0x205b: mov     %edi,0x30c(%rsp,%rcx,1)
    +0x2062: movzbl  -0x8(%rax),%r8d
    +0x2067: shr     $0x7,%r8d
    +0x206b: mov     %r8d,0x310(%rsp,%rcx,1)
    +0x2073: movzbl  -0x7(%rax),%r9d
    +0x2078: lea     (%r8,%r9,2),%r9d
    +0x207c: mov     %r9d,0x310(%rsp,%rcx,1)
    +0x2084: movzbl  -0x6(%rax),%r8d
    +0x2089: and     $0xf,%r8d
    +0x208d: shl     $0x9,%r8d
    +0x2091: or      %r9d,%r8d
    +0x2094: mov     %r8d,0x310(%rsp,%rcx,1)
    +0x209c: movzbl  -0x6(%rax),%r9d
    +0x20a1: shr     $0x4,%r9d
    +0x20a5: mov     %r9d,0x314(%rsp,%rcx,1)
    +0x20ad: movzbl  -0x5(%rax),%r10d
    +0x20b2: shl     $0x4,%r10d
    +0x20b6: or      %r9d,%r10d
    +0x20b9: mov     %r10d,0x314(%rsp,%rcx,1)
    +0x20c1: movzbl  -0x4(%rax),%r9d
    +0x20c6: and     $0x1,%r9d
    +0x20ca: shl     $0xc,%r9d
    +0x20ce: or      %r10d,%r9d
    +0x20d1: mov     %r9d,0x314(%rsp,%rcx,1)
    +0x20d9: movzbl  -0x4(%rax),%r11d
    +0x20de: shr     $1,%r11d
    +0x20e1: mov     %r11d,0x318(%rsp,%rcx,1)
    +0x20e9: movzbl  -0x3(%rax),%r10d
    +0x20ee: and     $0x3f,%r10d
    +0x20f2: shl     $0x7,%r10d
    +0x20f6: or      %r11d,%r10d
    +0x20f9: mov     %r10d,0x318(%rsp,%rcx,1)
    +0x2101: movzbl  -0x3(%rax),%r11d
    +0x2106: shr     $0x6,%r11d
    +0x210a: mov     %r11d,0x31c(%rsp,%rcx,1)
    +0x2112: movzbl  -0x2(%rax),%r14d
    +0x2117: lea     (%r11,%r14,4),%r14d
    +0x211b: mov     %r14d,0x31c(%rsp,%rcx,1)
    +0x2123: movzbl  -0x1(%rax),%r11d
    +0x2128: and     $0x7,%r11d
    +0x212c: shl     $0xa,%r11d
    +0x2130: or      %r14d,%r11d
    +0x2133: mov     %r11d,0x31c(%rsp,%rcx,1)
    +0x213b: movzbl  -0x1(%rax),%r14d
    +0x2140: shr     $0x3,%r14d
    +0x2144: mov     %r14d,0x320(%rsp,%rcx,1)
    +0x214c: movzbl  (%rax),%r15d
    +0x2150: shl     $0x5,%r15d
    +0x2154: mov     $0x1000,%r12d
    +0x215a: sub     %edx,%r12d
    +0x215d: mov     %r12d,0x304(%rsp,%rcx,1)
    +0x2165: mov     $0x1000,%edx
    +0x216a: sub     %esi,%edx
    +0x216c: mov     %edx,0x308(%rsp,%rcx,1)
    +0x2173: mov     $0x1000,%edx
    +0x2178: sub     %edi,%edx
    +0x217a: mov     %edx,0x30c(%rsp,%rcx,1)
    +0x2181: mov     $0x1000,%edx
    +0x2186: sub     %r8d,%edx
    +0x2189: mov     %edx,0x310(%rsp,%rcx,1)
    +0x2190: mov     $0x1000,%edx
    +0x2195: sub     %r9d,%edx
    +0x2198: mov     %edx,0x314(%rsp,%rcx,1)
    +0x219f: mov     $0x1000,%edx
    +0x21a4: sub     %r10d,%edx
    +0x21a7: mov     %edx,0x318(%rsp,%rcx,1)
    +0x21ae: mov     $0x1000,%edx
    +0x21b3: sub     %r11d,%edx
    +0x21b6: mov     %edx,0x31c(%rsp,%rcx,1)
    +0x21bd: or      %r14d,%r15d
    +0x21c0: mov     $0x1000,%edx
    +0x21c5: sub     %r15d,%edx
    +0x21c8: mov     %edx,0x320(%rsp,%rcx,1)
    +0x21cf: add     $0x20,%rcx
    +0x21d3: add     $0xd,%rax
    +0x21d7: cmp     $0x41c,%rcx
    +0x21de: jne     <mldsa44_signature_internal+0x1ff0>
    +0x21e4: lea     0x320(%rsp),%rdi
    +0x21ec: call    <mldsa_poly_ntt>
    +0x21f1: mov     $0x1,%eax
    +0x21f6: movabs  $0x380200100000000,%r12
    +0x2200: movslq  0x31c(%rsp,%rax,4),%rcx
    +0x2208: movslq  0x24fc(%rsp,%rax,4),%rdx
    +0x2210: imul    %rcx,%rdx
    +0x2214: mov     %rdx,%rcx
    +0x2217: imul    %r12,%rcx
    +0x221b: sar     $0x20,%rcx
    +0x221f: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x2226: add     %rdx,%rcx
    +0x2229: shr     $0x20,%rcx
    +0x222d: mov     %ecx,0x31c(%rsp,%rax,4)
    +0x2234: movslq  0x320(%rsp,%rax,4),%rcx
    +0x223c: movslq  0x2500(%rsp,%rax,4),%rdx
    +0x2244: imul    %rcx,%rdx
    +0x2248: mov     %rdx,%rcx
    +0x224b: imul    %r12,%rcx
    +0x224f: sar     $0x20,%rcx
    +0x2253: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x225a: add     %rdx,%rcx
    +0x225d: shr     $0x20,%rcx
    +0x2261: mov     %ecx,0x320(%rsp,%rax,4)
    +0x2268: add     $0x2,%rax
    +0x226c: cmp     $0x101,%rax
    +0x2272: jne     <mldsa44_signature_internal+0x2200>
    +0x2274: lea     0x320(%rsp),%rdi
    +0x227c: call    <mldsa_poly_invntt_tomont>
    +0x2281: xor     %eax,%eax
    +0x2283: movdqa  0x20765(%rip),%xmm5
    +0x228b: movdqa  0x2076d(%rip),%xmm6
    +0x2293: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x22a0: movdqa  0x320(%rsp,%rax,4),%xmm0
    +0x22a9: movdqa  0x330(%rsp,%rax,4),%xmm1
    +0x22b2: movdqa  %xmm0,%xmm2
    +0x22b6: paddd   %xmm5,%xmm2
    +0x22ba: movdqa  %xmm1,%xmm3
    +0x22be: paddd   %xmm5,%xmm3
    +0x22c2: psrad   $0x17,%xmm2
    +0x22c7: psrad   $0x17,%xmm3
    +0x22cc: pshufd  $0xf5,%xmm2,%xmm4
    +0x22d1: pmuludq %xmm6,%xmm2
    +0x22d5: pshufd  $0xe8,%xmm2,%xmm2
    +0x22da: pmuludq %xmm6,%xmm4
    +0x22de: pshufd  $0xe8,%xmm4,%xmm4
    +0x22e3: punpckldq %xmm4,%xmm2
    +0x22e7: pshufd  $0xf5,%xmm3,%xmm4
    +0x22ec: pmuludq %xmm6,%xmm3
    +0x22f0: pshufd  $0xe8,%xmm3,%xmm3
    +0x22f5: pmuludq %xmm6,%xmm4
    +0x22f9: pshufd  $0xe8,%xmm4,%xmm4
    +0x22fe: punpckldq %xmm4,%xmm3
    +0x2302: paddd   %xmm0,%xmm2
    +0x2306: paddd   %xmm1,%xmm3
    +0x230a: movdqa  %xmm2,0x320(%rsp,%rax,4)
    +0x2313: movdqa  %xmm3,0x330(%rsp,%rax,4)
    +0x231c: add     $0x8,%rax
    +0x2320: cmp     $0x100,%rax
    +0x2326: jne     <mldsa44_signature_internal+0x22a0>
    +0x232c: xor     %eax,%eax
    +0x232e: xor     %ecx,%ecx
    +0x2330: movslq  0x320(%rsp,%rcx,4),%rdx
    +0x2338: mov     %edx,%esi
    +0x233a: neg     %esi
    +0x233c: mov     %rdx,%rdi
    +0x233f: shr     $0x1f,%rdi
    +0x2343: xor     %edx,%esi
    +0x2345: and     %edi,%esi
    +0x2347: xor     %edx,%esi
    +0x2349: mov     $0x173ff,%edx
    +0x234e: sub     %esi,%edx
    +0x2350: movslq  %edx,%rdx
    +0x2353: shr     $0x1f,%rdx
    +0x2357: or      %edx,%eax
    +0x2359: inc     %rcx
    +0x235c: cmp     $0x100,%rcx
    +0x2363: jne     <mldsa44_signature_internal+0x2330>
    +0x2365: test    %eax,%eax
    +0x2367: jne     <mldsa44_signature_internal+0x2510>
    +0x236d: mov     $0xc,%eax
    +0x2372: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x2380: movdqa  0x2f0(%rsp,%rax,4),%xmm0
    +0x2389: movdqa  0x300(%rsp,%rax,4),%xmm1
    +0x2392: paddd   -0x30(%rbx,%rax,4),%xmm0
    +0x2398: paddd   -0x20(%rbx,%rax,4),%xmm1
    +0x239e: movdqa  %xmm0,-0x30(%rbx,%rax,4)
    +0x23a4: movdqa  %xmm1,-0x20(%rbx,%rax,4)
    +0x23aa: movdqa  0x310(%rsp,%rax,4),%xmm0
    +0x23b3: movdqa  0x320(%rsp,%rax,4),%xmm1
    +0x23bc: paddd   -0x10(%rbx,%rax,4),%xmm0
    +0x23c2: paddd   (%rbx,%rax,4),%xmm1
    +0x23c7: movdqa  %xmm0,-0x10(%rbx,%rax,4)
    +0x23cd: movdqa  %xmm1,(%rbx,%rax,4)
    +0x23d2: add     $0x10,%rax
    +0x23d6: cmp     $0x10c,%rax
    +0x23dc: jne     <mldsa44_signature_internal+0x2380>
    +0x23de: inc     %r13
    +0x23e1: mov     0x98(%rsp),%rcx
    +0x23e9: add     $0x60,%rcx
    +0x23ed: add     $0x400,%rbx
    +0x23f4: addq    $0x1a0,0x10(%rsp)
    +0x23fd: cmp     $0x4,%r13
    +0x2401: jne     <mldsa44_signature_internal+0x1cb0>
    +0x2407: movdqa  0x200(%rsp),%xmm0
    +0x2410: movdqa  0x210(%rsp),%xmm1
    +0x2419: mov     0x8(%rsp),%rax
    +0x241e: movdqu  %xmm1,0x10(%rax)
    +0x2423: movdqu  %xmm0,(%rax)
    +0x2427: mov     0x18(%rsp),%rax
    +0x242c: pxor    %xmm0,%xmm0
    +0x2430: movdqu  %xmm0,0x40(%rax)
    +0x2435: movdqu  %xmm0,0x30(%rax)
    +0x243a: movdqu  %xmm0,0x20(%rax)
    +0x243f: movdqu  %xmm0,0x10(%rax)
    +0x2444: movdqu  %xmm0,(%rax)
    +0x2448: movl    $0x0,0x50(%rax)
    +0x244f: mov     $0x2,%eax
    +0x2454: lea     0x32c(%rsp),%rcx
    +0x245c: nopl    0x0(%rax)
    +0x2460: movzbl  0x71e(%rsp,%rax,1),%edx
    +0x2468: mov     %edx,%esi
    +0x246a: and     $0x3f,%esi
    +0x246d: mov     %esi,-0xc(%rcx)
    +0x2470: shr     $0x6,%edx
    +0x2473: movzbl  0x71f(%rsp,%rax,1),%esi
    +0x247b: mov     %esi,%edi
    +0x247d: and     $0xf,%edi
    +0x2480: lea     (%rdx,%rdi,4),%edx
    +0x2483: mov     %edx,-0x8(%rcx)
    +0x2486: shr     $0x4,%esi
    +0x2489: movzbl  0x720(%rsp,%rax,1),%edx
    +0x2491: mov     %edx,%edi
    +0x2493: shl     $0x4,%edi
    +0x2496: and     $0x30,%edi
    +0x2499: or      %esi,%edi
    +0x249b: mov     %edi,-0x4(%rcx)
    +0x249e: shr     $0x2,%edx
    +0x24a1: mov     %edx,(%rcx)
    +0x24a3: add     $0x3,%rax
    +0x24a7: add     $0x10,%rcx
    +0x24ab: cmp     $0xc2,%rax
    +0x24b1: jne     <mldsa44_signature_internal+0x2460>
    +0x24b3: xor     %eax,%eax
    +0x24b5: xor     %ecx,%ecx
    +0x24b7: xor     %r15d,%r15d
    +0x24ba: jmp     <mldsa44_signature_internal+0x24cc>
    +0x24bc: nopl    0x0(%rax)
    +0x24c0: inc     %rcx
    +0x24c3: cmp     $0x100,%rcx
    +0x24ca: je      <mldsa44_signature_internal+0x251a>
    +0x24cc: mov     0x1500(%rsp,%rcx,4),%edi
    +0x24d3: sub     $0xfffe8c00,%edi
    +0x24d9: setne   %dl
    +0x24dc: cmpl    $0x0,0x320(%rsp,%rcx,4)
    +0x24e4: sete    %sil
    +0x24e8: cmp     $0x2e800,%edi
    +0x24ee: ja      <mldsa44_signature_internal+0x24f5>
    +0x24f0: or      %sil,%dl
    +0x24f3: jne     <mldsa44_signature_internal+0x24c0>
    +0x24f5: cmp     $0x50,%eax
    +0x24f8: je      <mldsa44_signature_internal+0x2780>
    +0x24fe: mov     %eax,%edx
    +0x2500: mov     0x18(%rsp),%rsi
    +0x2505: mov     %cl,(%rsi,%rdx,1)
    +0x2508: inc     %eax
    +0x250a: jmp     <mldsa44_signature_internal+0x24c0>
    +0x250c: nopl    0x0(%rax)
    +0x2510: xor     %ebx,%ebx
    +0x2512: xor     %r15d,%r15d
    +0x2515: jmp     <mldsa44_signature_internal+0x2782>
    +0x251a: mov     0x8(%rsp),%rcx
    +0x251f: mov     %al,0x970(%rcx)
    +0x2525: lea     0x32c(%rsp),%rcx
    +0x252d: xor     %edx,%edx
    +0x252f: nop     
    +0x2530: movzbl  0x7e0(%rsp,%rdx,1),%esi
    +0x2538: mov     %esi,%edi
    +0x253a: and     $0x3f,%edi
    +0x253d: mov     %edi,-0xc(%rcx)
    +0x2540: shr     $0x6,%esi
    +0x2543: movzbl  0x7e1(%rsp,%rdx,1),%edi
    +0x254b: mov     %edi,%r8d
    +0x254e: and     $0xf,%r8d
    +0x2552: lea     (%rsi,%r8,4),%esi
    +0x2556: mov     %esi,-0x8(%rcx)
    +0x2559: shr     $0x4,%edi
    +0x255c: movzbl  0x7e2(%rsp,%rdx,1),%esi
    +0x2564: mov     %esi,%r8d
    +0x2567: shl     $0x4,%r8d
    +0x256b: and     $0x30,%r8d
    +0x256f: or      %edi,%r8d
    +0x2572: mov     %r8d,-0x4(%rcx)
    +0x2576: shr     $0x2,%esi
    +0x2579: mov     %esi,(%rcx)
    +0x257b: add     $0x3,%rdx
    +0x257f: add     $0x10,%rcx
    +0x2583: cmp     $0xc0,%rdx
    +0x258a: jne     <mldsa44_signature_internal+0x2530>
    +0x258c: xor     %ecx,%ecx
    +0x258e: jmp     <mldsa44_signature_internal+0x25b1>
    +0x2590: cmp     $0x50,%eax
    +0x2593: je      <mldsa44_signature_internal+0x2780>
    +0x2599: mov     %eax,%edx
    +0x259b: mov     0x18(%rsp),%rsi
    +0x25a0: mov     %cl,(%rsi,%rdx,1)
    +0x25a3: inc     %eax
    +0x25a5: inc     %rcx
    +0x25a8: cmp     $0x100,%rcx
    +0x25af: je      <mldsa44_signature_internal+0x25dc>
    +0x25b1: mov     0x1900(%rsp,%rcx,4),%edi
    +0x25b8: sub     $0xfffe8c00,%edi
    +0x25be: setne   %dl
    +0x25c1: cmpl    $0x0,0x320(%rsp,%rcx,4)
    +0x25c9: sete    %sil
    +0x25cd: cmp     $0x2e800,%edi
    +0x25d3: ja      <mldsa44_signature_internal+0x2590>
    +0x25d5: or      %sil,%dl
    +0x25d8: jne     <mldsa44_signature_internal+0x25a5>
    +0x25da: jmp     <mldsa44_signature_internal+0x2590>
    +0x25dc: mov     0x8(%rsp),%rcx
    +0x25e1: mov     %al,0x971(%rcx)
    +0x25e7: lea     0x32c(%rsp),%rcx
    +0x25ef: xor     %edx,%edx
    +0x25f1: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x2600: movzbl  0x8a0(%rsp,%rdx,1),%esi
    +0x2608: mov     %esi,%edi
    +0x260a: and     $0x3f,%edi
    +0x260d: mov     %edi,-0xc(%rcx)
    +0x2610: shr     $0x6,%esi
    +0x2613: movzbl  0x8a1(%rsp,%rdx,1),%edi
    +0x261b: mov     %edi,%r8d
    +0x261e: and     $0xf,%r8d
    +0x2622: lea     (%rsi,%r8,4),%esi
    +0x2626: mov     %esi,-0x8(%rcx)
    +0x2629: shr     $0x4,%edi
    +0x262c: movzbl  0x8a2(%rsp,%rdx,1),%esi
    +0x2634: mov     %esi,%r8d
    +0x2637: shl     $0x4,%r8d
    +0x263b: and     $0x30,%r8d
    +0x263f: or      %edi,%r8d
    +0x2642: mov     %r8d,-0x4(%rcx)
    +0x2646: shr     $0x2,%esi
    +0x2649: mov     %esi,(%rcx)
    +0x264b: add     $0x3,%rdx
    +0x264f: add     $0x10,%rcx
    +0x2653: cmp     $0xc0,%rdx
    +0x265a: jne     <mldsa44_signature_internal+0x2600>
    +0x265c: xor     %ecx,%ecx
    +0x265e: jmp     <mldsa44_signature_internal+0x266c>
    +0x2660: inc     %rcx
    +0x2663: cmp     $0x100,%rcx
    +0x266a: je      <mldsa44_signature_internal+0x26ac>
    +0x266c: mov     0x1d00(%rsp,%rcx,4),%edi
    +0x2673: sub     $0xfffe8c00,%edi
    +0x2679: setne   %dl
    +0x267c: cmpl    $0x0,0x320(%rsp,%rcx,4)
    +0x2684: sete    %sil
    +0x2688: cmp     $0x2e800,%edi
    +0x268e: ja      <mldsa44_signature_internal+0x2695>
    +0x2690: or      %sil,%dl
    +0x2693: jne     <mldsa44_signature_internal+0x2660>
    +0x2695: cmp     $0x50,%eax
    +0x2698: je      <mldsa44_signature_internal+0x2780>
    +0x269e: mov     %eax,%edx
    +0x26a0: mov     0x18(%rsp),%rsi
    +0x26a5: mov     %cl,(%rsi,%rdx,1)
    +0x26a8: inc     %eax
    +0x26aa: jmp     <mldsa44_signature_internal+0x2660>
    +0x26ac: mov     0x8(%rsp),%rcx
    +0x26b1: mov     %al,0x972(%rcx)
    +0x26b7: lea     0x32c(%rsp),%rcx
    +0x26bf: xor     %edx,%edx
    +0x26c1: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x26d0: movzbl  0x960(%rsp,%rdx,1),%esi
    +0x26d8: mov     %esi,%edi
    +0x26da: and     $0x3f,%edi
    +0x26dd: mov     %edi,-0xc(%rcx)
    +0x26e0: shr     $0x6,%esi
    +0x26e3: movzbl  0x961(%rsp,%rdx,1),%edi
    +0x26eb: mov     %edi,%r8d
    +0x26ee: and     $0xf,%r8d
    +0x26f2: lea     (%rsi,%r8,4),%esi
    +0x26f6: mov     %esi,-0x8(%rcx)
    +0x26f9: shr     $0x4,%edi
    +0x26fc: movzbl  0x962(%rsp,%rdx,1),%esi
    +0x2704: mov     %esi,%r8d
    +0x2707: shl     $0x4,%r8d
    +0x270b: and     $0x30,%r8d
    +0x270f: or      %edi,%r8d
    +0x2712: mov     %r8d,-0x4(%rcx)
    +0x2716: shr     $0x2,%esi
    +0x2719: mov     %esi,(%rcx)
    +0x271b: add     $0x3,%rdx
    +0x271f: add     $0x10,%rcx
    +0x2723: cmp     $0xc0,%rdx
    +0x272a: jne     <mldsa44_signature_internal+0x26d0>
    +0x272c: xor     %ecx,%ecx
    +0x272e: jmp     <mldsa44_signature_internal+0x2751>
    +0x2730: cmp     $0x50,%eax
    +0x2733: je      <mldsa44_signature_internal+0x2780>
    +0x2735: mov     %eax,%edx
    +0x2737: mov     0x18(%rsp),%rsi
    +0x273c: mov     %cl,(%rsi,%rdx,1)
    +0x273f: inc     %eax
    +0x2741: inc     %rcx
    +0x2744: cmp     $0x100,%rcx
    +0x274b: je      <mldsa44_signature_internal+0x2842>
    +0x2751: mov     0x2100(%rsp,%rcx,4),%edi
    +0x2758: sub     $0xfffe8c00,%edi
    +0x275e: setne   %dl
    +0x2761: cmpl    $0x0,0x320(%rsp,%rcx,4)
    +0x2769: sete    %sil
    +0x276d: cmp     $0x2e800,%edi
    +0x2773: ja      <mldsa44_signature_internal+0x2730>
    +0x2775: or      %sil,%dl
    +0x2778: jne     <mldsa44_signature_internal+0x2741>
    +0x277a: jmp     <mldsa44_signature_internal+0x2730>
    +0x277c: nopl    0x0(%rax)
    +0x2780: xor     %ebx,%ebx
    +0x2782: mov     $0x400,%edx
    +0x2787: lea     0xce0(%rsp),%r14
    +0x278f: mov     %r14,%rdi
    +0x2792: xor     %esi,%esi
    +0x2794: call    <memset>
    +0x2799: mov     $0x400,%edx
    +0x279e: lea     0x2500(%rsp),%r14
    +0x27a6: mov     %r14,%rdi
    +0x27a9: xor     %esi,%esi
    +0x27ab: call    <memset>
    +0x27b0: mov     $0x1000,%edx
    +0x27b5: lea     0x1500(%rsp),%r14
    +0x27bd: mov     %r14,%rdi
    +0x27c0: xor     %esi,%esi
    +0x27c2: call    <memset>
    +0x27c7: mov     $0x300,%edx
    +0x27cc: lea     0x720(%rsp),%r14
    +0x27d4: mov     %r14,%rdi
    +0x27d7: xor     %esi,%esi
    +0x27d9: call    <memset>
    +0x27de: mov     $0x400,%edx
    +0x27e3: lea     0x320(%rsp),%r14
    +0x27eb: mov     %r14,%rdi
    +0x27ee: xor     %esi,%esi
    +0x27f0: call    <memset>
    +0x27f5: pxor    %xmm0,%xmm0
    +0x27f9: movdqa  %xmm0,0x80(%rsp)
    +0x2802: lea     0x80(%rsp),%rax
    +0x280a: movdqa  %xmm0,0x210(%rsp)
    +0x2813: movdqa  %xmm0,0x200(%rsp)
    +0x281c: lea     0x200(%rsp),%rax
    +0x2824: test    %bl,%bl
    +0x2826: jne     <mldsa44_signature_internal+0x286e>
    +0x2828: mov     0x190(%rsp),%rcx
    +0x2830: inc     %ecx
    +0x2832: movzwl  %cx,%eax
    +0x2835: cmp     $0x3ffe,%eax
    +0x283a: jne     <mldsa44_signature_internal+0x1b0>
    +0x2840: jmp     <mldsa44_signature_internal+0x2854>
    +0x2842: mov     0x8(%rsp),%rcx
    +0x2847: mov     %al,0x973(%rcx)
    +0x284d: mov     $0x1,%bl
    +0x284f: jmp     <mldsa44_signature_internal+0x2782>
    +0x2854: mov     $0x974,%edx
    +0x2859: mov     0x8(%rsp),%rbx
    +0x285e: mov     %rbx,%rdi
    +0x2861: xor     %esi,%esi
    +0x2863: call    <memset>
    +0x2868: mov     $0xfffffffc,%r15d
    +0x286e: movq    $0x0,0x20(%rsp)
    +0x2877: lea     0x20(%rsp),%rax
    +0x287c: movq    $0x0,0x40(%rsp)
    +0x2885: lea     0x40(%rsp),%rax
    +0x288a: movq    $0x0,0x60(%rsp)
    +0x2893: lea     0x60(%rsp),%rax
    +0x2898: lea     0x10e0(%rsp),%r14
    +0x28a0: mov     $0x420,%edx
    +0x28a5: mov     %r14,%rdi
    +0x28a8: xor     %esi,%esi
    +0x28aa: call    <memset>
    +0x28af: pxor    %xmm0,%xmm0
    +0x28b3: movdqa  %xmm0,0x310(%rsp)
    +0x28bc: movdqa  %xmm0,0x300(%rsp)
    +0x28c5: movdqa  %xmm0,0x2f0(%rsp)
    +0x28ce: movdqa  %xmm0,0x2e0(%rsp)
    +0x28d7: movdqa  %xmm0,0x2d0(%rsp)
    +0x28e0: movdqa  %xmm0,0x2c0(%rsp)
    +0x28e9: movdqa  %xmm0,0x2b0(%rsp)
    +0x28f2: movdqa  %xmm0,0x2a0(%rsp)
    +0x28fb: movdqa  %xmm0,0x290(%rsp)
    +0x2904: movdqa  %xmm0,0x280(%rsp)
    +0x290d: movdqa  %xmm0,0x270(%rsp)
    +0x2916: movdqa  %xmm0,0x260(%rsp)
    +0x291f: movdqa  %xmm0,0x250(%rsp)
    +0x2928: movdqa  %xmm0,0x240(%rsp)
    +0x2931: movdqa  %xmm0,0x230(%rsp)
    +0x293a: movdqa  %xmm0,0x220(%rsp)
    +0x2943: lea     0x220(%rsp),%rax
    +0x294b: mov     %r15d,%eax
    +0x294e: lea     -0x28(%rbp),%rsp
    +0x2952: pop     %rbx
    +0x2953: pop     %r12
    +0x2955: pop     %r13
    +0x2957: pop     %r14
    +0x2959: pop     %r15
    +0x295b: pop     %rbp
    +0x295c: xor     %ecx,%ecx
    +0x295e: xor     %edi,%edi
    +0x2960: xor     %edx,%edx
    +0x2962: xor     %esi,%esi
    +0x2964: xor     %r8d,%r8d
    +0x2967: xor     %r9d,%r9d
    +0x296a: xor     %r10d,%r10d
    +0x296d: xor     %r11d,%r11d
    +0x2970: ret     
 ***)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_signature_internal";
    layout_range "plt_memcpy";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* secret key skb at sk (2560 bytes), the message M of mlen bytes at m and   *)
(* the prefix PRE of prelen bytes at pre (or, if ext is nonzero as a 32-bit  *)
(* integer, mu in the first 64 bytes at m), and the 32 bytes RND at rnd,     *)
(* with MU the mu that the code uses: the result is 0, with the signature    *)
(* mld_sign_sig_44 at sig (2420 bytes), if one of the 16382 attempts         *)
(* succeeds (mld_sign_ok_44), and -4 with the signature zeroed otherwise.    *)
(* The last two arguments, sk and ext, are on the stack above the return     *)
(* address, sk as a 64-bit word and ext as a 32-bit one. The function aligns *)
(* the stack pointer down to a multiple of 32, which may lower it by up to   *)
(* 31 bytes, saves RBP, the frame pointer, and five more registers, and      *)
(* reserves its buffers, below which the callees use theirs: 12078 bytes of  *)
(* stack below the return address in all (the figure of stackx.py, which     *)
(* counts the red zone that mldsa_keccakf1600_permute writes below RSP). The *)
(* GOT entries of memset and memcpy, which the PLT stubs read, and the       *)
(* region (ea,el) that they may read are apart from the signature and the    *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
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
          mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
          mld_sign_terminates_44 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 12078),12078)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 12078),12078)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,2420) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa44_signature_internal) /\
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
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mld_sign_ok_44 skb MU RND
                     then word 0 else word 4294967292) /\
                    (!t. t < 2420
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             mld_sign_sig_44 skb MU RND t))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 12078),12078)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

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

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
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
          mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
          mld_sign_terminates_44 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 12078),12078)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 12078),12078)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,2420) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa44_signature_internal) /\
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
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mld_sign_ok_44 skb MU RND
                     then word 0 else word 4294967292) /\
                    (!t. t < 2420
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             mld_sign_sig_44 skb MU RND t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen rnd sk ext
                             (mld_sk_rho skb)
                             (mld_sign_declass_44 skb MU RND)
                             mf mc pc (word_sub stackpointer (word 12078))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; pre,prelen; rnd,32; sk,2560;
                         word_sub stackpointer (word 12078),12078;
                         stackpointer,8; word_add stackpointer (word 8),16;
                         word(pc + got_memset),8;
                          word(pc + got_memcpy),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa44_poly_challenge_consts),64;
                          word(pc + mldsa44_signature_internal_consts),32;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448]
                        [sig,2420;
                         word_sub stackpointer (word 12078),12078]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 12078),12078)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
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
          mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
          mld_sign_terminates_44 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 12078),12078)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 12078),12078)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,2420) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa44_signature_internal) /\
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
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen rnd sk ext
                             (mld_sk_rho skb)
                             (mld_sign_declass_44 skb MU RND)
                             mf mc pc (word_sub stackpointer (word 12078))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; pre,prelen; rnd,32; sk,2560;
                         word_sub stackpointer (word 12078),12078;
                         stackpointer,8; word_add stackpointer (word 8),16;
                         word(pc + got_memset),8;
                          word(pc + got_memcpy),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa44_poly_challenge_consts),64;
                          word(pc + mldsa44_signature_internal_consts),32;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448]
                        [sig,2420;
                         word_sub stackpointer (word 12078),12078]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 12078),12078)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
