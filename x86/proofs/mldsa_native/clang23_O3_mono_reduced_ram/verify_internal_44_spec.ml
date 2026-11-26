(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the statement. This is the code for          *)
(* mldsa44_verify_internal (mld_sign_verify_internal in sign.c) from         *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3    *)
(* and MLD_CONFIG_REDUCE_RAM as one translation unit (see                    *)
(* mldsa_native/README.md). Clang has inlined most of its callees, so the    *)
(* function itself unpacks z with four loops and checks its norm with a call *)
(* of mldsa44_polyvecl_chknorm, computes mu (or takes it from m if ext is    *)
(* nonzero) with the inline absorption of the public key and a call of       *)
(* mld_H44, transforms z with calls of mldsa_poly_ntt, copies rho into the   *)
(* structure of the matrix, whose entries are sampled when they are needed,  *)
(* and computes the challenge from c~ with mldsa44_poly_challenge. For each  *)
(* row it computes w1' = UseHint(h, A z - c t1 2^d) with a call of           *)
(* mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy and inlined loops   *)
(* for the unpacking of t1 and of the hints, the multiplication, the         *)
(* subtraction, the reduction and the use of the hints, and calls of         *)
(* mldsa_poly_ntt and mldsa_poly_invntt_tomont, packs it, and compares c~ with *)
(* mld_H44 of mu and w1'. It zeroes its buffers at the end with SSE stores   *)
(* and memset, which it calls through the PLT, so the direction flag must be *)
(* clear, as the ABI requires on entry. It is verified in the whole image    *)
(* (see libmldsa.ml) against mld_verify_internal_ok of                       *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and the   *)
(* contracts memset_full_contract and memcpy_full_contract of                *)
(* utils/mldsa_native_libc.ml, with the lemmas of inline_sign.ml for the     *)
(* inlined loops, assuming that the expansion of the matrix and the sampling *)
(* of the challenge terminate, and shown to be constant time and memory      *)
(* safe, with events depending on the signature, the message, the prefix and *)
(* the public key, which are all public.                                     *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvecl_chknorm_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_challenge_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/H_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_verify_internal:
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
      +0x2f: sub     $0x420,%rsp
      +0x36: mov     %r9,%rbx
      +0x39: mov     %r8,0x28(%rsp)
      +0x3e: mov     %rcx,0x30(%rsp)
      +0x43: mov     %rdx,%r13
      +0x46: mov     %rsi,%r12
      +0x49: mov     %rdi,%r10
      +0x4c: mov     0x10(%rbp),%r15d
      +0x50: movdqu  (%rdi),%xmm0
      +0x54: movdqu  0x10(%rdi),%xmm1
      +0x59: movdqa  %xmm0,0x40(%rsp)
      +0x5f: movdqa  %xmm1,0x50(%rsp)
      +0x65: lea     0x28(%rdi),%rax
      +0x69: mov     $0xc,%ecx
      +0x6e: xchg    %ax,%ax
      +0x70: movzwl  -0x8(%rax),%esi
      +0x74: movzbl  -0x6(%rax),%edi
      +0x78: mov     %edi,%edx
      +0x7a: and     $0x3,%edx
      +0x7d: shl     $0x10,%edx
      +0x80: or      %esi,%edx
      +0x82: shr     $0x2,%edi
      +0x85: movzbl  -0x5(%rax),%r8d
      +0x8a: shl     $0x6,%r8d
      +0x8e: or      %edi,%r8d
      +0x91: movzbl  -0x4(%rax),%edi
      +0x95: mov     %edi,%esi
      +0x97: and     $0xf,%esi
      +0x9a: shl     $0xe,%esi
      +0x9d: or      %r8d,%esi
      +0xa0: shr     $0x4,%edi
      +0xa3: movzbl  -0x3(%rax),%r8d
      +0xa8: shl     $0x4,%r8d
      +0xac: or      %edi,%r8d
      +0xaf: movzbl  -0x2(%rax),%edi
      +0xb3: mov     %edi,%r9d
      +0xb6: and     $0x3f,%r9d
      +0xba: shl     $0xc,%r9d
      +0xbe: or      %r8d,%r9d
      +0xc1: shr     $0x6,%edi
      +0xc4: movzbl  -0x1(%rax),%r8d
      +0xc9: lea     (%rdi,%r8,4),%edi
      +0xcd: movzbl  (%rax),%r8d
      +0xd1: shl     $0xa,%r8d
      +0xd5: or      %edi,%r8d
      +0xd8: mov     $0x20000,%edi
      +0xdd: sub     %edx,%edi
      +0xdf: mov     %edi,0x10d4(%rsp,%rcx,1)
      +0xe6: mov     $0x20000,%edx
      +0xeb: sub     %esi,%edx
      +0xed: mov     %edx,0x10d8(%rsp,%rcx,1)
      +0xf4: mov     $0x20000,%edx
      +0xf9: sub     %r9d,%edx
      +0xfc: mov     %edx,0x10dc(%rsp,%rcx,1)
     +0x103: mov     $0x20000,%edx
     +0x108: sub     %r8d,%edx
     +0x10b: mov     %edx,0x10e0(%rsp,%rcx,1)
     +0x112: add     $0x10,%rcx
     +0x116: add     $0x9,%rax
     +0x11a: cmp     $0x40c,%rcx
     +0x121: jne     <mldsa44_verify_internal+0x70>
     +0x127: lea     0x14e0(%rsp),%r14
     +0x12f: lea     0x268(%r10),%rax
     +0x136: mov     $0x40c,%ecx
     +0x13b: nopl    0x0(%rax,%rax,1)
     +0x140: movzwl  -0x8(%rax),%esi
     +0x144: movzbl  -0x6(%rax),%edi
     +0x148: mov     %edi,%edx
     +0x14a: and     $0x3,%edx
     +0x14d: shl     $0x10,%edx
     +0x150: or      %esi,%edx
     +0x152: shr     $0x2,%edi
     +0x155: movzbl  -0x5(%rax),%r8d
     +0x15a: shl     $0x6,%r8d
     +0x15e: or      %edi,%r8d
     +0x161: movzbl  -0x4(%rax),%edi
     +0x165: mov     %edi,%esi
     +0x167: and     $0xf,%esi
     +0x16a: shl     $0xe,%esi
     +0x16d: or      %r8d,%esi
     +0x170: shr     $0x4,%edi
     +0x173: movzbl  -0x3(%rax),%r8d
     +0x178: shl     $0x4,%r8d
     +0x17c: or      %edi,%r8d
     +0x17f: movzbl  -0x2(%rax),%edi
     +0x183: mov     %edi,%r9d
     +0x186: and     $0x3f,%r9d
     +0x18a: shl     $0xc,%r9d
     +0x18e: or      %r8d,%r9d
     +0x191: shr     $0x6,%edi
     +0x194: movzbl  -0x1(%rax),%r8d
     +0x199: lea     (%rdi,%r8,4),%edi
     +0x19d: movzbl  (%rax),%r8d
     +0x1a1: shl     $0xa,%r8d
     +0x1a5: or      %edi,%r8d
     +0x1a8: mov     $0x20000,%edi
     +0x1ad: sub     %edx,%edi
     +0x1af: mov     %edi,0x10d4(%rsp,%rcx,1)
     +0x1b6: mov     $0x20000,%edx
     +0x1bb: sub     %esi,%edx
     +0x1bd: mov     %edx,0x10d8(%rsp,%rcx,1)
     +0x1c4: mov     $0x20000,%edx
     +0x1c9: sub     %r9d,%edx
     +0x1cc: mov     %edx,0x10dc(%rsp,%rcx,1)
     +0x1d3: mov     $0x20000,%edx
     +0x1d8: sub     %r8d,%edx
     +0x1db: mov     %edx,0x10e0(%rsp,%rcx,1)
     +0x1e2: add     $0x10,%rcx
     +0x1e6: add     $0x9,%rax
     +0x1ea: cmp     $0x80c,%rcx
     +0x1f1: jne     <mldsa44_verify_internal+0x140>
     +0x1f7: lea     0x4a8(%r10),%rax
     +0x1fe: mov     $0x80c,%ecx
     +0x203: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x210: movzwl  -0x8(%rax),%esi
     +0x214: movzbl  -0x6(%rax),%edi
     +0x218: mov     %edi,%edx
     +0x21a: and     $0x3,%edx
     +0x21d: shl     $0x10,%edx
     +0x220: or      %esi,%edx
     +0x222: shr     $0x2,%edi
     +0x225: movzbl  -0x5(%rax),%r8d
     +0x22a: shl     $0x6,%r8d
     +0x22e: or      %edi,%r8d
     +0x231: movzbl  -0x4(%rax),%edi
     +0x235: mov     %edi,%esi
     +0x237: and     $0xf,%esi
     +0x23a: shl     $0xe,%esi
     +0x23d: or      %r8d,%esi
     +0x240: shr     $0x4,%edi
     +0x243: movzbl  -0x3(%rax),%r8d
     +0x248: shl     $0x4,%r8d
     +0x24c: or      %edi,%r8d
     +0x24f: movzbl  -0x2(%rax),%edi
     +0x253: mov     %edi,%r9d
     +0x256: and     $0x3f,%r9d
     +0x25a: shl     $0xc,%r9d
     +0x25e: or      %r8d,%r9d
     +0x261: shr     $0x6,%edi
     +0x264: movzbl  -0x1(%rax),%r8d
     +0x269: lea     (%rdi,%r8,4),%edi
     +0x26d: movzbl  (%rax),%r8d
     +0x271: shl     $0xa,%r8d
     +0x275: or      %edi,%r8d
     +0x278: mov     $0x20000,%edi
     +0x27d: sub     %edx,%edi
     +0x27f: mov     %edi,0x10d4(%rsp,%rcx,1)
     +0x286: mov     $0x20000,%edx
     +0x28b: sub     %esi,%edx
     +0x28d: mov     %edx,0x10d8(%rsp,%rcx,1)
     +0x294: mov     $0x20000,%edx
     +0x299: sub     %r9d,%edx
     +0x29c: mov     %edx,0x10dc(%rsp,%rcx,1)
     +0x2a3: mov     $0x20000,%edx
     +0x2a8: sub     %r8d,%edx
     +0x2ab: mov     %edx,0x10e0(%rsp,%rcx,1)
     +0x2b2: add     $0x10,%rcx
     +0x2b6: add     $0x9,%rax
     +0x2ba: cmp     $0xc0c,%rcx
     +0x2c1: jne     <mldsa44_verify_internal+0x210>
     +0x2c7: mov     %r10,0x38(%rsp)
     +0x2cc: lea     0x6e8(%r10),%rax
     +0x2d3: mov     $0xc0c,%ecx
     +0x2d8: nopl    0x0(%rax,%rax,1)
     +0x2e0: movzwl  -0x8(%rax),%esi
     +0x2e4: movzbl  -0x6(%rax),%edi
     +0x2e8: mov     %edi,%edx
     +0x2ea: and     $0x3,%edx
     +0x2ed: shl     $0x10,%edx
     +0x2f0: or      %esi,%edx
     +0x2f2: shr     $0x2,%edi
     +0x2f5: movzbl  -0x5(%rax),%r8d
     +0x2fa: shl     $0x6,%r8d
     +0x2fe: or      %edi,%r8d
     +0x301: movzbl  -0x4(%rax),%edi
     +0x305: mov     %edi,%esi
     +0x307: and     $0xf,%esi
     +0x30a: shl     $0xe,%esi
     +0x30d: or      %r8d,%esi
     +0x310: shr     $0x4,%edi
     +0x313: movzbl  -0x3(%rax),%r8d
     +0x318: shl     $0x4,%r8d
     +0x31c: or      %edi,%r8d
     +0x31f: movzbl  -0x2(%rax),%edi
     +0x323: mov     %edi,%r9d
     +0x326: and     $0x3f,%r9d
     +0x32a: shl     $0xc,%r9d
     +0x32e: or      %r8d,%r9d
     +0x331: shr     $0x6,%edi
     +0x334: movzbl  -0x1(%rax),%r8d
     +0x339: lea     (%rdi,%r8,4),%edi
     +0x33d: movzbl  (%rax),%r8d
     +0x341: shl     $0xa,%r8d
     +0x345: or      %edi,%r8d
     +0x348: mov     $0x20000,%edi
     +0x34d: sub     %edx,%edi
     +0x34f: mov     %edi,0x10d4(%rsp,%rcx,1)
     +0x356: mov     $0x20000,%edx
     +0x35b: sub     %esi,%edx
     +0x35d: mov     %edx,0x10d8(%rsp,%rcx,1)
     +0x364: mov     $0x20000,%edx
     +0x369: sub     %r9d,%edx
     +0x36c: mov     %edx,0x10dc(%rsp,%rcx,1)
     +0x373: mov     $0x20000,%edx
     +0x378: sub     %r8d,%edx
     +0x37b: mov     %edx,0x10e0(%rsp,%rcx,1)
     +0x382: add     $0x10,%rcx
     +0x386: add     $0x9,%rax
     +0x38a: cmp     $0x100c,%rcx
     +0x391: jne     <mldsa44_verify_internal+0x2e0>
     +0x397: lea     0x10e0(%rsp),%rdi
     +0x39f: mov     $0x1ffb2,%esi
     +0x3a4: call    <mldsa44_polyvecl_chknorm>
     +0x3a9: test    %eax,%eax
     +0x3ab: je      <mldsa44_verify_internal+0x4b6>
     +0x3b1: mov     $0xfffffffa,%r14d
     +0x3b7: lea     0x4e0(%rsp),%rbx
     +0x3bf: mov     $0x400,%edx
     +0x3c4: mov     %rbx,%rdi
     +0x3c7: xor     %esi,%esi
     +0x3c9: call    <memset>
     +0x3ce: lea     0x8e0(%rsp),%rbx
     +0x3d6: mov     $0x400,%edx
     +0x3db: mov     %rbx,%rdi
     +0x3de: xor     %esi,%esi
     +0x3e0: call    <memset>
     +0x3e5: lea     0x80(%rsp),%rbx
     +0x3ed: mov     $0x420,%edx
     +0x3f2: mov     %rbx,%rdi
     +0x3f5: xor     %esi,%esi
     +0x3f7: call    <memset>
     +0x3fc: lea     0xce0(%rsp),%rbx
     +0x404: mov     $0x400,%edx
     +0x409: mov     %rbx,%rdi
     +0x40c: xor     %esi,%esi
     +0x40e: call    <memset>
     +0x413: lea     0x10e0(%rsp),%rbx
     +0x41b: mov     $0x1000,%edx
     +0x420: mov     %rbx,%rdi
     +0x423: xor     %esi,%esi
     +0x425: call    <memset>
     +0x42a: pxor    %xmm0,%xmm0
     +0x42e: movdqa  %xmm0,0x70(%rsp)
     +0x434: movdqa  %xmm0,0x60(%rsp)
     +0x43a: lea     0x60(%rsp),%rax
     +0x43f: movdqa  %xmm0,0x50(%rsp)
     +0x445: movdqa  %xmm0,0x40(%rsp)
     +0x44b: lea     0x40(%rsp),%rax
     +0x450: movdqa  %xmm0,0x4d0(%rsp)
     +0x459: movdqa  %xmm0,0x4c0(%rsp)
     +0x462: movdqa  %xmm0,0x4b0(%rsp)
     +0x46b: movdqa  %xmm0,0x4a0(%rsp)
     +0x474: lea     0x4a0(%rsp),%rax
     +0x47c: lea     0x20e0(%rsp),%rbx
     +0x484: mov     $0x300,%edx
     +0x489: mov     %rbx,%rdi
     +0x48c: xor     %esi,%esi
     +0x48e: call    <memset>
     +0x493: mov     %r14d,%eax
     +0x496: lea     -0x28(%rbp),%rsp
     +0x49a: pop     %rbx
     +0x49b: pop     %r12
     +0x49d: pop     %r13
     +0x49f: pop     %r14
     +0x4a1: pop     %r15
     +0x4a3: pop     %rbp
     +0x4a4: xor     %ecx,%ecx
     +0x4a6: xor     %edi,%edi
     +0x4a8: xor     %edx,%edx
     +0x4aa: xor     %esi,%esi
     +0x4ac: xor     %r8d,%r8d
     +0x4af: xor     %r9d,%r9d
     +0x4b2: xor     %r10d,%r10d
     +0x4b5: ret     
     +0x4b6: test    %r15d,%r15d
     +0x4b9: je      <mldsa44_verify_internal+0x4fb>
     +0x4bb: movups  (%r12),%xmm0
     +0x4c0: movups  0x10(%r12),%xmm1
     +0x4c6: movdqu  0x20(%r12),%xmm2
     +0x4cd: movdqu  0x30(%r12),%xmm3
     +0x4d4: movdqa  %xmm3,0x4d0(%rsp)
     +0x4dd: movdqa  %xmm2,0x4c0(%rsp)
     +0x4e6: movaps  %xmm1,0x4b0(%rsp)
     +0x4ee: movaps  %xmm0,0x4a0(%rsp)
     +0x4f6: jmp     <mldsa44_verify_internal+0xec1>
     +0x4fb: pxor    %xmm0,%xmm0
     +0x4ff: movdqu  %xmm0,0x13c(%rsp)
     +0x508: movdqa  %xmm0,0x130(%rsp)
     +0x511: movdqa  %xmm0,0x120(%rsp)
     +0x51a: movdqa  %xmm0,0x110(%rsp)
     +0x523: movdqa  %xmm0,0x100(%rsp)
     +0x52c: movdqa  %xmm0,0xf0(%rsp)
     +0x535: movdqa  %xmm0,0xe0(%rsp)
     +0x53e: movdqa  %xmm0,0xd0(%rsp)
     +0x547: movdqa  %xmm0,0xc0(%rsp)
     +0x550: movdqa  %xmm0,0xb0(%rsp)
     +0x559: movdqa  %xmm0,0xa0(%rsp)
     +0x562: movdqa  %xmm0,0x90(%rsp)
     +0x56b: movdqa  %xmm0,0x80(%rsp)
     +0x574: movups  (%rbx),%xmm0
     +0x577: movups  0x10(%rbx),%xmm1
     +0x57b: movaps  %xmm0,0x80(%rsp)
     +0x583: movaps  %xmm1,0x90(%rsp)
     +0x58b: movups  0x20(%rbx),%xmm0
     +0x58f: movups  0x30(%rbx),%xmm1
     +0x593: movaps  %xmm0,0xa0(%rsp)
     +0x59b: movaps  %xmm1,0xb0(%rsp)
     +0x5a3: movups  0x40(%rbx),%xmm0
     +0x5a7: movups  0x50(%rbx),%xmm1
     +0x5ab: xorps   0xc0(%rsp),%xmm0
     +0x5b3: xorps   0xd0(%rsp),%xmm1
     +0x5bb: movaps  %xmm0,0xc0(%rsp)
     +0x5c3: movaps  %xmm1,0xd0(%rsp)
     +0x5cb: movups  0x60(%rbx),%xmm0
     +0x5cf: movups  0x70(%rbx),%xmm1
     +0x5d3: xorps   0xe0(%rsp),%xmm0
     +0x5db: xorps   0xf0(%rsp),%xmm1
     +0x5e3: movaps  %xmm0,0xe0(%rsp)
     +0x5eb: movaps  %xmm1,0xf0(%rsp)
     +0x5f3: mov     0x80(%rbx),%rax
     +0x5fa: xor     %rax,0x100(%rsp)
     +0x602: lea     0x80(%rsp),%r15
     +0x60a: mov     %r15,%rdi
     +0x60d: call    <mldsa_keccakf1600_permute>
     +0x612: movups  0x88(%rbx),%xmm0
     +0x619: movups  0x98(%rbx),%xmm1
     +0x620: xorps   0x80(%rsp),%xmm0
     +0x628: xorps   0x90(%rsp),%xmm1
     +0x630: movaps  %xmm0,0x80(%rsp)
     +0x638: movaps  %xmm1,0x90(%rsp)
     +0x640: movups  0xa8(%rbx),%xmm0
     +0x647: movups  0xb8(%rbx),%xmm1
     +0x64e: xorps   0xa0(%rsp),%xmm0
     +0x656: xorps   0xb0(%rsp),%xmm1
     +0x65e: movaps  %xmm0,0xa0(%rsp)
     +0x666: movaps  %xmm1,0xb0(%rsp)
     +0x66e: movups  0xc8(%rbx),%xmm0
     +0x675: movups  0xd8(%rbx),%xmm1
     +0x67c: xorps   0xc0(%rsp),%xmm0
     +0x684: xorps   0xd0(%rsp),%xmm1
     +0x68c: movaps  %xmm0,0xc0(%rsp)
     +0x694: movaps  %xmm1,0xd0(%rsp)
     +0x69c: movups  0xe8(%rbx),%xmm0
     +0x6a3: movups  0xf8(%rbx),%xmm1
     +0x6aa: xorps   0xe0(%rsp),%xmm0
     +0x6b2: xorps   0xf0(%rsp),%xmm1
     +0x6ba: movaps  %xmm0,0xe0(%rsp)
     +0x6c2: movaps  %xmm1,0xf0(%rsp)
     +0x6ca: mov     0x108(%rbx),%rax
     +0x6d1: xor     %rax,0x100(%rsp)
     +0x6d9: mov     %r15,%rdi
     +0x6dc: call    <mldsa_keccakf1600_permute>
     +0x6e1: movups  0x110(%rbx),%xmm0
     +0x6e8: movups  0x120(%rbx),%xmm1
     +0x6ef: xorps   0x80(%rsp),%xmm0
     +0x6f7: xorps   0x90(%rsp),%xmm1
     +0x6ff: movaps  %xmm0,0x80(%rsp)
     +0x707: movaps  %xmm1,0x90(%rsp)
     +0x70f: movups  0x130(%rbx),%xmm0
     +0x716: movups  0x140(%rbx),%xmm1
     +0x71d: xorps   0xa0(%rsp),%xmm0
     +0x725: xorps   0xb0(%rsp),%xmm1
     +0x72d: movaps  %xmm0,0xa0(%rsp)
     +0x735: movaps  %xmm1,0xb0(%rsp)
     +0x73d: movups  0x150(%rbx),%xmm0
     +0x744: movups  0x160(%rbx),%xmm1
     +0x74b: xorps   0xc0(%rsp),%xmm0
     +0x753: xorps   0xd0(%rsp),%xmm1
     +0x75b: movaps  %xmm0,0xc0(%rsp)
     +0x763: movaps  %xmm1,0xd0(%rsp)
     +0x76b: movups  0x170(%rbx),%xmm0
     +0x772: movups  0x180(%rbx),%xmm1
     +0x779: xorps   0xe0(%rsp),%xmm0
     +0x781: xorps   0xf0(%rsp),%xmm1
     +0x789: movaps  %xmm0,0xe0(%rsp)
     +0x791: movaps  %xmm1,0xf0(%rsp)
     +0x799: mov     0x190(%rbx),%rax
     +0x7a0: xor     %rax,0x100(%rsp)
     +0x7a8: mov     %r15,%rdi
     +0x7ab: call    <mldsa_keccakf1600_permute>
     +0x7b0: movups  0x198(%rbx),%xmm0
     +0x7b7: movups  0x1a8(%rbx),%xmm1
     +0x7be: xorps   0x80(%rsp),%xmm0
     +0x7c6: xorps   0x90(%rsp),%xmm1
     +0x7ce: movaps  %xmm0,0x80(%rsp)
     +0x7d6: movaps  %xmm1,0x90(%rsp)
     +0x7de: movups  0x1b8(%rbx),%xmm0
     +0x7e5: movups  0x1c8(%rbx),%xmm1
     +0x7ec: xorps   0xa0(%rsp),%xmm0
     +0x7f4: xorps   0xb0(%rsp),%xmm1
     +0x7fc: movaps  %xmm0,0xa0(%rsp)
     +0x804: movaps  %xmm1,0xb0(%rsp)
     +0x80c: movups  0x1d8(%rbx),%xmm0
     +0x813: movups  0x1e8(%rbx),%xmm1
     +0x81a: xorps   0xc0(%rsp),%xmm0
     +0x822: xorps   0xd0(%rsp),%xmm1
     +0x82a: movaps  %xmm0,0xc0(%rsp)
     +0x832: movaps  %xmm1,0xd0(%rsp)
     +0x83a: movups  0x1f8(%rbx),%xmm0
     +0x841: movups  0x208(%rbx),%xmm1
     +0x848: xorps   0xe0(%rsp),%xmm0
     +0x850: xorps   0xf0(%rsp),%xmm1
     +0x858: movaps  %xmm0,0xe0(%rsp)
     +0x860: movaps  %xmm1,0xf0(%rsp)
     +0x868: mov     0x218(%rbx),%rax
     +0x86f: xor     %rax,0x100(%rsp)
     +0x877: mov     %r15,%rdi
     +0x87a: call    <mldsa_keccakf1600_permute>
     +0x87f: movups  0x220(%rbx),%xmm0
     +0x886: movups  0x230(%rbx),%xmm1
     +0x88d: xorps   0x80(%rsp),%xmm0
     +0x895: xorps   0x90(%rsp),%xmm1
     +0x89d: movaps  %xmm0,0x80(%rsp)
     +0x8a5: movaps  %xmm1,0x90(%rsp)
     +0x8ad: movups  0x240(%rbx),%xmm0
     +0x8b4: movups  0x250(%rbx),%xmm1
     +0x8bb: xorps   0xa0(%rsp),%xmm0
     +0x8c3: xorps   0xb0(%rsp),%xmm1
     +0x8cb: movaps  %xmm0,0xa0(%rsp)
     +0x8d3: movaps  %xmm1,0xb0(%rsp)
     +0x8db: movups  0x260(%rbx),%xmm0
     +0x8e2: movups  0x270(%rbx),%xmm1
     +0x8e9: xorps   0xc0(%rsp),%xmm0
     +0x8f1: xorps   0xd0(%rsp),%xmm1
     +0x8f9: movaps  %xmm0,0xc0(%rsp)
     +0x901: movaps  %xmm1,0xd0(%rsp)
     +0x909: movups  0x280(%rbx),%xmm0
     +0x910: movups  0x290(%rbx),%xmm1
     +0x917: xorps   0xe0(%rsp),%xmm0
     +0x91f: xorps   0xf0(%rsp),%xmm1
     +0x927: movaps  %xmm0,0xe0(%rsp)
     +0x92f: movaps  %xmm1,0xf0(%rsp)
     +0x937: mov     0x2a0(%rbx),%rax
     +0x93e: xor     %rax,0x100(%rsp)
     +0x946: mov     %r15,%rdi
     +0x949: call    <mldsa_keccakf1600_permute>
     +0x94e: movups  0x2a8(%rbx),%xmm0
     +0x955: movups  0x2b8(%rbx),%xmm1
     +0x95c: xorps   0x80(%rsp),%xmm0
     +0x964: xorps   0x90(%rsp),%xmm1
     +0x96c: movaps  %xmm0,0x80(%rsp)
     +0x974: movaps  %xmm1,0x90(%rsp)
     +0x97c: movups  0x2c8(%rbx),%xmm0
     +0x983: movups  0x2d8(%rbx),%xmm1
     +0x98a: xorps   0xa0(%rsp),%xmm0
     +0x992: xorps   0xb0(%rsp),%xmm1
     +0x99a: movaps  %xmm0,0xa0(%rsp)
     +0x9a2: movaps  %xmm1,0xb0(%rsp)
     +0x9aa: movups  0x2e8(%rbx),%xmm0
     +0x9b1: movups  0x2f8(%rbx),%xmm1
     +0x9b8: xorps   0xc0(%rsp),%xmm0
     +0x9c0: xorps   0xd0(%rsp),%xmm1
     +0x9c8: movaps  %xmm0,0xc0(%rsp)
     +0x9d0: movaps  %xmm1,0xd0(%rsp)
     +0x9d8: movups  0x308(%rbx),%xmm0
     +0x9df: movups  0x318(%rbx),%xmm1
     +0x9e6: xorps   0xe0(%rsp),%xmm0
     +0x9ee: xorps   0xf0(%rsp),%xmm1
     +0x9f6: movaps  %xmm0,0xe0(%rsp)
     +0x9fe: movaps  %xmm1,0xf0(%rsp)
     +0xa06: mov     0x328(%rbx),%rax
     +0xa0d: xor     %rax,0x100(%rsp)
     +0xa15: mov     %r15,%rdi
     +0xa18: call    <mldsa_keccakf1600_permute>
     +0xa1d: movups  0x330(%rbx),%xmm0
     +0xa24: movups  0x340(%rbx),%xmm1
     +0xa2b: xorps   0x80(%rsp),%xmm0
     +0xa33: xorps   0x90(%rsp),%xmm1
     +0xa3b: movaps  %xmm0,0x80(%rsp)
     +0xa43: movaps  %xmm1,0x90(%rsp)
     +0xa4b: movups  0x350(%rbx),%xmm0
     +0xa52: movups  0x360(%rbx),%xmm1
     +0xa59: xorps   0xa0(%rsp),%xmm0
     +0xa61: xorps   0xb0(%rsp),%xmm1
     +0xa69: movaps  %xmm0,0xa0(%rsp)
     +0xa71: movaps  %xmm1,0xb0(%rsp)
     +0xa79: movups  0x370(%rbx),%xmm0
     +0xa80: movups  0x380(%rbx),%xmm1
     +0xa87: xorps   0xc0(%rsp),%xmm0
     +0xa8f: xorps   0xd0(%rsp),%xmm1
     +0xa97: movaps  %xmm0,0xc0(%rsp)
     +0xa9f: movaps  %xmm1,0xd0(%rsp)
     +0xaa7: movups  0x390(%rbx),%xmm0
     +0xaae: movups  0x3a0(%rbx),%xmm1
     +0xab5: xorps   0xe0(%rsp),%xmm0
     +0xabd: xorps   0xf0(%rsp),%xmm1
     +0xac5: movaps  %xmm0,0xe0(%rsp)
     +0xacd: movaps  %xmm1,0xf0(%rsp)
     +0xad5: mov     0x3b0(%rbx),%rax
     +0xadc: xor     %rax,0x100(%rsp)
     +0xae4: mov     %r15,%rdi
     +0xae7: call    <mldsa_keccakf1600_permute>
     +0xaec: movups  0x3b8(%rbx),%xmm0
     +0xaf3: movups  0x3c8(%rbx),%xmm1
     +0xafa: xorps   0x80(%rsp),%xmm0
     +0xb02: xorps   0x90(%rsp),%xmm1
     +0xb0a: movaps  %xmm0,0x80(%rsp)
     +0xb12: movaps  %xmm1,0x90(%rsp)
     +0xb1a: movups  0x3d8(%rbx),%xmm0
     +0xb21: movups  0x3e8(%rbx),%xmm1
     +0xb28: xorps   0xa0(%rsp),%xmm0
     +0xb30: xorps   0xb0(%rsp),%xmm1
     +0xb38: movaps  %xmm0,0xa0(%rsp)
     +0xb40: movaps  %xmm1,0xb0(%rsp)
     +0xb48: movups  0x3f8(%rbx),%xmm0
     +0xb4f: movups  0x408(%rbx),%xmm1
     +0xb56: xorps   0xc0(%rsp),%xmm0
     +0xb5e: xorps   0xd0(%rsp),%xmm1
     +0xb66: movaps  %xmm0,0xc0(%rsp)
     +0xb6e: movaps  %xmm1,0xd0(%rsp)
     +0xb76: movups  0x418(%rbx),%xmm0
     +0xb7d: movups  0x428(%rbx),%xmm1
     +0xb84: xorps   0xe0(%rsp),%xmm0
     +0xb8c: xorps   0xf0(%rsp),%xmm1
     +0xb94: movaps  %xmm0,0xe0(%rsp)
     +0xb9c: movaps  %xmm1,0xf0(%rsp)
     +0xba4: mov     0x438(%rbx),%rax
     +0xbab: xor     %rax,0x100(%rsp)
     +0xbb3: mov     %r15,%rdi
     +0xbb6: call    <mldsa_keccakf1600_permute>
     +0xbbb: movups  0x440(%rbx),%xmm0
     +0xbc2: movups  0x450(%rbx),%xmm1
     +0xbc9: xorps   0x80(%rsp),%xmm0
     +0xbd1: xorps   0x90(%rsp),%xmm1
     +0xbd9: movaps  %xmm0,0x80(%rsp)
     +0xbe1: movaps  %xmm1,0x90(%rsp)
     +0xbe9: movups  0x460(%rbx),%xmm0
     +0xbf0: movups  0x470(%rbx),%xmm1
     +0xbf7: xorps   0xa0(%rsp),%xmm0
     +0xbff: xorps   0xb0(%rsp),%xmm1
     +0xc07: movaps  %xmm0,0xa0(%rsp)
     +0xc0f: movaps  %xmm1,0xb0(%rsp)
     +0xc17: movups  0x480(%rbx),%xmm0
     +0xc1e: movups  0x490(%rbx),%xmm1
     +0xc25: xorps   0xc0(%rsp),%xmm0
     +0xc2d: xorps   0xd0(%rsp),%xmm1
     +0xc35: movaps  %xmm0,0xc0(%rsp)
     +0xc3d: movaps  %xmm1,0xd0(%rsp)
     +0xc45: movups  0x4a0(%rbx),%xmm0
     +0xc4c: movups  0x4b0(%rbx),%xmm1
     +0xc53: xorps   0xe0(%rsp),%xmm0
     +0xc5b: xorps   0xf0(%rsp),%xmm1
     +0xc63: movaps  %xmm0,0xe0(%rsp)
     +0xc6b: movaps  %xmm1,0xf0(%rsp)
     +0xc73: mov     0x4c0(%rbx),%rax
     +0xc7a: xor     %rax,0x100(%rsp)
     +0xc82: mov     %r15,%rdi
     +0xc85: call    <mldsa_keccakf1600_permute>
     +0xc8a: mov     0x4c8(%rbx),%rax
     +0xc91: mov     0x4d0(%rbx),%rcx
     +0xc98: xor     %rax,0x80(%rsp)
     +0xca0: xor     %rcx,0x88(%rsp)
     +0xca8: mov     0x4d8(%rbx),%rax
     +0xcaf: mov     0x4e0(%rbx),%rcx
     +0xcb6: xor     %rax,0x90(%rsp)
     +0xcbe: xor     %rcx,0x98(%rsp)
     +0xcc6: mov     0x4e8(%rbx),%rax
     +0xccd: mov     0x4f0(%rbx),%rcx
     +0xcd4: xor     %rax,0xa0(%rsp)
     +0xcdc: xor     %rcx,0xa8(%rsp)
     +0xce4: mov     0x4f8(%rbx),%rax
     +0xceb: mov     0x500(%rbx),%rcx
     +0xcf2: xor     %rax,0xb0(%rsp)
     +0xcfa: xor     %rcx,0xb8(%rsp)
     +0xd02: mov     0x508(%rbx),%rax
     +0xd09: mov     0x510(%rbx),%rcx
     +0xd10: xor     %rax,0xc0(%rsp)
     +0xd18: xor     %rcx,0xc8(%rsp)
     +0xd20: mov     0x518(%rbx),%rax
     +0xd27: xor     %rax,0xd0(%rsp)
     +0xd2f: xorb    $0x1f,0xd8(%rsp)
     +0xd37: xorb    $0x80,0x107(%rsp)
     +0xd3f: movl    $0x88,0x148(%rsp)
     +0xd4a: mov     %r15,%rdi
     +0xd4d: call    <mldsa_keccakf1600_permute>
     +0xd52: movaps  0x80(%rsp),%xmm0
     +0xd5a: movaps  0x90(%rsp),%xmm1
     +0xd62: movdqa  0xa0(%rsp),%xmm2
     +0xd6b: movdqa  0xb0(%rsp),%xmm3
     +0xd74: movdqa  %xmm3,0xd10(%rsp)
     +0xd7d: movdqa  %xmm2,0xd00(%rsp)
     +0xd86: movaps  %xmm1,0xcf0(%rsp)
     +0xd8e: movaps  %xmm0,0xce0(%rsp)
     +0xd96: xorps   %xmm0,%xmm0
     +0xd99: movaps  %xmm0,0xc0(%rsp)
     +0xda1: movaps  %xmm0,0xd0(%rsp)
     +0xda9: movaps  %xmm0,0xe0(%rsp)
     +0xdb1: movaps  %xmm0,0xf0(%rsp)
     +0xdb9: movaps  %xmm0,0x100(%rsp)
     +0xdc1: movaps  %xmm0,0x110(%rsp)
     +0xdc9: movaps  %xmm0,0x120(%rsp)
     +0xdd1: movaps  %xmm0,0x130(%rsp)
     +0xdd9: movaps  %xmm0,0x140(%rsp)
     +0xde1: movaps  %xmm0,0x80(%rsp)
     +0xde9: movaps  %xmm0,0x90(%rsp)
     +0xdf1: movaps  %xmm0,0xa0(%rsp)
     +0xdf9: movaps  %xmm0,0xb0(%rsp)
     +0xe01: movaps  %xmm0,0x140(%rsp)
     +0xe09: movaps  %xmm0,0x130(%rsp)
     +0xe11: movaps  %xmm0,0x120(%rsp)
     +0xe19: movaps  %xmm0,0x110(%rsp)
     +0xe21: movaps  %xmm0,0x100(%rsp)
     +0xe29: movaps  %xmm0,0xf0(%rsp)
     +0xe31: movaps  %xmm0,0xe0(%rsp)
     +0xe39: movaps  %xmm0,0xd0(%rsp)
     +0xe41: movaps  %xmm0,0xc0(%rsp)
     +0xe49: movaps  %xmm0,0xb0(%rsp)
     +0xe51: movaps  %xmm0,0xa0(%rsp)
     +0xe59: movaps  %xmm0,0x90(%rsp)
     +0xe61: movaps  %xmm0,0x80(%rsp)
     +0xe69: mov     %r13,0x8(%rsp)
     +0xe6e: mov     %r12,(%rsp)
     +0xe72: lea     0x4a0(%rsp),%rdi
     +0xe7a: lea     0xce0(%rsp),%r15
     +0xe82: mov     $0x40,%esi
     +0xe87: mov     $0x40,%ecx
     +0xe8c: mov     %r15,%rdx
     +0xe8f: mov     0x30(%rsp),%r8
     +0xe94: mov     0x28(%rsp),%r9
     +0xe99: call    <mld_H44>
     +0xe9e: xorps   %xmm0,%xmm0
     +0xea1: movaps  %xmm0,0xd10(%rsp)
     +0xea9: movaps  %xmm0,0xd00(%rsp)
     +0xeb1: movaps  %xmm0,0xcf0(%rsp)
     +0xeb9: movaps  %xmm0,0xce0(%rsp)
     +0xec1: movabs  $0x380200100000000,%r12
     +0xecb: lea     0x10e0(%rsp),%r13
     +0xed3: mov     %r13,%rdi
     +0xed6: call    <mldsa_poly_ntt>
     +0xedb: mov     %r14,%rdi
     +0xede: call    <mldsa_poly_ntt>
     +0xee3: lea     0x18e0(%rsp),%rdi
     +0xeeb: call    <mldsa_poly_ntt>
     +0xef0: lea     0x1ce0(%rsp),%rdi
     +0xef8: call    <mldsa_poly_ntt>
     +0xefd: movdqu  (%rbx),%xmm0
     +0xf01: movdqu  0x10(%rbx),%xmm1
     +0xf06: movdqa  %xmm1,0x490(%rsp)
     +0xf0f: movdqa  %xmm0,0x480(%rsp)
     +0xf18: lea     0xce0(%rsp),%r15
     +0xf20: lea     0x40(%rsp),%rsi
     +0xf25: mov     %r15,%rdi
     +0xf28: call    <mldsa44_poly_challenge>
     +0xf2d: mov     %r15,%rdi
     +0xf30: mov     %r13,%r15
     +0xf33: call    <mldsa_poly_ntt>
     +0xf38: add     $0x21,%rbx
     +0xf3c: lea     0x20e2(%rsp),%r13
     +0xf44: lea     0x8e0(%rsp),%r14
     +0xf4c: lea     0x80(%rsp),%rsi
     +0xf54: xor     %ecx,%ecx
     +0xf56: mov     %r14,%rdi
     +0xf59: mov     %r15,%rdx
     +0xf5c: mov     %rcx,0x28(%rsp)
     +0xf61: call    <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy>
     +0xf66: movq    0x1e532(%rip),%xmm4
     +0xf6e: movq    0x1e51a(%rip),%xmm3
     +0xf76: pxor    %xmm2,%xmm2
     +0xf7a: mov     %rbx,%rax
     +0xf7d: xor     %ecx,%ecx
     +0xf7f: nop     
     +0xf80: mov     (%rax),%edx
     +0xf82: movd    %edx,%xmm0
     +0xf86: movzbl  (%rax),%esi
     +0xf89: mov     %edx,%edi
     +0xf8b: shr     $0x16,%edi
     +0xf8e: and     $0x3,%edi
     +0xf91: shr     $0xc,%edx
     +0xf94: and     $0xf,%edx
     +0xf97: shr     $0x2,%esi
     +0xf9a: punpcklbw %xmm2,%xmm0
     +0xf9e: pmullw  %xmm3,%xmm0
     +0xfa2: pand    %xmm4,%xmm0
     +0xfa6: movzbl  -0x1(%rax),%r8d
     +0xfab: movd    %r8d,%xmm1
     +0xfb0: pinsrw  $0x1,%esi,%xmm1
     +0xfb5: pinsrw  $0x2,%edx,%xmm1
     +0xfba: pinsrw  $0x3,%edi,%xmm1
     +0xfbf: por     %xmm0,%xmm1
     +0xfc3: punpcklwd %xmm2,%xmm1
     +0xfc7: movdqa  %xmm1,0x4e0(%rsp,%rcx,1)
     +0xfd0: add     $0x10,%rcx
     +0xfd4: add     $0x5,%rax
     +0xfd8: cmp     $0x400,%rcx
     +0xfdf: jne     <mldsa44_verify_internal+0xf80>
     +0xfe1: movdqa  0x4e0(%rsp),%xmm0
     +0xfea: movdqa  0x4f0(%rsp),%xmm1
     +0xff3: movdqa  0x500(%rsp),%xmm2
     +0xffc: movdqa  0x510(%rsp),%xmm3
    +0x1005: pslld   $0xd,%xmm0
    +0x100a: pslld   $0xd,%xmm1
    +0x100f: movdqa  %xmm0,0x4e0(%rsp)
    +0x1018: movdqa  %xmm1,0x4f0(%rsp)
    +0x1021: pslld   $0xd,%xmm2
    +0x1026: pslld   $0xd,%xmm3
    +0x102b: movdqa  %xmm2,0x500(%rsp)
    +0x1034: movdqa  %xmm3,0x510(%rsp)
    +0x103d: movdqa  0x520(%rsp),%xmm0
    +0x1046: movdqa  0x530(%rsp),%xmm1
    +0x104f: pslld   $0xd,%xmm0
    +0x1054: pslld   $0xd,%xmm1
    +0x1059: movdqa  %xmm0,0x520(%rsp)
    +0x1062: movdqa  %xmm1,0x530(%rsp)
    +0x106b: movdqa  0x540(%rsp),%xmm0
    +0x1074: movdqa  0x550(%rsp),%xmm1
    +0x107d: pslld   $0xd,%xmm0
    +0x1082: pslld   $0xd,%xmm1
    +0x1087: movdqa  %xmm0,0x540(%rsp)
    +0x1090: movdqa  %xmm1,0x550(%rsp)
    +0x1099: movdqa  0x560(%rsp),%xmm0
    +0x10a2: movdqa  0x570(%rsp),%xmm1
    +0x10ab: pslld   $0xd,%xmm0
    +0x10b0: pslld   $0xd,%xmm1
    +0x10b5: movdqa  %xmm0,0x560(%rsp)
    +0x10be: movdqa  %xmm1,0x570(%rsp)
    +0x10c7: movdqa  0x580(%rsp),%xmm0
    +0x10d0: movdqa  0x590(%rsp),%xmm1
    +0x10d9: pslld   $0xd,%xmm0
    +0x10de: pslld   $0xd,%xmm1
    +0x10e3: movdqa  %xmm0,0x580(%rsp)
    +0x10ec: movdqa  %xmm1,0x590(%rsp)
    +0x10f5: movdqa  0x5a0(%rsp),%xmm0
    +0x10fe: movdqa  0x5b0(%rsp),%xmm1
    +0x1107: pslld   $0xd,%xmm0
    +0x110c: pslld   $0xd,%xmm1
    +0x1111: movdqa  %xmm0,0x5a0(%rsp)
    +0x111a: movdqa  %xmm1,0x5b0(%rsp)
    +0x1123: movdqa  0x5c0(%rsp),%xmm0
    +0x112c: movdqa  0x5d0(%rsp),%xmm1
    +0x1135: pslld   $0xd,%xmm0
    +0x113a: pslld   $0xd,%xmm1
    +0x113f: movdqa  %xmm0,0x5c0(%rsp)
    +0x1148: movdqa  %xmm1,0x5d0(%rsp)
    +0x1151: movdqa  0x5e0(%rsp),%xmm0
    +0x115a: movdqa  0x5f0(%rsp),%xmm1
    +0x1163: pslld   $0xd,%xmm0
    +0x1168: pslld   $0xd,%xmm1
    +0x116d: movdqa  %xmm0,0x5e0(%rsp)
    +0x1176: movdqa  %xmm1,0x5f0(%rsp)
    +0x117f: movdqa  0x600(%rsp),%xmm0
    +0x1188: movdqa  0x610(%rsp),%xmm1
    +0x1191: pslld   $0xd,%xmm0
    +0x1196: pslld   $0xd,%xmm1
    +0x119b: movdqa  %xmm0,0x600(%rsp)
    +0x11a4: movdqa  %xmm1,0x610(%rsp)
    +0x11ad: movdqa  0x620(%rsp),%xmm0
    +0x11b6: movdqa  0x630(%rsp),%xmm1
    +0x11bf: pslld   $0xd,%xmm0
    +0x11c4: pslld   $0xd,%xmm1
    +0x11c9: movdqa  %xmm0,0x620(%rsp)
    +0x11d2: movdqa  %xmm1,0x630(%rsp)
    +0x11db: movdqa  0x640(%rsp),%xmm0
    +0x11e4: movdqa  0x650(%rsp),%xmm1
    +0x11ed: pslld   $0xd,%xmm0
    +0x11f2: pslld   $0xd,%xmm1
    +0x11f7: movdqa  %xmm0,0x640(%rsp)
    +0x1200: movdqa  %xmm1,0x650(%rsp)
    +0x1209: movdqa  0x660(%rsp),%xmm0
    +0x1212: movdqa  0x670(%rsp),%xmm1
    +0x121b: pslld   $0xd,%xmm0
    +0x1220: pslld   $0xd,%xmm1
    +0x1225: movdqa  %xmm0,0x660(%rsp)
    +0x122e: movdqa  %xmm1,0x670(%rsp)
    +0x1237: movdqa  0x680(%rsp),%xmm0
    +0x1240: movdqa  0x690(%rsp),%xmm1
    +0x1249: pslld   $0xd,%xmm0
    +0x124e: pslld   $0xd,%xmm1
    +0x1253: movdqa  %xmm0,0x680(%rsp)
    +0x125c: movdqa  %xmm1,0x690(%rsp)
    +0x1265: movdqa  0x6a0(%rsp),%xmm0
    +0x126e: movdqa  0x6b0(%rsp),%xmm1
    +0x1277: pslld   $0xd,%xmm0
    +0x127c: pslld   $0xd,%xmm1
    +0x1281: movdqa  %xmm0,0x6a0(%rsp)
    +0x128a: movdqa  %xmm1,0x6b0(%rsp)
    +0x1293: movdqa  0x6c0(%rsp),%xmm0
    +0x129c: movdqa  0x6d0(%rsp),%xmm1
    +0x12a5: pslld   $0xd,%xmm0
    +0x12aa: pslld   $0xd,%xmm1
    +0x12af: movdqa  %xmm0,0x6c0(%rsp)
    +0x12b8: movdqa  %xmm1,0x6d0(%rsp)
    +0x12c1: movdqa  0x6e0(%rsp),%xmm0
    +0x12ca: movdqa  0x6f0(%rsp),%xmm1
    +0x12d3: pslld   $0xd,%xmm0
    +0x12d8: pslld   $0xd,%xmm1
    +0x12dd: movdqa  %xmm0,0x6e0(%rsp)
    +0x12e6: movdqa  %xmm1,0x6f0(%rsp)
    +0x12ef: movdqa  0x700(%rsp),%xmm0
    +0x12f8: movdqa  0x710(%rsp),%xmm1
    +0x1301: pslld   $0xd,%xmm0
    +0x1306: pslld   $0xd,%xmm1
    +0x130b: movdqa  %xmm0,0x700(%rsp)
    +0x1314: movdqa  %xmm1,0x710(%rsp)
    +0x131d: movdqa  0x720(%rsp),%xmm0
    +0x1326: movdqa  0x730(%rsp),%xmm1
    +0x132f: pslld   $0xd,%xmm0
    +0x1334: pslld   $0xd,%xmm1
    +0x1339: movdqa  %xmm0,0x720(%rsp)
    +0x1342: movdqa  %xmm1,0x730(%rsp)
    +0x134b: movdqa  0x740(%rsp),%xmm0
    +0x1354: movdqa  0x750(%rsp),%xmm1
    +0x135d: pslld   $0xd,%xmm0
    +0x1362: pslld   $0xd,%xmm1
    +0x1367: movdqa  %xmm0,0x740(%rsp)
    +0x1370: movdqa  %xmm1,0x750(%rsp)
    +0x1379: movdqa  0x760(%rsp),%xmm0
    +0x1382: movdqa  0x770(%rsp),%xmm1
    +0x138b: pslld   $0xd,%xmm0
    +0x1390: pslld   $0xd,%xmm1
    +0x1395: movdqa  %xmm0,0x760(%rsp)
    +0x139e: movdqa  %xmm1,0x770(%rsp)
    +0x13a7: movdqa  0x780(%rsp),%xmm0
    +0x13b0: movdqa  0x790(%rsp),%xmm1
    +0x13b9: pslld   $0xd,%xmm0
    +0x13be: pslld   $0xd,%xmm1
    +0x13c3: movdqa  %xmm0,0x780(%rsp)
    +0x13cc: movdqa  %xmm1,0x790(%rsp)
    +0x13d5: movdqa  0x7a0(%rsp),%xmm0
    +0x13de: movdqa  0x7b0(%rsp),%xmm1
    +0x13e7: pslld   $0xd,%xmm0
    +0x13ec: pslld   $0xd,%xmm1
    +0x13f1: movdqa  %xmm0,0x7a0(%rsp)
    +0x13fa: movdqa  %xmm1,0x7b0(%rsp)
    +0x1403: movdqa  0x7c0(%rsp),%xmm0
    +0x140c: movdqa  0x7d0(%rsp),%xmm1
    +0x1415: pslld   $0xd,%xmm0
    +0x141a: pslld   $0xd,%xmm1
    +0x141f: movdqa  %xmm0,0x7c0(%rsp)
    +0x1428: movdqa  %xmm1,0x7d0(%rsp)
    +0x1431: movdqa  0x7e0(%rsp),%xmm0
    +0x143a: movdqa  0x7f0(%rsp),%xmm1
    +0x1443: pslld   $0xd,%xmm0
    +0x1448: pslld   $0xd,%xmm1
    +0x144d: movdqa  %xmm0,0x7e0(%rsp)
    +0x1456: movdqa  %xmm1,0x7f0(%rsp)
    +0x145f: movdqa  0x800(%rsp),%xmm0
    +0x1468: movdqa  0x810(%rsp),%xmm1
    +0x1471: pslld   $0xd,%xmm0
    +0x1476: pslld   $0xd,%xmm1
    +0x147b: movdqa  %xmm0,0x800(%rsp)
    +0x1484: movdqa  %xmm1,0x810(%rsp)
    +0x148d: movdqa  0x820(%rsp),%xmm0
    +0x1496: movdqa  0x830(%rsp),%xmm1
    +0x149f: pslld   $0xd,%xmm0
    +0x14a4: pslld   $0xd,%xmm1
    +0x14a9: movdqa  %xmm0,0x820(%rsp)
    +0x14b2: movdqa  %xmm1,0x830(%rsp)
    +0x14bb: movdqa  0x840(%rsp),%xmm0
    +0x14c4: movdqa  0x850(%rsp),%xmm1
    +0x14cd: pslld   $0xd,%xmm0
    +0x14d2: pslld   $0xd,%xmm1
    +0x14d7: movdqa  %xmm0,0x840(%rsp)
    +0x14e0: movdqa  %xmm1,0x850(%rsp)
    +0x14e9: movdqa  0x860(%rsp),%xmm0
    +0x14f2: movdqa  0x870(%rsp),%xmm1
    +0x14fb: pslld   $0xd,%xmm0
    +0x1500: pslld   $0xd,%xmm1
    +0x1505: movdqa  %xmm0,0x860(%rsp)
    +0x150e: movdqa  %xmm1,0x870(%rsp)
    +0x1517: movdqa  0x880(%rsp),%xmm0
    +0x1520: movdqa  0x890(%rsp),%xmm1
    +0x1529: pslld   $0xd,%xmm0
    +0x152e: pslld   $0xd,%xmm1
    +0x1533: movdqa  %xmm0,0x880(%rsp)
    +0x153c: movdqa  %xmm1,0x890(%rsp)
    +0x1545: movdqa  0x8a0(%rsp),%xmm0
    +0x154e: movdqa  0x8b0(%rsp),%xmm1
    +0x1557: pslld   $0xd,%xmm0
    +0x155c: pslld   $0xd,%xmm1
    +0x1561: movdqa  %xmm0,0x8a0(%rsp)
    +0x156a: movdqa  %xmm1,0x8b0(%rsp)
    +0x1573: movdqa  0x8c0(%rsp),%xmm0
    +0x157c: movdqa  0x8d0(%rsp),%xmm1
    +0x1585: pslld   $0xd,%xmm0
    +0x158a: pslld   $0xd,%xmm1
    +0x158f: movdqa  %xmm0,0x8c0(%rsp)
    +0x1598: movdqa  %xmm1,0x8d0(%rsp)
    +0x15a1: lea     0x4e0(%rsp),%rdi
    +0x15a9: call    <mldsa_poly_ntt>
    +0x15ae: mov     $0x1,%eax
    +0x15b3: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x15c0: movslq  0x4dc(%rsp,%rax,4),%rcx
    +0x15c8: movslq  0xcdc(%rsp,%rax,4),%rdx
    +0x15d0: imul    %rcx,%rdx
    +0x15d4: mov     %rdx,%rcx
    +0x15d7: imul    %r12,%rcx
    +0x15db: sar     $0x20,%rcx
    +0x15df: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x15e6: add     %rdx,%rcx
    +0x15e9: shr     $0x20,%rcx
    +0x15ed: mov     %ecx,0x4dc(%rsp,%rax,4)
    +0x15f4: movslq  0x4e0(%rsp,%rax,4),%rcx
    +0x15fc: movslq  0xce0(%rsp,%rax,4),%rdx
    +0x1604: imul    %rcx,%rdx
    +0x1608: mov     %rdx,%rcx
    +0x160b: imul    %r12,%rcx
    +0x160f: sar     $0x20,%rcx
    +0x1613: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x161a: add     %rdx,%rcx
    +0x161d: shr     $0x20,%rcx
    +0x1621: mov     %ecx,0x4e0(%rsp,%rax,4)
    +0x1628: add     $0x2,%rax
    +0x162c: cmp     $0x101,%rax
    +0x1632: jne     <mldsa44_verify_internal+0x15c0>
    +0x1634: mov     $0xc,%eax
    +0x1639: movdqa  0x1de0f(%rip),%xmm5
    +0x1641: movdqa  0x1de17(%rip),%xmm6
    +0x1649: nopl    0x0(%rax)
    +0x1650: movdqa  0x8b0(%rsp,%rax,4),%xmm0
    +0x1659: movdqa  0x8c0(%rsp,%rax,4),%xmm1
    +0x1662: movdqa  0x8d0(%rsp,%rax,4),%xmm2
    +0x166b: movdqa  0x8e0(%rsp,%rax,4),%xmm3
    +0x1674: psubd   0x4b0(%rsp,%rax,4),%xmm0
    +0x167d: psubd   0x4c0(%rsp,%rax,4),%xmm1
    +0x1686: movdqa  %xmm0,0x8b0(%rsp,%rax,4)
    +0x168f: movdqa  %xmm1,0x8c0(%rsp,%rax,4)
    +0x1698: psubd   0x4d0(%rsp,%rax,4),%xmm2
    +0x16a1: psubd   0x4e0(%rsp,%rax,4),%xmm3
    +0x16aa: movdqa  %xmm2,0x8d0(%rsp,%rax,4)
    +0x16b3: movdqa  %xmm3,0x8e0(%rsp,%rax,4)
    +0x16bc: add     $0x10,%rax
    +0x16c0: cmp     $0x10c,%rax
    +0x16c6: jne     <mldsa44_verify_internal+0x1650>
    +0x16c8: mov     $0x4,%eax
    +0x16cd: nopl    (%rax)
    +0x16d0: movdqa  0x8d0(%rsp,%rax,4),%xmm0
    +0x16d9: movdqa  0x8e0(%rsp,%rax,4),%xmm1
    +0x16e2: movdqa  %xmm0,%xmm2
    +0x16e6: paddd   %xmm5,%xmm2
    +0x16ea: movdqa  %xmm1,%xmm3
    +0x16ee: paddd   %xmm5,%xmm3
    +0x16f2: psrad   $0x17,%xmm2
    +0x16f7: psrad   $0x17,%xmm3
    +0x16fc: pshufd  $0xf5,%xmm2,%xmm4
    +0x1701: pmuludq %xmm6,%xmm2
    +0x1705: pshufd  $0xe8,%xmm2,%xmm2
    +0x170a: pmuludq %xmm6,%xmm4
    +0x170e: pshufd  $0xe8,%xmm4,%xmm4
    +0x1713: punpckldq %xmm4,%xmm2
    +0x1717: pshufd  $0xf5,%xmm3,%xmm4
    +0x171c: pmuludq %xmm6,%xmm3
    +0x1720: pshufd  $0xe8,%xmm3,%xmm3
    +0x1725: pmuludq %xmm6,%xmm4
    +0x1729: pshufd  $0xe8,%xmm4,%xmm4
    +0x172e: punpckldq %xmm4,%xmm3
    +0x1732: paddd   %xmm0,%xmm2
    +0x1736: paddd   %xmm1,%xmm3
    +0x173a: movdqa  %xmm2,0x8d0(%rsp,%rax,4)
    +0x1743: movdqa  %xmm3,0x8e0(%rsp,%rax,4)
    +0x174c: add     $0x8,%rax
    +0x1750: cmp     $0x104,%rax
    +0x1756: jne     <mldsa44_verify_internal+0x16d0>
    +0x175c: mov     %r14,%rdi
    +0x175f: call    <mldsa_poly_invntt_tomont>
    +0x1764: xor     %eax,%eax
    +0x1766: cs      nopw 0x0(%rax,%rax,1)
    +0x1770: movslq  0x8e0(%rsp,%rax,4),%rcx
    +0x1778: lea     0x7fe001(%rcx),%edx
    +0x177e: mov     %rcx,%rsi
    +0x1781: shr     $0x1f,%rsi
    +0x1785: xor     %ecx,%edx
    +0x1787: and     %esi,%edx
    +0x1789: xor     %ecx,%edx
    +0x178b: mov     %edx,0x8e0(%rsp,%rax,4)
    +0x1792: inc     %rax
    +0x1795: cmp     $0x100,%rax
    +0x179b: jne     <mldsa44_verify_internal+0x1770>
    +0x179d: mov     %r15,%r14
    +0x17a0: mov     0x28(%rsp),%rcx
    +0x17a5: test    %rcx,%rcx
    +0x17a8: mov     0x38(%rsp),%rax
    +0x17ad: mov     %rbx,0x30(%rsp)
    +0x17b2: je      <mldsa44_verify_internal+0x17d0>
    +0x17b4: movzbl  0x96f(%rax,%rcx,1),%r15d
    +0x17bd: movzbl  0x970(%rax,%rcx,1),%ebx
    +0x17c5: cmp     $0x50,%ebx
    +0x17c8: jbe     <mldsa44_verify_internal+0x17e4>
    +0x17ca: jmp     <mldsa44_verify_internal+0x3b1>
    +0x17cf: nop     
    +0x17d0: xor     %r15d,%r15d
    +0x17d3: movzbl  0x970(%rax,%rcx,1),%ebx
    +0x17db: cmp     $0x50,%ebx
    +0x17de: ja      <mldsa44_verify_internal+0x3b1>
    +0x17e4: cmp     %ebx,%r15d
    +0x17e7: ja      <mldsa44_verify_internal+0x3b1>
    +0x17ed: mov     $0x400,%edx
    +0x17f2: lea     0x4e0(%rsp),%rdi
    +0x17fa: xor     %esi,%esi
    +0x17fc: call    <memset>
    +0x1801: mov     0x28(%rsp),%rcx
    +0x1806: mov     0x38(%rsp),%r8
    +0x180b: cmp     %ebx,%r15d
    +0x180e: mov     $0x2b,%r9d
    +0x1814: jae     <mldsa44_verify_internal+0x1839>
    +0x1816: mov     %r15d,%eax
    +0x1819: movzbl  0x920(%r8,%rax,1),%edx
    +0x1822: movl    $0x1,0x4e0(%rsp,%rdx,4)
    +0x182d: inc     %r15d
    +0x1830: cmp     %ebx,%r15d
    +0x1833: jne     <mldsa44_verify_internal+0x19a0>
    +0x1839: cmp     $0x3,%rcx
    +0x183d: mov     %r14,%r15
    +0x1840: jne     <mldsa44_verify_internal+0x1868>
    +0x1842: cmp     $0x50,%bl
    +0x1845: jae     <mldsa44_verify_internal+0x1868>
    +0x1847: mov     %ebx,%eax
    +0x1849: nopl    0x0(%rax)
    +0x1850: cmpb    $0x0,0x920(%r8,%rax,1)
    +0x1859: jne     <mldsa44_verify_internal+0x3b1>
    +0x185f: inc     %rax
    +0x1862: cmp     $0x50,%rax
    +0x1866: jne     <mldsa44_verify_internal+0x1850>
    +0x1868: xor     %eax,%eax
    +0x186a: mov     0x30(%rsp),%rbx
    +0x186f: xor     %r8d,%r8d
    +0x1872: lea     0x8e0(%rsp),%r14
    +0x187a: jmp     <mldsa44_verify_internal+0x18a2>
    +0x187c: nopl    0x0(%rax)
    +0x1880: cmp     $0x2b,%r10d
    +0x1884: lea     0x1(%r10),%edx
    +0x1888: cmove   %r8d,%edx
    +0x188c: mov     %edx,%r10d
    +0x188f: mov     %r10d,0x8e0(%rsp,%rax,4)
    +0x1897: inc     %rax
    +0x189a: cmp     $0x100,%rax
    +0x18a0: je      <mldsa44_verify_internal+0x1920>
    +0x18a2: mov     0x8e0(%rsp,%rax,4),%esi
    +0x18a9: lea     0x7f(%rsi),%edx
    +0x18ac: sar     $0x7,%edx
    +0x18af: imul    $0x2c0b,%edx,%edx
    +0x18b5: add     $0x800000,%edx
    +0x18bb: sar     $0x18,%edx
    +0x18be: mov     $0x2b,%edi
    +0x18c3: sub     %edx,%edi
    +0x18c5: movslq  %edi,%r10
    +0x18c8: mov     0x4e0(%rsp,%rax,4),%edi
    +0x18cf: shr     $0x1f,%r10
    +0x18d3: not     %r10d
    +0x18d6: and     %edx,%r10d
    +0x18d9: imul    $0xfffd1800,%r10d,%edx
    +0x18e0: add     %esi,%edx
    +0x18e2: mov     $0x3ff000,%esi
    +0x18e7: sub     %edx,%esi
    +0x18e9: movslq  %esi,%rsi
    +0x18ec: shr     $0x1f,%rsi
    +0x18f0: test    %edi,%edi
    +0x18f2: je      <mldsa44_verify_internal+0x188f>
    +0x18f4: lea     -0x7fe001(%rdx),%edi
    +0x18fa: xor     %edx,%edi
    +0x18fc: and     %esi,%edi
    +0x18fe: xor     %edx,%edi
    +0x1900: jg      <mldsa44_verify_internal+0x1880>
    +0x1906: sub     $0x1,%r10d
    +0x190a: cmovb   %r9d,%r10d
    +0x190e: jmp     <mldsa44_verify_internal+0x188f>
    +0x1913: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1920: lea     0x8ec(%rsp),%rax
    +0x1928: xor     %r8d,%r8d
    +0x192b: nopl    0x0(%rax,%rax,1)
    +0x1930: mov     -0x8(%rax),%edx
    +0x1933: mov     %edx,%esi
    +0x1935: shl     $0x6,%esi
    +0x1938: or      -0xc(%rax),%esi
    +0x193b: mov     %sil,-0x2(%r13,%r8,1)
    +0x1940: shr     $0x2,%edx
    +0x1943: mov     -0x4(%rax),%esi
    +0x1946: mov     %esi,%edi
    +0x1948: shl     $0x4,%edi
    +0x194b: or      %edx,%edi
    +0x194d: mov     %dil,-0x1(%r13,%r8,1)
    +0x1952: shr     $0x4,%esi
    +0x1955: mov     (%rax),%edx
    +0x1957: shl     $0x2,%edx
    +0x195a: or      %esi,%edx
    +0x195c: mov     %dl,0x0(%r13,%r8,1)
    +0x1961: add     $0x3,%r8
    +0x1965: add     $0x10,%rax
    +0x1969: cmp     $0xc0,%r8
    +0x1970: jne     <mldsa44_verify_internal+0x1930>
    +0x1972: inc     %rcx
    +0x1975: add     $0x140,%rbx
    +0x197c: add     $0xc0,%r13
    +0x1983: cmp     $0x4,%rcx
    +0x1987: lea     0x80(%rsp),%rsi
    +0x198f: jne     <mldsa44_verify_internal+0xf56>
    +0x1995: jmp     <mldsa44_verify_internal+0x19e8>
    +0x1997: nopw    0x0(%rax,%rax,1)
    +0x19a0: lea     -0x1(%rbx),%r10
    +0x19a4: mov     %rax,%rdx
    +0x19a7: jmp     <mldsa44_verify_internal+0x19c7>
    +0x19a9: nopl    0x0(%rax)
    +0x19b0: movl    $0x1,0x4e0(%rsp,%rdi,4)
    +0x19bb: mov     %rsi,%rdx
    +0x19be: cmp     %rsi,%r10
    +0x19c1: je      <mldsa44_verify_internal+0x1839>
    +0x19c7: lea     0x1(%rdx),%rsi
    +0x19cb: movzbl  0x921(%r8,%rdx,1),%edi
    +0x19d4: cmp     %rax,%rsi
    +0x19d7: jbe     <mldsa44_verify_internal+0x19b0>
    +0x19d9: cmp     0x920(%r8,%rdx,1),%dil
    +0x19e1: ja      <mldsa44_verify_internal+0x19b0>
    +0x19e3: jmp     <mldsa44_verify_internal+0x3b1>
    +0x19e8: pxor    %xmm0,%xmm0
    +0x19ec: movdqu  %xmm0,(%rsp)
    +0x19f1: lea     0x60(%rsp),%rdi
    +0x19f6: lea     0x4a0(%rsp),%rdx
    +0x19fe: lea     0x20e0(%rsp),%r8
    +0x1a06: mov     $0x20,%esi
    +0x1a0b: mov     $0x40,%ecx
    +0x1a10: mov     $0x300,%r9d
    +0x1a16: call    <mld_H44>
    +0x1a1b: movdqa  0x60(%rsp),%xmm1
    +0x1a21: pxor    0x40(%rsp),%xmm1
    +0x1a27: mov     0x70(%rsp),%rax
    +0x1a2c: xor     0x50(%rsp),%rax
    +0x1a31: movq    %rax,%xmm0
    +0x1a36: mov     0x78(%rsp),%rax
    +0x1a3b: xor     0x58(%rsp),%rax
    +0x1a40: movq    %rax,%xmm2
    +0x1a45: movdqa  %xmm1,%xmm3
    +0x1a49: pxor    %xmm0,%xmm3
    +0x1a4d: mov     0x7c(%rsp),%eax
    +0x1a51: xor     0x5c(%rsp),%eax
    +0x1a55: movd    %eax,%xmm4
    +0x1a59: punpcklqdq %xmm2,%xmm4
    +0x1a5d: shufps  $0x24,%xmm4,%xmm0
    +0x1a61: pshufd  $0xee,%xmm1,%xmm4
    +0x1a66: orps    %xmm1,%xmm0
    +0x1a69: movsd   %xmm3,%xmm1
    +0x1a6d: pxor    %xmm2,%xmm3
    +0x1a71: movss   %xmm3,%xmm1
    +0x1a75: pxor    %xmm1,%xmm4
    +0x1a79: pshufd  $0x55,%xmm4,%xmm1
    +0x1a7e: pxor    %xmm4,%xmm1
    +0x1a82: movdqa  %xmm1,%xmm2
    +0x1a86: psrld   $0x10,%xmm2
    +0x1a8b: pxor    %xmm1,%xmm2
    +0x1a8f: movdqa  %xmm2,%xmm1
    +0x1a93: psrlw   $0x8,%xmm1
    +0x1a98: pxor    %xmm2,%xmm1
    +0x1a9c: movd    %xmm1,%ecx
    +0x1aa0: mov     %eax,%edx
    +0x1aa2: shr     $0x8,%edx
    +0x1aa5: mov     %eax,%esi
    +0x1aa7: shr     $0x10,%esi
    +0x1aaa: xor     %edx,%esi
    +0x1aac: xor     %eax,%esi
    +0x1aae: pshufd  $0xee,%xmm0,%xmm1
    +0x1ab3: por     %xmm0,%xmm1
    +0x1ab7: pshufd  $0x55,%xmm1,%xmm0
    +0x1abc: por     %xmm1,%xmm0
    +0x1ac0: movdqa  %xmm0,%xmm1
    +0x1ac4: psrld   $0x10,%xmm1
    +0x1ac9: por     %xmm0,%xmm1
    +0x1acd: movdqa  %xmm1,%xmm0
    +0x1ad1: psrlw   $0x8,%xmm0
    +0x1ad6: por     %xmm1,%xmm0
    +0x1ada: movd    %xmm0,%edx
    +0x1ade: shr     $0x18,%eax
    +0x1ae1: xor     %esi,%eax
    +0x1ae3: xor     %ecx,%eax
    +0x1ae5: movzbl  %dl,%ecx
    +0x1ae8: neg     %rcx
    +0x1aeb: shr     $0x20,%rcx
    +0x1aef: xor     %al,%cl
    +0x1af1: xor     %edx,%edx
    +0x1af3: cmp     %al,%cl
    +0x1af5: mov     $0xfffffffa,%r14d
    +0x1afb: cmove   %edx,%r14d
    +0x1aff: jmp     <mldsa44_verify_internal+0x3b7>
 ***)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_verify_internal";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for memset and memcpy. The signature *)
(* sigb at sig (2420 bytes), the message M of mlen bytes at m and the prefix *)
(* PRE of prelen bytes at pre (or, if ext is nonzero, mu in the first 64     *)
(* bytes at m), the public key pkb at pk (1312 bytes): the result is 0 if    *)
(* the signature is accepted, and -6 otherwise. ext, the seventh argument,   *)
(* a 32-bit int, is on the stack above the return address; the callers write *)
(* only its 32 bits. The function saves RBP, sets it to the stack pointer,   *)
(* pushes five more registers, lowers RSP by up to 31 bytes to align it to   *)
(* 32 bytes, and reserves 9216 bytes for its buffers (touching each page),   *)
(* below which the callees use theirs: 10949 bytes of stack below the        *)
(* return address in all. The GOT entries of memset and memcpy, which the    *)
(* stubs read, and the region (ea,el) that they may read are apart from the  *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 4 4 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 39 32
           (num_of_bytelist(list_of_seq sigb 32)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 10949),10949))
              [(sig,2420); (m,mlen); (pre,prelen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa44_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes32(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mld_verify_internal_ok 4 4 32
                           mld_polyz_unpack_17 576 130994
                           mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39
                           sigb pkb
                           (if ext = (word 0:int32)
                            then mld_verify_mu 1312 pkb prelen PRE mlen M
                            else M MOD 2 EXP 512)
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 10949),10949)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the flag ext, the    *)
(* signature, the message, the prefix and the public key, all public, the    *)
(* addresses of memset and memcpy and the stack, with all accesses within   *)
(* the arguments, the stack, the return address and ext above it, the GOT    *)
(* entries, the region (ea,el), the constants of the function (its own       *)
(* pools and those of the inlined compute_pack_t0_t1 code) and those of the  *)
(* callees, and the writes within the stack.                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 4 4 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 39 32
           (num_of_bytelist(list_of_seq sigb 32)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 10949),10949))
              [(sig,2420); (m,mlen); (pre,prelen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa44_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes32(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mld_verify_internal_ok 4 4 32
                           mld_polyz_unpack_17 576 130994
                           mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39
                           sigb pkb
                           (if ext = (word 0:int32)
                            then mld_verify_mu 1312 pkb prelen PRE mlen M
                            else M MOD 2 EXP 512)
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE
                              mf mc pc (word_sub stackpointer (word 10949))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; pre,prelen; pk,1312;
                         word_sub stackpointer (word 10949),10949;
                         stackpointer,8; word_add stackpointer (word 8),4;
                         word(pc + got_memset),8;
                          word(pc + got_memcpy),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa44_poly_challenge_consts),64;
                          word(pc + mldsa44_verify_internal_const1),16;
                          word(pc + mldsa44_verify_internal_const2),16;
                          word(pc + mldsa44_verify_internal_const3),8;
                          word(pc + mldsa44_verify_internal_const4),8;
                          word(pc + mld_compute_pack_t0_t144_const1),16;
                          word(pc + mld_compute_pack_t0_t144_const2),16;
                          word(pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448]
                        [word_sub stackpointer (word 10949),10949]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 10949),10949)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 4 4 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 39 32
           (num_of_bytelist(list_of_seq sigb 32)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 10949),10949))
              [(sig,2420); (m,mlen); (pre,prelen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa44_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes32(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE
                              mf mc pc (word_sub stackpointer (word 10949))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; pre,prelen; pk,1312;
                         word_sub stackpointer (word 10949),10949;
                         stackpointer,8; word_add stackpointer (word 8),4;
                         word(pc + got_memset),8;
                          word(pc + got_memcpy),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa44_poly_challenge_consts),64;
                          word(pc + mldsa44_verify_internal_const1),16;
                          word(pc + mldsa44_verify_internal_const2),16;
                          word(pc + mldsa44_verify_internal_const3),8;
                          word(pc + mldsa44_verify_internal_const4),8;
                          word(pc + mld_compute_pack_t0_t144_const1),16;
                          word(pc + mld_compute_pack_t0_t144_const2),16;
                          word(pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448]
                        [word_sub stackpointer (word 10949),10949]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 10949),10949)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
