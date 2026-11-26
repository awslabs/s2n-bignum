(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the statement. This is the code for          *)
(* mldsa65_verify_internal (mld_sign_verify_internal in sign.c) from mldsa-  *)
(* native's portable C implementation compiled by clang 23 with -O3 and      *)
(* MLD_CONFIG_REDUCE_RAM as one translation unit (see                        *)
(* mldsa_native/README.md). It aligns its stack frame to 32 bytes, unpacks z *)
(* and checks its norm, computes mu (or takes it from m if ext is nonzero),  *)
(* transforms z, computes the challenge from c~ with mldsa65_poly_challenge, *)
(* and for each row computes w1' = UseHint(h, A z - c t1 2^d), and compares  *)
(* c~ with mld_H65 of mu and w1'. Clang has inlined most of its callees; it  *)
(* still calls mldsa65_polyvecl_chknorm, mld_H65, mldsa_poly_ntt,            *)
(* mldsa_poly_invntt_tomont,                                                 *)
(* mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy and                  *)
(* mldsa_keccakf1600_permute, and memset through the PLT, so the direction   *)
(* flag must be clear, as the ABI requires on entry. It is verified in the   *)
(* whole image (see libmldsa.ml) against mld_verify_internal_ok of           *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and the   *)
(* contracts memset_full_contract and memcpy_full_contract of                *)
(* utils/mldsa_native_libc.ml for the C library functions that they call,    *)
(* assuming that the expansion of the matrix and the sampling of the         *)
(* challenge terminate, and shown to be constant time and memory safe, with  *)
(* events depending on the signature, the message, the prefix and the public *)
(* key, which are all public.                                                *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvecl_chknorm_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_challenge_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/H_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa65_verify_internal:
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
      +0x2f: sub     $0x860,%rsp
      +0x36: mov     %r9,%rbx
      +0x39: mov     %r8,%r14
      +0x3c: mov     %rcx,0x498(%rsp)
      +0x44: mov     %rdx,%r13
      +0x47: mov     %rsi,%r12
      +0x4a: mov     0x10(%rbp),%r15d
      +0x4e: movdqu  (%rdi),%xmm0
      +0x52: movups  0x10(%rdi),%xmm1
      +0x56: movdqu  0x20(%rdi),%xmm2
      +0x5b: movdqa  %xmm0,0x460(%rsp)
      +0x64: movaps  %xmm1,0x470(%rsp)
      +0x6c: movdqa  %xmm2,0x480(%rsp)
      +0x75: lea     0x34(%rdi),%rax
      +0x79: xor     %ecx,%ecx
      +0x7b: nopl    0x0(%rax,%rax,1)
      +0x80: movzwl  -0x4(%rax),%edx
      +0x84: movzbl  -0x2(%rax),%esi
      +0x88: mov     %esi,%r8d
      +0x8b: and     $0xf,%r8d
      +0x8f: shl     $0x10,%r8d
      +0x93: or      %edx,%r8d
      +0x96: shr     $0x4,%esi
      +0x99: movzbl  -0x1(%rax),%edx
      +0x9d: shl     $0x4,%edx
      +0xa0: or      %esi,%edx
      +0xa2: movzbl  (%rax),%esi
      +0xa5: shl     $0xc,%esi
      +0xa8: or      %edx,%esi
      +0xaa: mov     $0x80000,%edx
      +0xaf: sub     %r8d,%edx
      +0xb2: mov     %edx,0x1420(%rsp,%rcx,8)
      +0xb9: mov     $0x80000,%edx
      +0xbe: sub     %esi,%edx
      +0xc0: mov     %edx,0x1424(%rsp,%rcx,8)
      +0xc7: inc     %rcx
      +0xca: add     $0x5,%rax
      +0xce: cmp     $0x80,%rcx
      +0xd5: jne     <mldsa65_verify_internal+0x80>
      +0xd7: lea     0x2b4(%rdi),%rax
      +0xde: mov     $0x80,%ecx
      +0xe3: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
      +0xf0: movzwl  -0x4(%rax),%edx
      +0xf4: movzbl  -0x2(%rax),%esi
      +0xf8: mov     %esi,%r8d
      +0xfb: and     $0xf,%r8d
      +0xff: shl     $0x10,%r8d
     +0x103: or      %edx,%r8d
     +0x106: shr     $0x4,%esi
     +0x109: movzbl  -0x1(%rax),%edx
     +0x10d: shl     $0x4,%edx
     +0x110: or      %esi,%edx
     +0x112: movzbl  (%rax),%esi
     +0x115: shl     $0xc,%esi
     +0x118: or      %edx,%esi
     +0x11a: mov     $0x80000,%edx
     +0x11f: sub     %r8d,%edx
     +0x122: mov     %edx,0x1420(%rsp,%rcx,8)
     +0x129: mov     $0x80000,%edx
     +0x12e: sub     %esi,%edx
     +0x130: mov     %edx,0x1424(%rsp,%rcx,8)
     +0x137: inc     %rcx
     +0x13a: add     $0x5,%rax
     +0x13e: cmp     $0x100,%rcx
     +0x145: jne     <mldsa65_verify_internal+0xf0>
     +0x147: lea     0x534(%rdi),%rax
     +0x14e: mov     $0x100,%ecx
     +0x153: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x160: movzwl  -0x4(%rax),%edx
     +0x164: movzbl  -0x2(%rax),%esi
     +0x168: mov     %esi,%r8d
     +0x16b: and     $0xf,%r8d
     +0x16f: shl     $0x10,%r8d
     +0x173: or      %edx,%r8d
     +0x176: shr     $0x4,%esi
     +0x179: movzbl  -0x1(%rax),%edx
     +0x17d: shl     $0x4,%edx
     +0x180: or      %esi,%edx
     +0x182: movzbl  (%rax),%esi
     +0x185: shl     $0xc,%esi
     +0x188: or      %edx,%esi
     +0x18a: mov     $0x80000,%edx
     +0x18f: sub     %r8d,%edx
     +0x192: mov     %edx,0x1420(%rsp,%rcx,8)
     +0x199: mov     $0x80000,%edx
     +0x19e: sub     %esi,%edx
     +0x1a0: mov     %edx,0x1424(%rsp,%rcx,8)
     +0x1a7: inc     %rcx
     +0x1aa: add     $0x5,%rax
     +0x1ae: cmp     $0x180,%rcx
     +0x1b5: jne     <mldsa65_verify_internal+0x160>
     +0x1b7: lea     0x7b4(%rdi),%rax
     +0x1be: mov     $0x180,%ecx
     +0x1c3: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x1d0: movzwl  -0x4(%rax),%edx
     +0x1d4: movzbl  -0x2(%rax),%esi
     +0x1d8: mov     %esi,%r8d
     +0x1db: and     $0xf,%r8d
     +0x1df: shl     $0x10,%r8d
     +0x1e3: or      %edx,%r8d
     +0x1e6: shr     $0x4,%esi
     +0x1e9: movzbl  -0x1(%rax),%edx
     +0x1ed: shl     $0x4,%edx
     +0x1f0: or      %esi,%edx
     +0x1f2: movzbl  (%rax),%esi
     +0x1f5: shl     $0xc,%esi
     +0x1f8: or      %edx,%esi
     +0x1fa: mov     $0x80000,%edx
     +0x1ff: sub     %r8d,%edx
     +0x202: mov     %edx,0x1420(%rsp,%rcx,8)
     +0x209: mov     $0x80000,%edx
     +0x20e: sub     %esi,%edx
     +0x210: mov     %edx,0x1424(%rsp,%rcx,8)
     +0x217: inc     %rcx
     +0x21a: add     $0x5,%rax
     +0x21e: cmp     $0x200,%rcx
     +0x225: jne     <mldsa65_verify_internal+0x1d0>
     +0x227: mov     %rdi,0x28(%rsp)
     +0x22c: lea     0xa34(%rdi),%rax
     +0x233: mov     $0x200,%ecx
     +0x238: nopl    0x0(%rax,%rax,1)
     +0x240: movzwl  -0x4(%rax),%edx
     +0x244: movzbl  -0x2(%rax),%esi
     +0x248: mov     %esi,%edi
     +0x24a: and     $0xf,%edi
     +0x24d: shl     $0x10,%edi
     +0x250: or      %edx,%edi
     +0x252: shr     $0x4,%esi
     +0x255: movzbl  -0x1(%rax),%edx
     +0x259: shl     $0x4,%edx
     +0x25c: or      %esi,%edx
     +0x25e: movzbl  (%rax),%esi
     +0x261: shl     $0xc,%esi
     +0x264: or      %edx,%esi
     +0x266: mov     $0x80000,%edx
     +0x26b: sub     %edi,%edx
     +0x26d: mov     %edx,0x1420(%rsp,%rcx,8)
     +0x274: mov     $0x80000,%edx
     +0x279: sub     %esi,%edx
     +0x27b: mov     %edx,0x1424(%rsp,%rcx,8)
     +0x282: inc     %rcx
     +0x285: add     $0x5,%rax
     +0x289: cmp     $0x280,%rcx
     +0x290: jne     <mldsa65_verify_internal+0x240>
     +0x292: lea     0x1420(%rsp),%rdi
     +0x29a: mov     $0x7ff3c,%esi
     +0x29f: call    <mldsa65_polyvecl_chknorm>
     +0x2a4: test    %eax,%eax
     +0x2a6: je      <mldsa65_verify_internal+0x3cf>
     +0x2ac: mov     $0xfffffffa,%r14d
     +0x2b2: lea     0x520(%rsp),%rbx
     +0x2ba: mov     $0x400,%edx
     +0x2bf: mov     %rbx,%rdi
     +0x2c2: xor     %esi,%esi
     +0x2c4: call    <memset>
     +0x2c9: lea     0x920(%rsp),%rbx
     +0x2d1: mov     $0x400,%edx
     +0x2d6: mov     %rbx,%rdi
     +0x2d9: xor     %esi,%esi
     +0x2db: call    <memset>
     +0x2e0: lea     0x40(%rsp),%rbx
     +0x2e5: mov     $0x420,%edx
     +0x2ea: mov     %rbx,%rdi
     +0x2ed: xor     %esi,%esi
     +0x2ef: call    <memset>
     +0x2f4: lea     0xd20(%rsp),%rbx
     +0x2fc: mov     $0x400,%edx
     +0x301: mov     %rbx,%rdi
     +0x304: xor     %esi,%esi
     +0x306: call    <memset>
     +0x30b: lea     0x1420(%rsp),%rbx
     +0x313: mov     $0x1400,%edx
     +0x318: mov     %rbx,%rdi
     +0x31b: xor     %esi,%esi
     +0x31d: call    <memset>
     +0x322: pxor    %xmm0,%xmm0
     +0x326: movdqa  %xmm0,0x4c0(%rsp)
     +0x32f: movdqa  %xmm0,0x4b0(%rsp)
     +0x338: movdqa  %xmm0,0x4a0(%rsp)
     +0x341: lea     0x4a0(%rsp),%rax
     +0x349: movdqa  %xmm0,0x480(%rsp)
     +0x352: movdqa  %xmm0,0x470(%rsp)
     +0x35b: movdqa  %xmm0,0x460(%rsp)
     +0x364: lea     0x460(%rsp),%rax
     +0x36c: movdqa  %xmm0,0x510(%rsp)
     +0x375: movdqa  %xmm0,0x500(%rsp)
     +0x37e: movdqa  %xmm0,0x4f0(%rsp)
     +0x387: movdqa  %xmm0,0x4e0(%rsp)
     +0x390: lea     0x4e0(%rsp),%rax
     +0x398: lea     0x1120(%rsp),%rbx
     +0x3a0: mov     $0x300,%edx
     +0x3a5: mov     %rbx,%rdi
     +0x3a8: xor     %esi,%esi
     +0x3aa: call    <memset>
     +0x3af: mov     %r14d,%eax
     +0x3b2: lea     -0x28(%rbp),%rsp
     +0x3b6: pop     %rbx
     +0x3b7: pop     %r12
     +0x3b9: pop     %r13
     +0x3bb: pop     %r14
     +0x3bd: pop     %r15
     +0x3bf: pop     %rbp
     +0x3c0: xor     %ecx,%ecx
     +0x3c2: xor     %edi,%edi
     +0x3c4: xor     %edx,%edx
     +0x3c6: xor     %esi,%esi
     +0x3c8: xor     %r8d,%r8d
     +0x3cb: xor     %r9d,%r9d
     +0x3ce: ret     
     +0x3cf: test    %r15d,%r15d
     +0x3d2: je      <mldsa65_verify_internal+0x412>
     +0x3d4: movups  (%r12),%xmm0
     +0x3d9: movups  0x10(%r12),%xmm1
     +0x3df: movdqu  0x20(%r12),%xmm2
     +0x3e6: movups  0x30(%r12),%xmm3
     +0x3ec: movaps  %xmm3,0x510(%rsp)
     +0x3f4: movdqa  %xmm2,0x500(%rsp)
     +0x3fd: movaps  %xmm1,0x4f0(%rsp)
     +0x405: movaps  %xmm0,0x4e0(%rsp)
     +0x40d: jmp     <mldsa65_verify_internal+0xff6>
     +0x412: pxor    %xmm0,%xmm0
     +0x416: movdqu  %xmm0,0xfc(%rsp)
     +0x41f: movdqa  %xmm0,0xf0(%rsp)
     +0x428: movdqa  %xmm0,0xe0(%rsp)
     +0x431: movdqa  %xmm0,0xd0(%rsp)
     +0x43a: movdqa  %xmm0,0xc0(%rsp)
     +0x443: movdqa  %xmm0,0xb0(%rsp)
     +0x44c: movdqa  %xmm0,0xa0(%rsp)
     +0x455: movdqa  %xmm0,0x90(%rsp)
     +0x45e: movdqa  %xmm0,0x80(%rsp)
     +0x467: movdqa  %xmm0,0x70(%rsp)
     +0x46d: movdqa  %xmm0,0x60(%rsp)
     +0x473: movdqa  %xmm0,0x50(%rsp)
     +0x479: movdqa  %xmm0,0x40(%rsp)
     +0x47f: movups  (%rbx),%xmm0
     +0x482: movups  0x10(%rbx),%xmm1
     +0x486: movaps  %xmm0,0x40(%rsp)
     +0x48b: movaps  %xmm1,0x50(%rsp)
     +0x490: movups  0x20(%rbx),%xmm0
     +0x494: movups  0x30(%rbx),%xmm1
     +0x498: movaps  %xmm0,0x60(%rsp)
     +0x49d: movaps  %xmm1,0x70(%rsp)
     +0x4a2: movups  0x40(%rbx),%xmm0
     +0x4a6: movups  0x50(%rbx),%xmm1
     +0x4aa: xorps   0x80(%rsp),%xmm0
     +0x4b2: xorps   0x90(%rsp),%xmm1
     +0x4ba: movaps  %xmm0,0x80(%rsp)
     +0x4c2: movaps  %xmm1,0x90(%rsp)
     +0x4ca: movups  0x60(%rbx),%xmm0
     +0x4ce: movups  0x70(%rbx),%xmm1
     +0x4d2: xorps   0xa0(%rsp),%xmm0
     +0x4da: xorps   0xb0(%rsp),%xmm1
     +0x4e2: movaps  %xmm0,0xa0(%rsp)
     +0x4ea: movaps  %xmm1,0xb0(%rsp)
     +0x4f2: mov     0x80(%rbx),%rax
     +0x4f9: xor     %rax,0xc0(%rsp)
     +0x501: lea     0x40(%rsp),%r15
     +0x506: mov     %r15,%rdi
     +0x509: call    <mldsa_keccakf1600_permute>
     +0x50e: movups  0x88(%rbx),%xmm0
     +0x515: movups  0x98(%rbx),%xmm1
     +0x51c: xorps   0x40(%rsp),%xmm0
     +0x521: xorps   0x50(%rsp),%xmm1
     +0x526: movaps  %xmm0,0x40(%rsp)
     +0x52b: movaps  %xmm1,0x50(%rsp)
     +0x530: movups  0xa8(%rbx),%xmm0
     +0x537: movups  0xb8(%rbx),%xmm1
     +0x53e: xorps   0x60(%rsp),%xmm0
     +0x543: xorps   0x70(%rsp),%xmm1
     +0x548: movaps  %xmm0,0x60(%rsp)
     +0x54d: movaps  %xmm1,0x70(%rsp)
     +0x552: movups  0xc8(%rbx),%xmm0
     +0x559: movups  0xd8(%rbx),%xmm1
     +0x560: xorps   0x80(%rsp),%xmm0
     +0x568: xorps   0x90(%rsp),%xmm1
     +0x570: movaps  %xmm0,0x80(%rsp)
     +0x578: movaps  %xmm1,0x90(%rsp)
     +0x580: movups  0xe8(%rbx),%xmm0
     +0x587: movups  0xf8(%rbx),%xmm1
     +0x58e: xorps   0xa0(%rsp),%xmm0
     +0x596: xorps   0xb0(%rsp),%xmm1
     +0x59e: movaps  %xmm0,0xa0(%rsp)
     +0x5a6: movaps  %xmm1,0xb0(%rsp)
     +0x5ae: mov     0x108(%rbx),%rax
     +0x5b5: xor     %rax,0xc0(%rsp)
     +0x5bd: mov     %r15,%rdi
     +0x5c0: call    <mldsa_keccakf1600_permute>
     +0x5c5: movups  0x110(%rbx),%xmm0
     +0x5cc: movups  0x120(%rbx),%xmm1
     +0x5d3: xorps   0x40(%rsp),%xmm0
     +0x5d8: xorps   0x50(%rsp),%xmm1
     +0x5dd: movaps  %xmm0,0x40(%rsp)
     +0x5e2: movaps  %xmm1,0x50(%rsp)
     +0x5e7: movups  0x130(%rbx),%xmm0
     +0x5ee: movups  0x140(%rbx),%xmm1
     +0x5f5: xorps   0x60(%rsp),%xmm0
     +0x5fa: xorps   0x70(%rsp),%xmm1
     +0x5ff: movaps  %xmm0,0x60(%rsp)
     +0x604: movaps  %xmm1,0x70(%rsp)
     +0x609: movups  0x150(%rbx),%xmm0
     +0x610: movups  0x160(%rbx),%xmm1
     +0x617: xorps   0x80(%rsp),%xmm0
     +0x61f: xorps   0x90(%rsp),%xmm1
     +0x627: movaps  %xmm0,0x80(%rsp)
     +0x62f: movaps  %xmm1,0x90(%rsp)
     +0x637: movups  0x170(%rbx),%xmm0
     +0x63e: movups  0x180(%rbx),%xmm1
     +0x645: xorps   0xa0(%rsp),%xmm0
     +0x64d: xorps   0xb0(%rsp),%xmm1
     +0x655: movaps  %xmm0,0xa0(%rsp)
     +0x65d: movaps  %xmm1,0xb0(%rsp)
     +0x665: mov     0x190(%rbx),%rax
     +0x66c: xor     %rax,0xc0(%rsp)
     +0x674: mov     %r15,%rdi
     +0x677: call    <mldsa_keccakf1600_permute>
     +0x67c: movups  0x198(%rbx),%xmm0
     +0x683: movups  0x1a8(%rbx),%xmm1
     +0x68a: xorps   0x40(%rsp),%xmm0
     +0x68f: xorps   0x50(%rsp),%xmm1
     +0x694: movaps  %xmm0,0x40(%rsp)
     +0x699: movaps  %xmm1,0x50(%rsp)
     +0x69e: movups  0x1b8(%rbx),%xmm0
     +0x6a5: movups  0x1c8(%rbx),%xmm1
     +0x6ac: xorps   0x60(%rsp),%xmm0
     +0x6b1: xorps   0x70(%rsp),%xmm1
     +0x6b6: movaps  %xmm0,0x60(%rsp)
     +0x6bb: movaps  %xmm1,0x70(%rsp)
     +0x6c0: movups  0x1d8(%rbx),%xmm0
     +0x6c7: movups  0x1e8(%rbx),%xmm1
     +0x6ce: xorps   0x80(%rsp),%xmm0
     +0x6d6: xorps   0x90(%rsp),%xmm1
     +0x6de: movaps  %xmm0,0x80(%rsp)
     +0x6e6: movaps  %xmm1,0x90(%rsp)
     +0x6ee: movups  0x1f8(%rbx),%xmm0
     +0x6f5: movups  0x208(%rbx),%xmm1
     +0x6fc: xorps   0xa0(%rsp),%xmm0
     +0x704: xorps   0xb0(%rsp),%xmm1
     +0x70c: movaps  %xmm0,0xa0(%rsp)
     +0x714: movaps  %xmm1,0xb0(%rsp)
     +0x71c: mov     0x218(%rbx),%rax
     +0x723: xor     %rax,0xc0(%rsp)
     +0x72b: mov     %r15,%rdi
     +0x72e: call    <mldsa_keccakf1600_permute>
     +0x733: movups  0x220(%rbx),%xmm0
     +0x73a: movups  0x230(%rbx),%xmm1
     +0x741: xorps   0x40(%rsp),%xmm0
     +0x746: xorps   0x50(%rsp),%xmm1
     +0x74b: movaps  %xmm0,0x40(%rsp)
     +0x750: movaps  %xmm1,0x50(%rsp)
     +0x755: movups  0x240(%rbx),%xmm0
     +0x75c: movups  0x250(%rbx),%xmm1
     +0x763: xorps   0x60(%rsp),%xmm0
     +0x768: xorps   0x70(%rsp),%xmm1
     +0x76d: movaps  %xmm0,0x60(%rsp)
     +0x772: movaps  %xmm1,0x70(%rsp)
     +0x777: movups  0x260(%rbx),%xmm0
     +0x77e: movups  0x270(%rbx),%xmm1
     +0x785: xorps   0x80(%rsp),%xmm0
     +0x78d: xorps   0x90(%rsp),%xmm1
     +0x795: movaps  %xmm0,0x80(%rsp)
     +0x79d: movaps  %xmm1,0x90(%rsp)
     +0x7a5: movups  0x280(%rbx),%xmm0
     +0x7ac: movups  0x290(%rbx),%xmm1
     +0x7b3: xorps   0xa0(%rsp),%xmm0
     +0x7bb: xorps   0xb0(%rsp),%xmm1
     +0x7c3: movaps  %xmm0,0xa0(%rsp)
     +0x7cb: movaps  %xmm1,0xb0(%rsp)
     +0x7d3: mov     0x2a0(%rbx),%rax
     +0x7da: xor     %rax,0xc0(%rsp)
     +0x7e2: mov     %r15,%rdi
     +0x7e5: call    <mldsa_keccakf1600_permute>
     +0x7ea: movups  0x2a8(%rbx),%xmm0
     +0x7f1: movups  0x2b8(%rbx),%xmm1
     +0x7f8: xorps   0x40(%rsp),%xmm0
     +0x7fd: xorps   0x50(%rsp),%xmm1
     +0x802: movaps  %xmm0,0x40(%rsp)
     +0x807: movaps  %xmm1,0x50(%rsp)
     +0x80c: movups  0x2c8(%rbx),%xmm0
     +0x813: movups  0x2d8(%rbx),%xmm1
     +0x81a: xorps   0x60(%rsp),%xmm0
     +0x81f: xorps   0x70(%rsp),%xmm1
     +0x824: movaps  %xmm0,0x60(%rsp)
     +0x829: movaps  %xmm1,0x70(%rsp)
     +0x82e: movups  0x2e8(%rbx),%xmm0
     +0x835: movups  0x2f8(%rbx),%xmm1
     +0x83c: xorps   0x80(%rsp),%xmm0
     +0x844: xorps   0x90(%rsp),%xmm1
     +0x84c: movaps  %xmm0,0x80(%rsp)
     +0x854: movaps  %xmm1,0x90(%rsp)
     +0x85c: movups  0x308(%rbx),%xmm0
     +0x863: movups  0x318(%rbx),%xmm1
     +0x86a: xorps   0xa0(%rsp),%xmm0
     +0x872: xorps   0xb0(%rsp),%xmm1
     +0x87a: movaps  %xmm0,0xa0(%rsp)
     +0x882: movaps  %xmm1,0xb0(%rsp)
     +0x88a: mov     0x328(%rbx),%rax
     +0x891: xor     %rax,0xc0(%rsp)
     +0x899: mov     %r15,%rdi
     +0x89c: call    <mldsa_keccakf1600_permute>
     +0x8a1: movups  0x330(%rbx),%xmm0
     +0x8a8: movups  0x340(%rbx),%xmm1
     +0x8af: xorps   0x40(%rsp),%xmm0
     +0x8b4: xorps   0x50(%rsp),%xmm1
     +0x8b9: movaps  %xmm0,0x40(%rsp)
     +0x8be: movaps  %xmm1,0x50(%rsp)
     +0x8c3: movups  0x350(%rbx),%xmm0
     +0x8ca: movups  0x360(%rbx),%xmm1
     +0x8d1: xorps   0x60(%rsp),%xmm0
     +0x8d6: xorps   0x70(%rsp),%xmm1
     +0x8db: movaps  %xmm0,0x60(%rsp)
     +0x8e0: movaps  %xmm1,0x70(%rsp)
     +0x8e5: movups  0x370(%rbx),%xmm0
     +0x8ec: movups  0x380(%rbx),%xmm1
     +0x8f3: xorps   0x80(%rsp),%xmm0
     +0x8fb: xorps   0x90(%rsp),%xmm1
     +0x903: movaps  %xmm0,0x80(%rsp)
     +0x90b: movaps  %xmm1,0x90(%rsp)
     +0x913: movups  0x390(%rbx),%xmm0
     +0x91a: movups  0x3a0(%rbx),%xmm1
     +0x921: xorps   0xa0(%rsp),%xmm0
     +0x929: xorps   0xb0(%rsp),%xmm1
     +0x931: movaps  %xmm0,0xa0(%rsp)
     +0x939: movaps  %xmm1,0xb0(%rsp)
     +0x941: mov     0x3b0(%rbx),%rax
     +0x948: xor     %rax,0xc0(%rsp)
     +0x950: mov     %r15,%rdi
     +0x953: call    <mldsa_keccakf1600_permute>
     +0x958: movups  0x3b8(%rbx),%xmm0
     +0x95f: movups  0x3c8(%rbx),%xmm1
     +0x966: xorps   0x40(%rsp),%xmm0
     +0x96b: xorps   0x50(%rsp),%xmm1
     +0x970: movaps  %xmm0,0x40(%rsp)
     +0x975: movaps  %xmm1,0x50(%rsp)
     +0x97a: movups  0x3d8(%rbx),%xmm0
     +0x981: movups  0x3e8(%rbx),%xmm1
     +0x988: xorps   0x60(%rsp),%xmm0
     +0x98d: xorps   0x70(%rsp),%xmm1
     +0x992: movaps  %xmm0,0x60(%rsp)
     +0x997: movaps  %xmm1,0x70(%rsp)
     +0x99c: movups  0x3f8(%rbx),%xmm0
     +0x9a3: movups  0x408(%rbx),%xmm1
     +0x9aa: xorps   0x80(%rsp),%xmm0
     +0x9b2: xorps   0x90(%rsp),%xmm1
     +0x9ba: movaps  %xmm0,0x80(%rsp)
     +0x9c2: movaps  %xmm1,0x90(%rsp)
     +0x9ca: movups  0x418(%rbx),%xmm0
     +0x9d1: movups  0x428(%rbx),%xmm1
     +0x9d8: xorps   0xa0(%rsp),%xmm0
     +0x9e0: xorps   0xb0(%rsp),%xmm1
     +0x9e8: movaps  %xmm0,0xa0(%rsp)
     +0x9f0: movaps  %xmm1,0xb0(%rsp)
     +0x9f8: mov     0x438(%rbx),%rax
     +0x9ff: xor     %rax,0xc0(%rsp)
     +0xa07: mov     %r15,%rdi
     +0xa0a: call    <mldsa_keccakf1600_permute>
     +0xa0f: movups  0x440(%rbx),%xmm0
     +0xa16: movups  0x450(%rbx),%xmm1
     +0xa1d: xorps   0x40(%rsp),%xmm0
     +0xa22: xorps   0x50(%rsp),%xmm1
     +0xa27: movaps  %xmm0,0x40(%rsp)
     +0xa2c: movaps  %xmm1,0x50(%rsp)
     +0xa31: movups  0x460(%rbx),%xmm0
     +0xa38: movups  0x470(%rbx),%xmm1
     +0xa3f: xorps   0x60(%rsp),%xmm0
     +0xa44: xorps   0x70(%rsp),%xmm1
     +0xa49: movaps  %xmm0,0x60(%rsp)
     +0xa4e: movaps  %xmm1,0x70(%rsp)
     +0xa53: movups  0x480(%rbx),%xmm0
     +0xa5a: movups  0x490(%rbx),%xmm1
     +0xa61: xorps   0x80(%rsp),%xmm0
     +0xa69: xorps   0x90(%rsp),%xmm1
     +0xa71: movaps  %xmm0,0x80(%rsp)
     +0xa79: movaps  %xmm1,0x90(%rsp)
     +0xa81: movups  0x4a0(%rbx),%xmm0
     +0xa88: movups  0x4b0(%rbx),%xmm1
     +0xa8f: xorps   0xa0(%rsp),%xmm0
     +0xa97: xorps   0xb0(%rsp),%xmm1
     +0xa9f: movaps  %xmm0,0xa0(%rsp)
     +0xaa7: movaps  %xmm1,0xb0(%rsp)
     +0xaaf: mov     0x4c0(%rbx),%rax
     +0xab6: xor     %rax,0xc0(%rsp)
     +0xabe: mov     %r15,%rdi
     +0xac1: call    <mldsa_keccakf1600_permute>
     +0xac6: movups  0x4c8(%rbx),%xmm0
     +0xacd: movups  0x4d8(%rbx),%xmm1
     +0xad4: xorps   0x40(%rsp),%xmm0
     +0xad9: xorps   0x50(%rsp),%xmm1
     +0xade: movaps  %xmm0,0x40(%rsp)
     +0xae3: movaps  %xmm1,0x50(%rsp)
     +0xae8: movups  0x4e8(%rbx),%xmm0
     +0xaef: movups  0x4f8(%rbx),%xmm1
     +0xaf6: xorps   0x60(%rsp),%xmm0
     +0xafb: xorps   0x70(%rsp),%xmm1
     +0xb00: movaps  %xmm0,0x60(%rsp)
     +0xb05: movaps  %xmm1,0x70(%rsp)
     +0xb0a: movups  0x508(%rbx),%xmm0
     +0xb11: movups  0x518(%rbx),%xmm1
     +0xb18: xorps   0x80(%rsp),%xmm0
     +0xb20: xorps   0x90(%rsp),%xmm1
     +0xb28: movaps  %xmm0,0x80(%rsp)
     +0xb30: movaps  %xmm1,0x90(%rsp)
     +0xb38: movups  0x528(%rbx),%xmm0
     +0xb3f: movups  0x538(%rbx),%xmm1
     +0xb46: xorps   0xa0(%rsp),%xmm0
     +0xb4e: xorps   0xb0(%rsp),%xmm1
     +0xb56: movaps  %xmm0,0xa0(%rsp)
     +0xb5e: movaps  %xmm1,0xb0(%rsp)
     +0xb66: mov     0x548(%rbx),%rax
     +0xb6d: xor     %rax,0xc0(%rsp)
     +0xb75: mov     %r15,%rdi
     +0xb78: call    <mldsa_keccakf1600_permute>
     +0xb7d: movups  0x550(%rbx),%xmm0
     +0xb84: movups  0x560(%rbx),%xmm1
     +0xb8b: xorps   0x40(%rsp),%xmm0
     +0xb90: xorps   0x50(%rsp),%xmm1
     +0xb95: movaps  %xmm0,0x40(%rsp)
     +0xb9a: movaps  %xmm1,0x50(%rsp)
     +0xb9f: movups  0x570(%rbx),%xmm0
     +0xba6: movups  0x580(%rbx),%xmm1
     +0xbad: xorps   0x60(%rsp),%xmm0
     +0xbb2: xorps   0x70(%rsp),%xmm1
     +0xbb7: movaps  %xmm0,0x60(%rsp)
     +0xbbc: movaps  %xmm1,0x70(%rsp)
     +0xbc1: movups  0x590(%rbx),%xmm0
     +0xbc8: movups  0x5a0(%rbx),%xmm1
     +0xbcf: xorps   0x80(%rsp),%xmm0
     +0xbd7: xorps   0x90(%rsp),%xmm1
     +0xbdf: movaps  %xmm0,0x80(%rsp)
     +0xbe7: movaps  %xmm1,0x90(%rsp)
     +0xbef: movups  0x5b0(%rbx),%xmm0
     +0xbf6: movups  0x5c0(%rbx),%xmm1
     +0xbfd: xorps   0xa0(%rsp),%xmm0
     +0xc05: xorps   0xb0(%rsp),%xmm1
     +0xc0d: movaps  %xmm0,0xa0(%rsp)
     +0xc15: movaps  %xmm1,0xb0(%rsp)
     +0xc1d: mov     0x5d0(%rbx),%rax
     +0xc24: xor     %rax,0xc0(%rsp)
     +0xc2c: mov     %r15,%rdi
     +0xc2f: call    <mldsa_keccakf1600_permute>
     +0xc34: movups  0x5d8(%rbx),%xmm0
     +0xc3b: movups  0x5e8(%rbx),%xmm1
     +0xc42: xorps   0x40(%rsp),%xmm0
     +0xc47: xorps   0x50(%rsp),%xmm1
     +0xc4c: movaps  %xmm0,0x40(%rsp)
     +0xc51: movaps  %xmm1,0x50(%rsp)
     +0xc56: movups  0x5f8(%rbx),%xmm0
     +0xc5d: movups  0x608(%rbx),%xmm1
     +0xc64: xorps   0x60(%rsp),%xmm0
     +0xc69: xorps   0x70(%rsp),%xmm1
     +0xc6e: movaps  %xmm0,0x60(%rsp)
     +0xc73: movaps  %xmm1,0x70(%rsp)
     +0xc78: movups  0x618(%rbx),%xmm0
     +0xc7f: movups  0x628(%rbx),%xmm1
     +0xc86: xorps   0x80(%rsp),%xmm0
     +0xc8e: xorps   0x90(%rsp),%xmm1
     +0xc96: movaps  %xmm0,0x80(%rsp)
     +0xc9e: movaps  %xmm1,0x90(%rsp)
     +0xca6: movups  0x638(%rbx),%xmm0
     +0xcad: movups  0x648(%rbx),%xmm1
     +0xcb4: xorps   0xa0(%rsp),%xmm0
     +0xcbc: xorps   0xb0(%rsp),%xmm1
     +0xcc4: movaps  %xmm0,0xa0(%rsp)
     +0xccc: movaps  %xmm1,0xb0(%rsp)
     +0xcd4: mov     0x658(%rbx),%rax
     +0xcdb: xor     %rax,0xc0(%rsp)
     +0xce3: mov     %r15,%rdi
     +0xce6: call    <mldsa_keccakf1600_permute>
     +0xceb: movups  0x660(%rbx),%xmm0
     +0xcf2: movups  0x670(%rbx),%xmm1
     +0xcf9: xorps   0x40(%rsp),%xmm0
     +0xcfe: xorps   0x50(%rsp),%xmm1
     +0xd03: movaps  %xmm0,0x40(%rsp)
     +0xd08: movaps  %xmm1,0x50(%rsp)
     +0xd0d: movups  0x680(%rbx),%xmm0
     +0xd14: movups  0x690(%rbx),%xmm1
     +0xd1b: xorps   0x60(%rsp),%xmm0
     +0xd20: xorps   0x70(%rsp),%xmm1
     +0xd25: movaps  %xmm0,0x60(%rsp)
     +0xd2a: movaps  %xmm1,0x70(%rsp)
     +0xd2f: movups  0x6a0(%rbx),%xmm0
     +0xd36: movups  0x6b0(%rbx),%xmm1
     +0xd3d: xorps   0x80(%rsp),%xmm0
     +0xd45: xorps   0x90(%rsp),%xmm1
     +0xd4d: movaps  %xmm0,0x80(%rsp)
     +0xd55: movaps  %xmm1,0x90(%rsp)
     +0xd5d: movups  0x6c0(%rbx),%xmm0
     +0xd64: movups  0x6d0(%rbx),%xmm1
     +0xd6b: xorps   0xa0(%rsp),%xmm0
     +0xd73: xorps   0xb0(%rsp),%xmm1
     +0xd7b: movaps  %xmm0,0xa0(%rsp)
     +0xd83: movaps  %xmm1,0xb0(%rsp)
     +0xd8b: mov     0x6e0(%rbx),%rax
     +0xd92: xor     %rax,0xc0(%rsp)
     +0xd9a: mov     %r15,%rdi
     +0xd9d: call    <mldsa_keccakf1600_permute>
     +0xda2: movups  0x6e8(%rbx),%xmm0
     +0xda9: movups  0x6f8(%rbx),%xmm1
     +0xdb0: xorps   0x40(%rsp),%xmm0
     +0xdb5: xorps   0x50(%rsp),%xmm1
     +0xdba: movaps  %xmm0,0x40(%rsp)
     +0xdbf: movaps  %xmm1,0x50(%rsp)
     +0xdc4: movups  0x708(%rbx),%xmm0
     +0xdcb: movups  0x718(%rbx),%xmm1
     +0xdd2: xorps   0x60(%rsp),%xmm0
     +0xdd7: xorps   0x70(%rsp),%xmm1
     +0xddc: movaps  %xmm0,0x60(%rsp)
     +0xde1: movaps  %xmm1,0x70(%rsp)
     +0xde6: movups  0x728(%rbx),%xmm0
     +0xded: movups  0x738(%rbx),%xmm1
     +0xdf4: xorps   0x80(%rsp),%xmm0
     +0xdfc: xorps   0x90(%rsp),%xmm1
     +0xe04: movaps  %xmm0,0x80(%rsp)
     +0xe0c: movaps  %xmm1,0x90(%rsp)
     +0xe14: movups  0x748(%rbx),%xmm0
     +0xe1b: movups  0x758(%rbx),%xmm1
     +0xe22: xorps   0xa0(%rsp),%xmm0
     +0xe2a: xorps   0xb0(%rsp),%xmm1
     +0xe32: movaps  %xmm0,0xa0(%rsp)
     +0xe3a: movaps  %xmm1,0xb0(%rsp)
     +0xe42: mov     0x768(%rbx),%rax
     +0xe49: xor     %rax,0xc0(%rsp)
     +0xe51: mov     %r15,%rdi
     +0xe54: call    <mldsa_keccakf1600_permute>
     +0xe59: movups  0x770(%rbx),%xmm0
     +0xe60: xorps   0x40(%rsp),%xmm0
     +0xe65: movaps  %xmm0,0x40(%rsp)
     +0xe6a: movups  0x780(%rbx),%xmm0
     +0xe71: xorps   0x50(%rsp),%xmm0
     +0xe76: movaps  %xmm0,0x50(%rsp)
     +0xe7b: movups  0x790(%rbx),%xmm0
     +0xe82: xorps   0x60(%rsp),%xmm0
     +0xe87: movaps  %xmm0,0x60(%rsp)
     +0xe8c: xorb    $0x1f,0x70(%rsp)
     +0xe91: xorb    $0x80,0xc7(%rsp)
     +0xe99: movl    $0x88,0x108(%rsp)
     +0xea4: mov     %r15,%rdi
     +0xea7: call    <mldsa_keccakf1600_permute>
     +0xeac: movaps  0x40(%rsp),%xmm0
     +0xeb1: movaps  0x50(%rsp),%xmm1
     +0xeb6: movdqa  0x60(%rsp),%xmm2
     +0xebc: movaps  0x70(%rsp),%xmm3
     +0xec1: movaps  %xmm3,0xd50(%rsp)
     +0xec9: movdqa  %xmm2,0xd40(%rsp)
     +0xed2: movaps  %xmm1,0xd30(%rsp)
     +0xeda: movaps  %xmm0,0xd20(%rsp)
     +0xee2: xorps   %xmm0,%xmm0
     +0xee5: movaps  %xmm0,0x80(%rsp)
     +0xeed: movaps  %xmm0,0x90(%rsp)
     +0xef5: movaps  %xmm0,0xa0(%rsp)
     +0xefd: movaps  %xmm0,0xb0(%rsp)
     +0xf05: movaps  %xmm0,0xc0(%rsp)
     +0xf0d: movaps  %xmm0,0xd0(%rsp)
     +0xf15: movaps  %xmm0,0xe0(%rsp)
     +0xf1d: movaps  %xmm0,0xf0(%rsp)
     +0xf25: movaps  %xmm0,0x100(%rsp)
     +0xf2d: movaps  %xmm0,0x40(%rsp)
     +0xf32: movaps  %xmm0,0x50(%rsp)
     +0xf37: movaps  %xmm0,0x60(%rsp)
     +0xf3c: movaps  %xmm0,0x70(%rsp)
     +0xf41: movaps  %xmm0,0x100(%rsp)
     +0xf49: movaps  %xmm0,0xf0(%rsp)
     +0xf51: movaps  %xmm0,0xe0(%rsp)
     +0xf59: movaps  %xmm0,0xd0(%rsp)
     +0xf61: movaps  %xmm0,0xc0(%rsp)
     +0xf69: movaps  %xmm0,0xb0(%rsp)
     +0xf71: movaps  %xmm0,0xa0(%rsp)
     +0xf79: movaps  %xmm0,0x90(%rsp)
     +0xf81: movaps  %xmm0,0x80(%rsp)
     +0xf89: movaps  %xmm0,0x70(%rsp)
     +0xf8e: movaps  %xmm0,0x60(%rsp)
     +0xf93: movaps  %xmm0,0x50(%rsp)
     +0xf98: movaps  %xmm0,0x40(%rsp)
     +0xf9d: mov     %r13,0x8(%rsp)
     +0xfa2: mov     %r12,(%rsp)
     +0xfa6: lea     0x4e0(%rsp),%rdi
     +0xfae: lea     0xd20(%rsp),%r15
     +0xfb6: mov     $0x40,%esi
     +0xfbb: mov     $0x40,%ecx
     +0xfc0: mov     %r15,%rdx
     +0xfc3: mov     0x498(%rsp),%r8
     +0xfcb: mov     %r14,%r9
     +0xfce: call    <mld_H65>
     +0xfd3: xorps   %xmm0,%xmm0
     +0xfd6: movaps  %xmm0,0xd50(%rsp)
     +0xfde: movaps  %xmm0,0xd40(%rsp)
     +0xfe6: movaps  %xmm0,0xd30(%rsp)
     +0xfee: movaps  %xmm0,0xd20(%rsp)
     +0xff6: movabs  $0x380200100000000,%r12
    +0x1000: lea     0x1420(%rsp),%r14
    +0x1008: mov     %r14,%rdi
    +0x100b: call    <mldsa_poly_ntt>
    +0x1010: lea     0x1820(%rsp),%rdi
    +0x1018: call    <mldsa_poly_ntt>
    +0x101d: lea     0x1c20(%rsp),%rdi
    +0x1025: call    <mldsa_poly_ntt>
    +0x102a: lea     0x2020(%rsp),%rdi
    +0x1032: call    <mldsa_poly_ntt>
    +0x1037: lea     0x2420(%rsp),%rdi
    +0x103f: call    <mldsa_poly_ntt>
    +0x1044: movdqu  (%rbx),%xmm0
    +0x1048: movups  0x10(%rbx),%xmm1
    +0x104c: movaps  %xmm1,0x450(%rsp)
    +0x1054: movdqa  %xmm0,0x440(%rsp)
    +0x105d: lea     0xd20(%rsp),%r15
    +0x1065: lea     0x460(%rsp),%rsi
    +0x106d: mov     %r15,%rdi
    +0x1070: call    <mldsa65_poly_challenge>
    +0x1075: mov     %r15,%rdi
    +0x1078: call    <mldsa_poly_ntt>
    +0x107d: add     $0x21,%rbx
    +0x1081: lea     0x1124(%rsp),%r15
    +0x1089: xor     %r13d,%r13d
    +0x108c: lea     0x920(%rsp),%rdi
    +0x1094: lea     0x40(%rsp),%rsi
    +0x1099: mov     %r14,%rdx
    +0x109c: mov     %r13d,%ecx
    +0x109f: call    <mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy>
    +0x10a4: mov     %rbx,%rax
    +0x10a7: xor     %ecx,%ecx
    +0x10a9: pxor    %xmm2,%xmm2
    +0x10ad: movq    0x1265b(%rip),%xmm3
    +0x10b5: movq    0x12663(%rip),%xmm4
    +0x10bd: nopl    (%rax)
    +0x10c0: mov     (%rax),%edx
    +0x10c2: movd    %edx,%xmm0
    +0x10c6: movzbl  (%rax),%esi
    +0x10c9: mov     %edx,%edi
    +0x10cb: shr     $0x16,%edi
    +0x10ce: and     $0x3,%edi
    +0x10d1: shr     $0xc,%edx
    +0x10d4: and     $0xf,%edx
    +0x10d7: shr     $0x2,%esi
    +0x10da: punpcklbw %xmm2,%xmm0
    +0x10de: pmullw  %xmm3,%xmm0
    +0x10e2: pand    %xmm4,%xmm0
    +0x10e6: movzbl  -0x1(%rax),%r8d
    +0x10eb: movd    %r8d,%xmm1
    +0x10f0: pinsrw  $0x1,%esi,%xmm1
    +0x10f5: pinsrw  $0x2,%edx,%xmm1
    +0x10fa: pinsrw  $0x3,%edi,%xmm1
    +0x10ff: por     %xmm0,%xmm1
    +0x1103: punpcklwd %xmm2,%xmm1
    +0x1107: movdqa  %xmm1,0x520(%rsp,%rcx,1)
    +0x1110: add     $0x10,%rcx
    +0x1114: add     $0x5,%rax
    +0x1118: cmp     $0x400,%rcx
    +0x111f: jne     <mldsa65_verify_internal+0x10c0>
    +0x1121: movdqa  0x520(%rsp),%xmm0
    +0x112a: movdqa  0x530(%rsp),%xmm1
    +0x1133: movdqa  0x540(%rsp),%xmm2
    +0x113c: movdqa  0x550(%rsp),%xmm3
    +0x1145: pslld   $0xd,%xmm0
    +0x114a: pslld   $0xd,%xmm1
    +0x114f: movdqa  %xmm0,0x520(%rsp)
    +0x1158: movdqa  %xmm1,0x530(%rsp)
    +0x1161: pslld   $0xd,%xmm2
    +0x1166: pslld   $0xd,%xmm3
    +0x116b: movdqa  %xmm2,0x540(%rsp)
    +0x1174: movdqa  %xmm3,0x550(%rsp)
    +0x117d: movdqa  0x560(%rsp),%xmm0
    +0x1186: movdqa  0x570(%rsp),%xmm1
    +0x118f: pslld   $0xd,%xmm0
    +0x1194: pslld   $0xd,%xmm1
    +0x1199: movdqa  %xmm0,0x560(%rsp)
    +0x11a2: movdqa  %xmm1,0x570(%rsp)
    +0x11ab: movdqa  0x580(%rsp),%xmm0
    +0x11b4: movdqa  0x590(%rsp),%xmm1
    +0x11bd: pslld   $0xd,%xmm0
    +0x11c2: pslld   $0xd,%xmm1
    +0x11c7: movdqa  %xmm0,0x580(%rsp)
    +0x11d0: movdqa  %xmm1,0x590(%rsp)
    +0x11d9: movdqa  0x5a0(%rsp),%xmm0
    +0x11e2: movdqa  0x5b0(%rsp),%xmm1
    +0x11eb: pslld   $0xd,%xmm0
    +0x11f0: pslld   $0xd,%xmm1
    +0x11f5: movdqa  %xmm0,0x5a0(%rsp)
    +0x11fe: movdqa  %xmm1,0x5b0(%rsp)
    +0x1207: movdqa  0x5c0(%rsp),%xmm0
    +0x1210: movdqa  0x5d0(%rsp),%xmm1
    +0x1219: pslld   $0xd,%xmm0
    +0x121e: pslld   $0xd,%xmm1
    +0x1223: movdqa  %xmm0,0x5c0(%rsp)
    +0x122c: movdqa  %xmm1,0x5d0(%rsp)
    +0x1235: movdqa  0x5e0(%rsp),%xmm0
    +0x123e: movdqa  0x5f0(%rsp),%xmm1
    +0x1247: pslld   $0xd,%xmm0
    +0x124c: pslld   $0xd,%xmm1
    +0x1251: movdqa  %xmm0,0x5e0(%rsp)
    +0x125a: movdqa  %xmm1,0x5f0(%rsp)
    +0x1263: movdqa  0x600(%rsp),%xmm0
    +0x126c: movdqa  0x610(%rsp),%xmm1
    +0x1275: pslld   $0xd,%xmm0
    +0x127a: pslld   $0xd,%xmm1
    +0x127f: movdqa  %xmm0,0x600(%rsp)
    +0x1288: movdqa  %xmm1,0x610(%rsp)
    +0x1291: movdqa  0x620(%rsp),%xmm0
    +0x129a: movdqa  0x630(%rsp),%xmm1
    +0x12a3: pslld   $0xd,%xmm0
    +0x12a8: pslld   $0xd,%xmm1
    +0x12ad: movdqa  %xmm0,0x620(%rsp)
    +0x12b6: movdqa  %xmm1,0x630(%rsp)
    +0x12bf: movdqa  0x640(%rsp),%xmm0
    +0x12c8: movdqa  0x650(%rsp),%xmm1
    +0x12d1: pslld   $0xd,%xmm0
    +0x12d6: pslld   $0xd,%xmm1
    +0x12db: movdqa  %xmm0,0x640(%rsp)
    +0x12e4: movdqa  %xmm1,0x650(%rsp)
    +0x12ed: movdqa  0x660(%rsp),%xmm0
    +0x12f6: movdqa  0x670(%rsp),%xmm1
    +0x12ff: pslld   $0xd,%xmm0
    +0x1304: pslld   $0xd,%xmm1
    +0x1309: movdqa  %xmm0,0x660(%rsp)
    +0x1312: movdqa  %xmm1,0x670(%rsp)
    +0x131b: movdqa  0x680(%rsp),%xmm0
    +0x1324: movdqa  0x690(%rsp),%xmm1
    +0x132d: pslld   $0xd,%xmm0
    +0x1332: pslld   $0xd,%xmm1
    +0x1337: movdqa  %xmm0,0x680(%rsp)
    +0x1340: movdqa  %xmm1,0x690(%rsp)
    +0x1349: movdqa  0x6a0(%rsp),%xmm0
    +0x1352: movdqa  0x6b0(%rsp),%xmm1
    +0x135b: pslld   $0xd,%xmm0
    +0x1360: pslld   $0xd,%xmm1
    +0x1365: movdqa  %xmm0,0x6a0(%rsp)
    +0x136e: movdqa  %xmm1,0x6b0(%rsp)
    +0x1377: movdqa  0x6c0(%rsp),%xmm0
    +0x1380: movdqa  0x6d0(%rsp),%xmm1
    +0x1389: pslld   $0xd,%xmm0
    +0x138e: pslld   $0xd,%xmm1
    +0x1393: movdqa  %xmm0,0x6c0(%rsp)
    +0x139c: movdqa  %xmm1,0x6d0(%rsp)
    +0x13a5: movdqa  0x6e0(%rsp),%xmm0
    +0x13ae: movdqa  0x6f0(%rsp),%xmm1
    +0x13b7: pslld   $0xd,%xmm0
    +0x13bc: pslld   $0xd,%xmm1
    +0x13c1: movdqa  %xmm0,0x6e0(%rsp)
    +0x13ca: movdqa  %xmm1,0x6f0(%rsp)
    +0x13d3: movdqa  0x700(%rsp),%xmm0
    +0x13dc: movdqa  0x710(%rsp),%xmm1
    +0x13e5: pslld   $0xd,%xmm0
    +0x13ea: pslld   $0xd,%xmm1
    +0x13ef: movdqa  %xmm0,0x700(%rsp)
    +0x13f8: movdqa  %xmm1,0x710(%rsp)
    +0x1401: movdqa  0x720(%rsp),%xmm0
    +0x140a: movdqa  0x730(%rsp),%xmm1
    +0x1413: pslld   $0xd,%xmm0
    +0x1418: pslld   $0xd,%xmm1
    +0x141d: movdqa  %xmm0,0x720(%rsp)
    +0x1426: movdqa  %xmm1,0x730(%rsp)
    +0x142f: movdqa  0x740(%rsp),%xmm0
    +0x1438: movdqa  0x750(%rsp),%xmm1
    +0x1441: pslld   $0xd,%xmm0
    +0x1446: pslld   $0xd,%xmm1
    +0x144b: movdqa  %xmm0,0x740(%rsp)
    +0x1454: movdqa  %xmm1,0x750(%rsp)
    +0x145d: movdqa  0x760(%rsp),%xmm0
    +0x1466: movdqa  0x770(%rsp),%xmm1
    +0x146f: pslld   $0xd,%xmm0
    +0x1474: pslld   $0xd,%xmm1
    +0x1479: movdqa  %xmm0,0x760(%rsp)
    +0x1482: movdqa  %xmm1,0x770(%rsp)
    +0x148b: movdqa  0x780(%rsp),%xmm0
    +0x1494: movdqa  0x790(%rsp),%xmm1
    +0x149d: pslld   $0xd,%xmm0
    +0x14a2: pslld   $0xd,%xmm1
    +0x14a7: movdqa  %xmm0,0x780(%rsp)
    +0x14b0: movdqa  %xmm1,0x790(%rsp)
    +0x14b9: movdqa  0x7a0(%rsp),%xmm0
    +0x14c2: movdqa  0x7b0(%rsp),%xmm1
    +0x14cb: pslld   $0xd,%xmm0
    +0x14d0: pslld   $0xd,%xmm1
    +0x14d5: movdqa  %xmm0,0x7a0(%rsp)
    +0x14de: movdqa  %xmm1,0x7b0(%rsp)
    +0x14e7: movdqa  0x7c0(%rsp),%xmm0
    +0x14f0: movdqa  0x7d0(%rsp),%xmm1
    +0x14f9: pslld   $0xd,%xmm0
    +0x14fe: pslld   $0xd,%xmm1
    +0x1503: movdqa  %xmm0,0x7c0(%rsp)
    +0x150c: movdqa  %xmm1,0x7d0(%rsp)
    +0x1515: movdqa  0x7e0(%rsp),%xmm0
    +0x151e: movdqa  0x7f0(%rsp),%xmm1
    +0x1527: pslld   $0xd,%xmm0
    +0x152c: pslld   $0xd,%xmm1
    +0x1531: movdqa  %xmm0,0x7e0(%rsp)
    +0x153a: movdqa  %xmm1,0x7f0(%rsp)
    +0x1543: movdqa  0x800(%rsp),%xmm0
    +0x154c: movdqa  0x810(%rsp),%xmm1
    +0x1555: pslld   $0xd,%xmm0
    +0x155a: pslld   $0xd,%xmm1
    +0x155f: movdqa  %xmm0,0x800(%rsp)
    +0x1568: movdqa  %xmm1,0x810(%rsp)
    +0x1571: movdqa  0x820(%rsp),%xmm0
    +0x157a: movdqa  0x830(%rsp),%xmm1
    +0x1583: pslld   $0xd,%xmm0
    +0x1588: pslld   $0xd,%xmm1
    +0x158d: movdqa  %xmm0,0x820(%rsp)
    +0x1596: movdqa  %xmm1,0x830(%rsp)
    +0x159f: movdqa  0x840(%rsp),%xmm0
    +0x15a8: movdqa  0x850(%rsp),%xmm1
    +0x15b1: pslld   $0xd,%xmm0
    +0x15b6: pslld   $0xd,%xmm1
    +0x15bb: movdqa  %xmm0,0x840(%rsp)
    +0x15c4: movdqa  %xmm1,0x850(%rsp)
    +0x15cd: movdqa  0x860(%rsp),%xmm0
    +0x15d6: movdqa  0x870(%rsp),%xmm1
    +0x15df: pslld   $0xd,%xmm0
    +0x15e4: pslld   $0xd,%xmm1
    +0x15e9: movdqa  %xmm0,0x860(%rsp)
    +0x15f2: movdqa  %xmm1,0x870(%rsp)
    +0x15fb: movdqa  0x880(%rsp),%xmm0
    +0x1604: movdqa  0x890(%rsp),%xmm1
    +0x160d: pslld   $0xd,%xmm0
    +0x1612: pslld   $0xd,%xmm1
    +0x1617: movdqa  %xmm0,0x880(%rsp)
    +0x1620: movdqa  %xmm1,0x890(%rsp)
    +0x1629: movdqa  0x8a0(%rsp),%xmm0
    +0x1632: movdqa  0x8b0(%rsp),%xmm1
    +0x163b: pslld   $0xd,%xmm0
    +0x1640: pslld   $0xd,%xmm1
    +0x1645: movdqa  %xmm0,0x8a0(%rsp)
    +0x164e: movdqa  %xmm1,0x8b0(%rsp)
    +0x1657: movdqa  0x8c0(%rsp),%xmm0
    +0x1660: movdqa  0x8d0(%rsp),%xmm1
    +0x1669: pslld   $0xd,%xmm0
    +0x166e: pslld   $0xd,%xmm1
    +0x1673: movdqa  %xmm0,0x8c0(%rsp)
    +0x167c: movdqa  %xmm1,0x8d0(%rsp)
    +0x1685: movdqa  0x8e0(%rsp),%xmm0
    +0x168e: movdqa  0x8f0(%rsp),%xmm1
    +0x1697: pslld   $0xd,%xmm0
    +0x169c: pslld   $0xd,%xmm1
    +0x16a1: movdqa  %xmm0,0x8e0(%rsp)
    +0x16aa: movdqa  %xmm1,0x8f0(%rsp)
    +0x16b3: movdqa  0x900(%rsp),%xmm0
    +0x16bc: movdqa  0x910(%rsp),%xmm1
    +0x16c5: pslld   $0xd,%xmm0
    +0x16ca: pslld   $0xd,%xmm1
    +0x16cf: movdqa  %xmm0,0x900(%rsp)
    +0x16d8: movdqa  %xmm1,0x910(%rsp)
    +0x16e1: lea     0x520(%rsp),%rdi
    +0x16e9: call    <mldsa_poly_ntt>
    +0x16ee: mov     $0x1,%eax
    +0x16f3: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1700: movslq  0x51c(%rsp,%rax,4),%rcx
    +0x1708: movslq  0xd1c(%rsp,%rax,4),%rdx
    +0x1710: imul    %rcx,%rdx
    +0x1714: mov     %rdx,%rcx
    +0x1717: imul    %r12,%rcx
    +0x171b: sar     $0x20,%rcx
    +0x171f: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x1726: add     %rdx,%rcx
    +0x1729: shr     $0x20,%rcx
    +0x172d: mov     %ecx,0x51c(%rsp,%rax,4)
    +0x1734: movslq  0x520(%rsp,%rax,4),%rcx
    +0x173c: movslq  0xd20(%rsp,%rax,4),%rdx
    +0x1744: imul    %rcx,%rdx
    +0x1748: mov     %rdx,%rcx
    +0x174b: imul    %r12,%rcx
    +0x174f: sar     $0x20,%rcx
    +0x1753: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x175a: add     %rdx,%rcx
    +0x175d: shr     $0x20,%rcx
    +0x1761: mov     %ecx,0x520(%rsp,%rax,4)
    +0x1768: add     $0x2,%rax
    +0x176c: cmp     $0x101,%rax
    +0x1772: jne     <mldsa65_verify_internal+0x1700>
    +0x1774: mov     $0xc,%eax
    +0x1779: lea     0x920(%rsp),%rdi
    +0x1781: movdqa  0x11f47(%rip),%xmm5
    +0x1789: movdqa  0x11f4f(%rip),%xmm6
    +0x1791: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x17a0: movdqa  0x8f0(%rsp,%rax,4),%xmm0
    +0x17a9: movdqa  0x900(%rsp,%rax,4),%xmm1
    +0x17b2: movdqa  0x910(%rsp,%rax,4),%xmm2
    +0x17bb: movdqa  0x920(%rsp,%rax,4),%xmm3
    +0x17c4: psubd   0x4f0(%rsp,%rax,4),%xmm0
    +0x17cd: psubd   0x500(%rsp,%rax,4),%xmm1
    +0x17d6: movdqa  %xmm0,0x8f0(%rsp,%rax,4)
    +0x17df: movdqa  %xmm1,0x900(%rsp,%rax,4)
    +0x17e8: psubd   0x510(%rsp,%rax,4),%xmm2
    +0x17f1: psubd   0x520(%rsp,%rax,4),%xmm3
    +0x17fa: movdqa  %xmm2,0x910(%rsp,%rax,4)
    +0x1803: movdqa  %xmm3,0x920(%rsp,%rax,4)
    +0x180c: add     $0x10,%rax
    +0x1810: cmp     $0x10c,%rax
    +0x1816: jne     <mldsa65_verify_internal+0x17a0>
    +0x1818: mov     $0x4,%eax
    +0x181d: nopl    (%rax)
    +0x1820: movdqa  0x910(%rsp,%rax,4),%xmm0
    +0x1829: movdqa  0x920(%rsp,%rax,4),%xmm1
    +0x1832: movdqa  %xmm0,%xmm2
    +0x1836: paddd   %xmm5,%xmm2
    +0x183a: movdqa  %xmm1,%xmm3
    +0x183e: paddd   %xmm5,%xmm3
    +0x1842: psrad   $0x17,%xmm2
    +0x1847: psrad   $0x17,%xmm3
    +0x184c: pshufd  $0xf5,%xmm2,%xmm4
    +0x1851: pmuludq %xmm6,%xmm2
    +0x1855: pshufd  $0xe8,%xmm2,%xmm2
    +0x185a: pmuludq %xmm6,%xmm4
    +0x185e: pshufd  $0xe8,%xmm4,%xmm4
    +0x1863: punpckldq %xmm4,%xmm2
    +0x1867: pshufd  $0xf5,%xmm3,%xmm4
    +0x186c: pmuludq %xmm6,%xmm3
    +0x1870: pshufd  $0xe8,%xmm3,%xmm3
    +0x1875: pmuludq %xmm6,%xmm4
    +0x1879: pshufd  $0xe8,%xmm4,%xmm4
    +0x187e: punpckldq %xmm4,%xmm3
    +0x1882: paddd   %xmm0,%xmm2
    +0x1886: paddd   %xmm1,%xmm3
    +0x188a: movdqa  %xmm2,0x910(%rsp,%rax,4)
    +0x1893: movdqa  %xmm3,0x920(%rsp,%rax,4)
    +0x189c: add     $0x8,%rax
    +0x18a0: cmp     $0x104,%rax
    +0x18a6: jne     <mldsa65_verify_internal+0x1820>
    +0x18ac: call    <mldsa_poly_invntt_tomont>
    +0x18b1: xor     %eax,%eax
    +0x18b3: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x18c0: movslq  0x920(%rsp,%rax,4),%rcx
    +0x18c8: lea     0x7fe001(%rcx),%edx
    +0x18ce: mov     %rcx,%rsi
    +0x18d1: shr     $0x1f,%rsi
    +0x18d5: xor     %ecx,%edx
    +0x18d7: and     %esi,%edx
    +0x18d9: xor     %ecx,%edx
    +0x18db: mov     %edx,0x920(%rsp,%rax,4)
    +0x18e2: inc     %rax
    +0x18e5: cmp     $0x100,%rax
    +0x18eb: jne     <mldsa65_verify_internal+0x18c0>
    +0x18ed: mov     %rbx,%r14
    +0x18f0: test    %r13,%r13
    +0x18f3: mov     0x28(%rsp),%rax
    +0x18f8: je      <mldsa65_verify_internal+0x1920>
    +0x18fa: movzbl  0xce6(%rax,%r13,1),%ebx
    +0x1903: mov     %r13,%r12
    +0x1906: movzbl  0xce7(%rax,%r13,1),%r13d
    +0x190f: cmp     $0x37,%r13d
    +0x1913: jbe     <mldsa65_verify_internal+0x1938>
    +0x1915: jmp     <mldsa65_verify_internal+0x2ac>
    +0x191a: nopw    0x0(%rax,%rax,1)
    +0x1920: xor     %ebx,%ebx
    +0x1922: mov     %r13,%r12
    +0x1925: movzbl  0xce7(%rax,%r13,1),%r13d
    +0x192e: cmp     $0x37,%r13d
    +0x1932: ja      <mldsa65_verify_internal+0x2ac>
    +0x1938: cmp     %r13d,%ebx
    +0x193b: ja      <mldsa65_verify_internal+0x2ac>
    +0x1941: mov     $0x400,%edx
    +0x1946: lea     0x520(%rsp),%rdi
    +0x194e: xor     %esi,%esi
    +0x1950: call    <memset>
    +0x1955: mov     0x28(%rsp),%r8
    +0x195a: cmp     %r13d,%ebx
    +0x195d: movdqa  0x1206b(%rip),%xmm5
    +0x1965: jae     <mldsa65_verify_internal+0x1988>
    +0x1967: mov     %ebx,%eax
    +0x1969: movzbl  0xcb0(%r8,%rax,1),%ecx
    +0x1972: movl    $0x1,0x520(%rsp,%rcx,4)
    +0x197d: inc     %ebx
    +0x197f: cmp     %r13d,%ebx
    +0x1982: jne     <mldsa65_verify_internal+0x1b00>
    +0x1988: cmp     $0x5,%r12
    +0x198c: mov     %r14,%rbx
    +0x198f: jne     <mldsa65_verify_internal+0x19b8>
    +0x1991: cmp     $0x37,%r13b
    +0x1995: jae     <mldsa65_verify_internal+0x19b8>
    +0x1997: mov     %r13d,%eax
    +0x199a: nopw    0x0(%rax,%rax,1)
    +0x19a0: cmpb    $0x0,0xcb0(%r8,%rax,1)
    +0x19a9: jne     <mldsa65_verify_internal+0x2ac>
    +0x19af: inc     %rax
    +0x19b2: cmp     $0x37,%rax
    +0x19b6: jne     <mldsa65_verify_internal+0x19a0>
    +0x19b8: xor     %eax,%eax
    +0x19ba: lea     0x1420(%rsp),%r14
    +0x19c2: mov     %r12,%r13
    +0x19c5: movabs  $0x380200100000000,%r12
    +0x19cf: jmp     <mldsa65_verify_internal+0x19f9>
    +0x19d1: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x19e0: inc     %ecx
    +0x19e2: and     $0xf,%ecx
    +0x19e5: mov     %ecx,%esi
    +0x19e7: mov     %esi,0x920(%rsp,%rax,4)
    +0x19ee: inc     %rax
    +0x19f1: cmp     $0x100,%rax
    +0x19f7: je      <mldsa65_verify_internal+0x1a50>
    +0x19f9: mov     0x920(%rsp,%rax,4),%edi
    +0x1a00: lea     0x7f(%rdi),%ecx
    +0x1a03: sar     $0x7,%ecx
    +0x1a06: mov     %ecx,%edx
    +0x1a08: shl     $0xa,%ecx
    +0x1a0b: add     %edx,%ecx
    +0x1a0d: add     $0x200000,%ecx
    +0x1a13: shr     $0x16,%ecx
    +0x1a16: mov     %ecx,%esi
    +0x1a18: and     $0xf,%esi
    +0x1a1b: imul    $0xfff80200,%esi,%edx
    +0x1a21: add     %edi,%edx
    +0x1a23: mov     $0x3ff000,%edi
    +0x1a28: sub     %edx,%edi
    +0x1a2a: movslq  %edi,%rdi
    +0x1a2d: mov     0x520(%rsp,%rax,4),%r8d
    +0x1a35: shr     $0x1f,%rdi
    +0x1a39: test    %r8d,%r8d
    +0x1a3c: je      <mldsa65_verify_internal+0x19e7>
    +0x1a3e: lea     -0x7fe001(%rdx),%esi
    +0x1a44: xor     %edx,%esi
    +0x1a46: and     %edi,%esi
    +0x1a48: xor     %edx,%esi
    +0x1a4a: jg      <mldsa65_verify_internal+0x19e0>
    +0x1a4c: dec     %ecx
    +0x1a4e: jmp     <mldsa65_verify_internal+0x19e2>
    +0x1a50: xor     %eax,%eax
    +0x1a52: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1a60: movaps  0x920(%rsp,%rax,8),%xmm0
    +0x1a68: movaps  0x930(%rsp,%rax,8),%xmm1
    +0x1a70: movaps  0x940(%rsp,%rax,8),%xmm2
    +0x1a78: movaps  0x950(%rsp,%rax,8),%xmm3
    +0x1a80: movaps  %xmm0,%xmm4
    +0x1a83: shufps  $0x88,%xmm1,%xmm4
    +0x1a87: shufps  $0xdd,%xmm1,%xmm0
    +0x1a8b: movaps  %xmm2,%xmm1
    +0x1a8e: shufps  $0x88,%xmm3,%xmm1
    +0x1a92: shufps  $0xdd,%xmm3,%xmm2
    +0x1a96: pslld   $0x4,%xmm0
    +0x1a9b: por     %xmm4,%xmm0
    +0x1a9f: pslld   $0x4,%xmm2
    +0x1aa4: por     %xmm1,%xmm2
    +0x1aa8: pand    %xmm5,%xmm0
    +0x1aac: packuswb %xmm0,%xmm0
    +0x1ab0: packuswb %xmm0,%xmm0
    +0x1ab4: pand    %xmm5,%xmm2
    +0x1ab8: packuswb %xmm2,%xmm2
    +0x1abc: packuswb %xmm2,%xmm2
    +0x1ac0: movd    %xmm0,-0x4(%r15,%rax,1)
    +0x1ac7: movd    %xmm2,(%r15,%rax,1)
    +0x1acd: add     $0x8,%rax
    +0x1ad1: cmp     $0x80,%rax
    +0x1ad7: jne     <mldsa65_verify_internal+0x1a60>
    +0x1ad9: inc     %r13
    +0x1adc: add     $0x140,%rbx
    +0x1ae3: sub     $0xffffffffffffff80,%r15
    +0x1ae7: cmp     $0x6,%r13
    +0x1aeb: lea     0x920(%rsp),%rdi
    +0x1af3: lea     0x40(%rsp),%rsi
    +0x1af8: jne     <mldsa65_verify_internal+0x1099>
    +0x1afe: jmp     <mldsa65_verify_internal+0x1b48>
    +0x1b00: lea     -0x1(%r13),%rcx
    +0x1b04: mov     %rax,%rdx
    +0x1b07: jmp     <mldsa65_verify_internal+0x1b27>
    +0x1b09: nopl    0x0(%rax)
    +0x1b10: movl    $0x1,0x520(%rsp,%rdi,4)
    +0x1b1b: mov     %rsi,%rdx
    +0x1b1e: cmp     %rsi,%rcx
    +0x1b21: je      <mldsa65_verify_internal+0x1988>
    +0x1b27: lea     0x1(%rdx),%rsi
    +0x1b2b: movzbl  0xcb1(%r8,%rdx,1),%edi
    +0x1b34: cmp     %rax,%rsi
    +0x1b37: jbe     <mldsa65_verify_internal+0x1b10>
    +0x1b39: cmp     0xcb0(%r8,%rdx,1),%dil
    +0x1b41: ja      <mldsa65_verify_internal+0x1b10>
    +0x1b43: jmp     <mldsa65_verify_internal+0x2ac>
    +0x1b48: pxor    %xmm0,%xmm0
    +0x1b4c: movdqu  %xmm0,(%rsp)
    +0x1b51: lea     0x4a0(%rsp),%rdi
    +0x1b59: lea     0x4e0(%rsp),%rdx
    +0x1b61: lea     0x1120(%rsp),%r8
    +0x1b69: mov     $0x30,%esi
    +0x1b6e: mov     $0x40,%ecx
    +0x1b73: mov     $0x300,%r9d
    +0x1b79: call    <mld_H65>
    +0x1b7e: movaps  0x4b0(%rsp),%xmm0
    +0x1b86: xorps   0x470(%rsp),%xmm0
    +0x1b8e: movdqa  0x4a0(%rsp),%xmm1
    +0x1b97: pxor    0x460(%rsp),%xmm1
    +0x1ba0: mov     0x4c0(%rsp),%rax
    +0x1ba8: xor     0x480(%rsp),%rax
    +0x1bb0: movq    %rax,%xmm2
    +0x1bb5: mov     0x4c8(%rsp),%rax
    +0x1bbd: xor     0x488(%rsp),%rax
    +0x1bc5: movq    %rax,%xmm3
    +0x1bca: movdqa  %xmm1,%xmm4
    +0x1bce: pxor    %xmm2,%xmm4
    +0x1bd2: movdqa  %xmm1,%xmm5
    +0x1bd6: movsd   %xmm4,%xmm5
    +0x1bda: pxor    %xmm3,%xmm4
    +0x1bde: movss   %xmm4,%xmm5
    +0x1be2: xorps   %xmm0,%xmm5
    +0x1be5: pshufd  $0xee,%xmm5,%xmm4
    +0x1bea: pxor    %xmm5,%xmm4
    +0x1bee: pshufd  $0x55,%xmm4,%xmm5
    +0x1bf3: pxor    %xmm4,%xmm5
    +0x1bf7: movdqa  %xmm5,%xmm4
    +0x1bfb: psrld   $0x10,%xmm4
    +0x1c00: pxor    %xmm5,%xmm4
    +0x1c04: movdqa  %xmm4,%xmm5
    +0x1c08: psrlw   $0x8,%xmm5
    +0x1c0d: pxor    %xmm4,%xmm5
    +0x1c11: movd    %xmm5,%ecx
    +0x1c15: mov     0x4cc(%rsp),%eax
    +0x1c1c: xor     0x48c(%rsp),%eax
    +0x1c23: movd    %eax,%xmm4
    +0x1c27: movdqa  %xmm4,0x30(%rsp)
    +0x1c2d: xor     0x30(%rsp),%cl
    +0x1c31: movzbl  0x31(%rsp),%eax
    +0x1c36: xor     0x32(%rsp),%al
    +0x1c3a: xor     %cl,%al
    +0x1c3c: por     %xmm1,%xmm2
    +0x1c40: movsd   %xmm2,%xmm1
    +0x1c44: por     %xmm4,%xmm3
    +0x1c48: por     %xmm2,%xmm3
    +0x1c4c: movss   %xmm3,%xmm1
    +0x1c50: orps    %xmm0,%xmm1
    +0x1c53: pshufd  $0xee,%xmm1,%xmm0
    +0x1c58: por     %xmm1,%xmm0
    +0x1c5c: pshufd  $0x55,%xmm0,%xmm1
    +0x1c61: por     %xmm0,%xmm1
    +0x1c65: movdqa  %xmm1,%xmm0
    +0x1c69: psrld   $0x10,%xmm0
    +0x1c6e: por     %xmm1,%xmm0
    +0x1c72: movdqa  %xmm0,%xmm1
    +0x1c76: psrlw   $0x8,%xmm1
    +0x1c7b: por     %xmm0,%xmm1
    +0x1c7f: xor     0x33(%rsp),%al
    +0x1c83: movd    %xmm1,%ecx
    +0x1c87: movzbl  %cl,%ecx
    +0x1c8a: neg     %rcx
    +0x1c8d: shr     $0x20,%rcx
    +0x1c91: xor     %al,%cl
    +0x1c93: xor     %edx,%edx
    +0x1c95: cmp     %al,%cl
    +0x1c97: mov     $0xfffffffa,%r14d
    +0x1c9d: cmove   %edx,%r14d
    +0x1ca1: jmp     <mldsa65_verify_internal+0x2b2>
 ***)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa65_verify_internal";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* signature sigb at sig (3309 bytes), the message M of mlen bytes at m and  *)
(* the prefix PRE of prelen bytes at pre (or, if ext is nonzero as a 32-bit  *)
(* integer, mu in the first 64 bytes at m), and the public key pkb at pk     *)
(* (1952 bytes): the result is 0 if the signature is accepted, and -6        *)
(* otherwise. ext, the seventh argument, is on the stack above the return    *)
(* address, and the code reads its low 32 bits. The function aligns the      *)
(* stack pointer down to a multiple of 32, which may lower it by up to 31    *)
(* bytes, saves RBP, the frame pointer, and five more registers, and         *)
(* reserves its buffers, below which the callees use theirs: 12037 bytes of  *)
(* stack below the return address in all (the figure of stackx.py, which     *)
(* counts the red zone that mldsa_keccakf1600_permute writes below RSP). The *)
(* GOT entries of memset and memcpy, which the PLT stubs read, and the       *)
(* region (ea,el) that they may read are apart from the stack.               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 6 5 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 49 48
           (num_of_bytelist(list_of_seq sigb 48)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 12037),12037))
              [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa65_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes32(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 3309
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mld_verify_internal_ok 6 5 48
                           mld_polyz_unpack_19 640 524092
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49
                           sigb pkb
                           (if ext = (word 0:int32)
                            then mld_verify_mu 1952 pkb prelen PRE mlen M
                            else M MOD 2 EXP 512)
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 12037),12037)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the flag ext, the    *)
(* signature, the message, the prefix and the public key, all public, the    *)
(* addresses of memset and memcpy and the stack, with all accesses within    *)
(* the arguments, the stack, the return address and ext above it, the GOT    *)
(* entries of memset and memcpy, the region (ea,el) that they may read and   *)
(* the constants of the callees, and the writes within the stack.            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 6 5 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 49 48
           (num_of_bytelist(list_of_seq sigb 48)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 12037),12037))
              [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa65_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes32(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 3309
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mld_verify_internal_ok 6 5 48
                           mld_polyz_unpack_19 640 524092
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49
                           sigb pkb
                           (if ext = (word 0:int32)
                            then mld_verify_mu 1952 pkb prelen PRE mlen M
                            else M MOD 2 EXP 512)
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE
                              mf mc pc (word_sub stackpointer (word 12037))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; pk,1952;
                         word_sub stackpointer (word 12037),12037;
                         stackpointer,8; word_add stackpointer (word 8),4;
                         word(pc + got_memset),8;
                          word(pc + got_memcpy),8; ea,el;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa65_poly_challenge_consts),48;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc +
                            mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy_consts),
                          32;
                          word(pc + mldsa65_verify_internal_consts),784]
                        [word_sub stackpointer (word 12037),12037]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 12037),12037)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 6 5 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 49 48
           (num_of_bytelist(list_of_seq sigb 48)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 12037),12037))
              [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa65_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes32(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 3309
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE
                              mf mc pc (word_sub stackpointer (word 12037))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; pk,1952;
                         word_sub stackpointer (word 12037),12037;
                         stackpointer,8; word_add stackpointer (word 8),4;
                         word(pc + got_memset),8;
                          word(pc + got_memcpy),8; ea,el;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa65_poly_challenge_consts),48;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc +
                            mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy_consts),
                          32;
                          word(pc + mldsa65_verify_internal_consts),784]
                        [word_sub stackpointer (word 12037),12037]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 12037),12037)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
