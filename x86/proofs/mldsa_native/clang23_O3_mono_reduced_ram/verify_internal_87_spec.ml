(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the statement. This is the code for          *)
(* mldsa87_verify_internal (mld_sign_verify_internal in sign.c) from mldsa-  *)
(* native's portable C implementation compiled by clang 23 with -O3 and      *)
(* MLD_CONFIG_REDUCE_RAM as one translation unit (see                        *)
(* mldsa_native/README.md). It aligns its stack frame to 32 bytes, unpacks z *)
(* and checks its norm, computes mu (or takes it from m if ext is nonzero),  *)
(* transforms z, computes the challenge from c~ with mldsa87_poly_challenge, *)
(* and for each row computes w1' = UseHint(h, A z - c t1 2^d), and compares  *)
(* c~ with mld_H87 of mu and w1'. Clang has inlined most of its callees; it  *)
(* still calls mldsa87_polyvecl_chknorm, mld_H87, mldsa_poly_ntt,            *)
(* mldsa_poly_invntt_tomont,                                                 *)
(* mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy and                  *)
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
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvecl_chknorm_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_challenge_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/H_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa87_verify_internal:
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
      +0x3e: sub     $0x240,%rsp
      +0x45: mov     %r9,%rbx
      +0x48: mov     %r8,%r14
      +0x4b: mov     %rcx,%r13
      +0x4e: mov     %rdx,0x18(%rsp)
      +0x53: mov     %rsi,%r12
      +0x56: mov     0x10(%rbp),%r15d
      +0x5a: movdqu  (%rdi),%xmm0
      +0x5e: movups  0x10(%rdi),%xmm1
      +0x62: movdqu  0x20(%rdi),%xmm2
      +0x67: movups  0x30(%rdi),%xmm3
      +0x6b: movdqa  %xmm0,0x540(%rsp)
      +0x74: movaps  %xmm1,0x550(%rsp)
      +0x7c: movdqa  %xmm2,0x560(%rsp)
      +0x85: movaps  %xmm3,0x570(%rsp)
      +0x8d: lea     0x44(%rdi),%rax
      +0x91: xor     %ecx,%ecx
      +0x93: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
      +0xa0: movzwl  -0x4(%rax),%edx
      +0xa4: movzbl  -0x2(%rax),%esi
      +0xa8: mov     %esi,%r8d
      +0xab: and     $0xf,%r8d
      +0xaf: shl     $0x10,%r8d
      +0xb3: or      %edx,%r8d
      +0xb6: shr     $0x4,%esi
      +0xb9: movzbl  -0x1(%rax),%edx
      +0xbd: shl     $0x4,%edx
      +0xc0: or      %esi,%edx
      +0xc2: movzbl  (%rax),%esi
      +0xc5: shl     $0xc,%esi
      +0xc8: or      %edx,%esi
      +0xca: mov     $0x80000,%edx
      +0xcf: sub     %r8d,%edx
      +0xd2: mov     %edx,0x1600(%rsp,%rcx,8)
      +0xd9: mov     $0x80000,%edx
      +0xde: sub     %esi,%edx
      +0xe0: mov     %edx,0x1604(%rsp,%rcx,8)
      +0xe7: inc     %rcx
      +0xea: add     $0x5,%rax
      +0xee: cmp     $0x80,%rcx
      +0xf5: jne     <mldsa87_verify_internal+0xa0>
      +0xf7: lea     0x2c4(%rdi),%rax
      +0xfe: mov     $0x80,%ecx
     +0x103: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x110: movzwl  -0x4(%rax),%edx
     +0x114: movzbl  -0x2(%rax),%esi
     +0x118: mov     %esi,%r8d
     +0x11b: and     $0xf,%r8d
     +0x11f: shl     $0x10,%r8d
     +0x123: or      %edx,%r8d
     +0x126: shr     $0x4,%esi
     +0x129: movzbl  -0x1(%rax),%edx
     +0x12d: shl     $0x4,%edx
     +0x130: or      %esi,%edx
     +0x132: movzbl  (%rax),%esi
     +0x135: shl     $0xc,%esi
     +0x138: or      %edx,%esi
     +0x13a: mov     $0x80000,%edx
     +0x13f: sub     %r8d,%edx
     +0x142: mov     %edx,0x1600(%rsp,%rcx,8)
     +0x149: mov     $0x80000,%edx
     +0x14e: sub     %esi,%edx
     +0x150: mov     %edx,0x1604(%rsp,%rcx,8)
     +0x157: inc     %rcx
     +0x15a: add     $0x5,%rax
     +0x15e: cmp     $0x100,%rcx
     +0x165: jne     <mldsa87_verify_internal+0x110>
     +0x167: lea     0x544(%rdi),%rax
     +0x16e: mov     $0x100,%ecx
     +0x173: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x180: movzwl  -0x4(%rax),%edx
     +0x184: movzbl  -0x2(%rax),%esi
     +0x188: mov     %esi,%r8d
     +0x18b: and     $0xf,%r8d
     +0x18f: shl     $0x10,%r8d
     +0x193: or      %edx,%r8d
     +0x196: shr     $0x4,%esi
     +0x199: movzbl  -0x1(%rax),%edx
     +0x19d: shl     $0x4,%edx
     +0x1a0: or      %esi,%edx
     +0x1a2: movzbl  (%rax),%esi
     +0x1a5: shl     $0xc,%esi
     +0x1a8: or      %edx,%esi
     +0x1aa: mov     $0x80000,%edx
     +0x1af: sub     %r8d,%edx
     +0x1b2: mov     %edx,0x1600(%rsp,%rcx,8)
     +0x1b9: mov     $0x80000,%edx
     +0x1be: sub     %esi,%edx
     +0x1c0: mov     %edx,0x1604(%rsp,%rcx,8)
     +0x1c7: inc     %rcx
     +0x1ca: add     $0x5,%rax
     +0x1ce: cmp     $0x180,%rcx
     +0x1d5: jne     <mldsa87_verify_internal+0x180>
     +0x1d7: lea     0x7c4(%rdi),%rax
     +0x1de: mov     $0x180,%ecx
     +0x1e3: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x1f0: movzwl  -0x4(%rax),%edx
     +0x1f4: movzbl  -0x2(%rax),%esi
     +0x1f8: mov     %esi,%r8d
     +0x1fb: and     $0xf,%r8d
     +0x1ff: shl     $0x10,%r8d
     +0x203: or      %edx,%r8d
     +0x206: shr     $0x4,%esi
     +0x209: movzbl  -0x1(%rax),%edx
     +0x20d: shl     $0x4,%edx
     +0x210: or      %esi,%edx
     +0x212: movzbl  (%rax),%esi
     +0x215: shl     $0xc,%esi
     +0x218: or      %edx,%esi
     +0x21a: mov     $0x80000,%edx
     +0x21f: sub     %r8d,%edx
     +0x222: mov     %edx,0x1600(%rsp,%rcx,8)
     +0x229: mov     $0x80000,%edx
     +0x22e: sub     %esi,%edx
     +0x230: mov     %edx,0x1604(%rsp,%rcx,8)
     +0x237: inc     %rcx
     +0x23a: add     $0x5,%rax
     +0x23e: cmp     $0x200,%rcx
     +0x245: jne     <mldsa87_verify_internal+0x1f0>
     +0x247: lea     0xa44(%rdi),%rax
     +0x24e: mov     $0x200,%ecx
     +0x253: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x260: movzwl  -0x4(%rax),%edx
     +0x264: movzbl  -0x2(%rax),%esi
     +0x268: mov     %esi,%r8d
     +0x26b: and     $0xf,%r8d
     +0x26f: shl     $0x10,%r8d
     +0x273: or      %edx,%r8d
     +0x276: shr     $0x4,%esi
     +0x279: movzbl  -0x1(%rax),%edx
     +0x27d: shl     $0x4,%edx
     +0x280: or      %esi,%edx
     +0x282: movzbl  (%rax),%esi
     +0x285: shl     $0xc,%esi
     +0x288: or      %edx,%esi
     +0x28a: mov     $0x80000,%edx
     +0x28f: sub     %r8d,%edx
     +0x292: mov     %edx,0x1600(%rsp,%rcx,8)
     +0x299: mov     $0x80000,%edx
     +0x29e: sub     %esi,%edx
     +0x2a0: mov     %edx,0x1604(%rsp,%rcx,8)
     +0x2a7: inc     %rcx
     +0x2aa: add     $0x5,%rax
     +0x2ae: cmp     $0x280,%rcx
     +0x2b5: jne     <mldsa87_verify_internal+0x260>
     +0x2b7: lea     0xcc4(%rdi),%rax
     +0x2be: mov     $0x280,%ecx
     +0x2c3: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x2d0: movzwl  -0x4(%rax),%edx
     +0x2d4: movzbl  -0x2(%rax),%esi
     +0x2d8: mov     %esi,%r8d
     +0x2db: and     $0xf,%r8d
     +0x2df: shl     $0x10,%r8d
     +0x2e3: or      %edx,%r8d
     +0x2e6: shr     $0x4,%esi
     +0x2e9: movzbl  -0x1(%rax),%edx
     +0x2ed: shl     $0x4,%edx
     +0x2f0: or      %esi,%edx
     +0x2f2: movzbl  (%rax),%esi
     +0x2f5: shl     $0xc,%esi
     +0x2f8: or      %edx,%esi
     +0x2fa: mov     $0x80000,%edx
     +0x2ff: sub     %r8d,%edx
     +0x302: mov     %edx,0x1600(%rsp,%rcx,8)
     +0x309: mov     $0x80000,%edx
     +0x30e: sub     %esi,%edx
     +0x310: mov     %edx,0x1604(%rsp,%rcx,8)
     +0x317: inc     %rcx
     +0x31a: add     $0x5,%rax
     +0x31e: cmp     $0x300,%rcx
     +0x325: jne     <mldsa87_verify_internal+0x2d0>
     +0x327: mov     %rdi,0xf8(%rsp)
     +0x32f: lea     0xf44(%rdi),%rax
     +0x336: mov     $0x300,%ecx
     +0x33b: nopl    0x0(%rax,%rax,1)
     +0x340: movzwl  -0x4(%rax),%edx
     +0x344: movzbl  -0x2(%rax),%esi
     +0x348: mov     %esi,%edi
     +0x34a: and     $0xf,%edi
     +0x34d: shl     $0x10,%edi
     +0x350: or      %edx,%edi
     +0x352: shr     $0x4,%esi
     +0x355: movzbl  -0x1(%rax),%edx
     +0x359: shl     $0x4,%edx
     +0x35c: or      %esi,%edx
     +0x35e: movzbl  (%rax),%esi
     +0x361: shl     $0xc,%esi
     +0x364: or      %edx,%esi
     +0x366: mov     $0x80000,%edx
     +0x36b: sub     %edi,%edx
     +0x36d: mov     %edx,0x1600(%rsp,%rcx,8)
     +0x374: mov     $0x80000,%edx
     +0x379: sub     %esi,%edx
     +0x37b: mov     %edx,0x1604(%rsp,%rcx,8)
     +0x382: inc     %rcx
     +0x385: add     $0x5,%rax
     +0x389: cmp     $0x380,%rcx
     +0x390: jne     <mldsa87_verify_internal+0x340>
     +0x392: lea     0x1600(%rsp),%rdi
     +0x39a: mov     $0x7ff88,%esi
     +0x39f: call    <mldsa87_polyvecl_chknorm>
     +0x3a4: test    %eax,%eax
     +0x3a6: je      <mldsa87_verify_internal+0x4e4>
     +0x3ac: mov     $0xfffffffa,%r14d
     +0x3b2: lea     0x600(%rsp),%rbx
     +0x3ba: mov     $0x400,%edx
     +0x3bf: mov     %rbx,%rdi
     +0x3c2: xor     %esi,%esi
     +0x3c4: call    <memset>
     +0x3c9: lea     0xa00(%rsp),%rbx
     +0x3d1: mov     $0x400,%edx
     +0x3d6: mov     %rbx,%rdi
     +0x3d9: xor     %esi,%esi
     +0x3db: call    <memset>
     +0x3e0: lea     0x100(%rsp),%rbx
     +0x3e8: mov     $0x420,%edx
     +0x3ed: mov     %rbx,%rdi
     +0x3f0: xor     %esi,%esi
     +0x3f2: call    <memset>
     +0x3f7: lea     0x1200(%rsp),%rbx
     +0x3ff: mov     $0x400,%edx
     +0x404: mov     %rbx,%rdi
     +0x407: xor     %esi,%esi
     +0x409: call    <memset>
     +0x40e: lea     0x1600(%rsp),%rbx
     +0x416: mov     $0x1c00,%edx
     +0x41b: mov     %rbx,%rdi
     +0x41e: xor     %esi,%esi
     +0x420: call    <memset>
     +0x425: pxor    %xmm0,%xmm0
     +0x429: movdqa  %xmm0,0x5f0(%rsp)
     +0x432: movdqa  %xmm0,0x5e0(%rsp)
     +0x43b: movdqa  %xmm0,0x5d0(%rsp)
     +0x444: movdqa  %xmm0,0x5c0(%rsp)
     +0x44d: lea     0x5c0(%rsp),%rax
     +0x455: movdqa  %xmm0,0x570(%rsp)
     +0x45e: movdqa  %xmm0,0x560(%rsp)
     +0x467: movdqa  %xmm0,0x550(%rsp)
     +0x470: movdqa  %xmm0,0x540(%rsp)
     +0x479: lea     0x540(%rsp),%rax
     +0x481: movdqa  %xmm0,0x5b0(%rsp)
     +0x48a: movdqa  %xmm0,0x5a0(%rsp)
     +0x493: movdqa  %xmm0,0x590(%rsp)
     +0x49c: movdqa  %xmm0,0x580(%rsp)
     +0x4a5: lea     0x580(%rsp),%rax
     +0x4ad: lea     0xe00(%rsp),%rbx
     +0x4b5: mov     $0x400,%edx
     +0x4ba: mov     %rbx,%rdi
     +0x4bd: xor     %esi,%esi
     +0x4bf: call    <memset>
     +0x4c4: mov     %r14d,%eax
     +0x4c7: lea     -0x28(%rbp),%rsp
     +0x4cb: pop     %rbx
     +0x4cc: pop     %r12
     +0x4ce: pop     %r13
     +0x4d0: pop     %r14
     +0x4d2: pop     %r15
     +0x4d4: pop     %rbp
     +0x4d5: xor     %ecx,%ecx
     +0x4d7: xor     %edi,%edi
     +0x4d9: xor     %edx,%edx
     +0x4db: xor     %esi,%esi
     +0x4dd: xor     %r8d,%r8d
     +0x4e0: xor     %r9d,%r9d
     +0x4e3: ret     
     +0x4e4: test    %r15d,%r15d
     +0x4e7: je      <mldsa87_verify_internal+0x527>
     +0x4e9: movups  (%r12),%xmm0
     +0x4ee: movups  0x10(%r12),%xmm1
     +0x4f4: movdqu  0x20(%r12),%xmm2
     +0x4fb: movups  0x30(%r12),%xmm3
     +0x501: movaps  %xmm3,0x5b0(%rsp)
     +0x509: movdqa  %xmm2,0x5a0(%rsp)
     +0x512: movaps  %xmm1,0x590(%rsp)
     +0x51a: movaps  %xmm0,0x580(%rsp)
     +0x522: jmp     <mldsa87_verify_internal+0x1672>
     +0x527: pxor    %xmm0,%xmm0
     +0x52b: movdqu  %xmm0,0x1bc(%rsp)
     +0x534: movdqa  %xmm0,0x1b0(%rsp)
     +0x53d: movdqa  %xmm0,0x1a0(%rsp)
     +0x546: movdqa  %xmm0,0x190(%rsp)
     +0x54f: movdqa  %xmm0,0x180(%rsp)
     +0x558: movdqa  %xmm0,0x170(%rsp)
     +0x561: movdqa  %xmm0,0x160(%rsp)
     +0x56a: movdqa  %xmm0,0x150(%rsp)
     +0x573: movdqa  %xmm0,0x140(%rsp)
     +0x57c: movdqa  %xmm0,0x130(%rsp)
     +0x585: movdqa  %xmm0,0x120(%rsp)
     +0x58e: movdqa  %xmm0,0x110(%rsp)
     +0x597: movdqa  %xmm0,0x100(%rsp)
     +0x5a0: movups  (%rbx),%xmm0
     +0x5a3: movups  0x10(%rbx),%xmm1
     +0x5a7: movaps  %xmm0,0x100(%rsp)
     +0x5af: movaps  %xmm1,0x110(%rsp)
     +0x5b7: movups  0x20(%rbx),%xmm0
     +0x5bb: movups  0x30(%rbx),%xmm1
     +0x5bf: movaps  %xmm0,0x120(%rsp)
     +0x5c7: movaps  %xmm1,0x130(%rsp)
     +0x5cf: movups  0x40(%rbx),%xmm0
     +0x5d3: movups  0x50(%rbx),%xmm1
     +0x5d7: xorps   0x140(%rsp),%xmm0
     +0x5df: xorps   0x150(%rsp),%xmm1
     +0x5e7: movaps  %xmm0,0x140(%rsp)
     +0x5ef: movaps  %xmm1,0x150(%rsp)
     +0x5f7: movups  0x60(%rbx),%xmm0
     +0x5fb: movups  0x70(%rbx),%xmm1
     +0x5ff: xorps   0x160(%rsp),%xmm0
     +0x607: xorps   0x170(%rsp),%xmm1
     +0x60f: movaps  %xmm0,0x160(%rsp)
     +0x617: movaps  %xmm1,0x170(%rsp)
     +0x61f: mov     0x80(%rbx),%rax
     +0x626: xor     %rax,0x180(%rsp)
     +0x62e: mov     %r13,0x538(%rsp)
     +0x636: lea     0x100(%rsp),%r13
     +0x63e: mov     %r13,%rdi
     +0x641: call    <mldsa_keccakf1600_permute>
     +0x646: movups  0x88(%rbx),%xmm0
     +0x64d: movups  0x98(%rbx),%xmm1
     +0x654: xorps   0x100(%rsp),%xmm0
     +0x65c: xorps   0x110(%rsp),%xmm1
     +0x664: movaps  %xmm0,0x100(%rsp)
     +0x66c: movaps  %xmm1,0x110(%rsp)
     +0x674: movups  0xa8(%rbx),%xmm0
     +0x67b: movups  0xb8(%rbx),%xmm1
     +0x682: xorps   0x120(%rsp),%xmm0
     +0x68a: xorps   0x130(%rsp),%xmm1
     +0x692: movaps  %xmm0,0x120(%rsp)
     +0x69a: movaps  %xmm1,0x130(%rsp)
     +0x6a2: movups  0xc8(%rbx),%xmm0
     +0x6a9: movups  0xd8(%rbx),%xmm1
     +0x6b0: xorps   0x140(%rsp),%xmm0
     +0x6b8: xorps   0x150(%rsp),%xmm1
     +0x6c0: movaps  %xmm0,0x140(%rsp)
     +0x6c8: movaps  %xmm1,0x150(%rsp)
     +0x6d0: movups  0xe8(%rbx),%xmm0
     +0x6d7: movups  0xf8(%rbx),%xmm1
     +0x6de: xorps   0x160(%rsp),%xmm0
     +0x6e6: xorps   0x170(%rsp),%xmm1
     +0x6ee: movaps  %xmm0,0x160(%rsp)
     +0x6f6: movaps  %xmm1,0x170(%rsp)
     +0x6fe: mov     0x108(%rbx),%rax
     +0x705: xor     %rax,0x180(%rsp)
     +0x70d: mov     %r13,%rdi
     +0x710: call    <mldsa_keccakf1600_permute>
     +0x715: movups  0x110(%rbx),%xmm0
     +0x71c: movups  0x120(%rbx),%xmm1
     +0x723: xorps   0x100(%rsp),%xmm0
     +0x72b: xorps   0x110(%rsp),%xmm1
     +0x733: movaps  %xmm0,0x100(%rsp)
     +0x73b: movaps  %xmm1,0x110(%rsp)
     +0x743: movups  0x130(%rbx),%xmm0
     +0x74a: movups  0x140(%rbx),%xmm1
     +0x751: xorps   0x120(%rsp),%xmm0
     +0x759: xorps   0x130(%rsp),%xmm1
     +0x761: movaps  %xmm0,0x120(%rsp)
     +0x769: movaps  %xmm1,0x130(%rsp)
     +0x771: movups  0x150(%rbx),%xmm0
     +0x778: movups  0x160(%rbx),%xmm1
     +0x77f: xorps   0x140(%rsp),%xmm0
     +0x787: xorps   0x150(%rsp),%xmm1
     +0x78f: movaps  %xmm0,0x140(%rsp)
     +0x797: movaps  %xmm1,0x150(%rsp)
     +0x79f: movups  0x170(%rbx),%xmm0
     +0x7a6: movups  0x180(%rbx),%xmm1
     +0x7ad: xorps   0x160(%rsp),%xmm0
     +0x7b5: xorps   0x170(%rsp),%xmm1
     +0x7bd: movaps  %xmm0,0x160(%rsp)
     +0x7c5: movaps  %xmm1,0x170(%rsp)
     +0x7cd: mov     0x190(%rbx),%rax
     +0x7d4: xor     %rax,0x180(%rsp)
     +0x7dc: mov     %r13,%rdi
     +0x7df: call    <mldsa_keccakf1600_permute>
     +0x7e4: movups  0x198(%rbx),%xmm0
     +0x7eb: movups  0x1a8(%rbx),%xmm1
     +0x7f2: xorps   0x100(%rsp),%xmm0
     +0x7fa: xorps   0x110(%rsp),%xmm1
     +0x802: movaps  %xmm0,0x100(%rsp)
     +0x80a: movaps  %xmm1,0x110(%rsp)
     +0x812: movups  0x1b8(%rbx),%xmm0
     +0x819: movups  0x1c8(%rbx),%xmm1
     +0x820: xorps   0x120(%rsp),%xmm0
     +0x828: xorps   0x130(%rsp),%xmm1
     +0x830: movaps  %xmm0,0x120(%rsp)
     +0x838: movaps  %xmm1,0x130(%rsp)
     +0x840: movups  0x1d8(%rbx),%xmm0
     +0x847: movups  0x1e8(%rbx),%xmm1
     +0x84e: xorps   0x140(%rsp),%xmm0
     +0x856: xorps   0x150(%rsp),%xmm1
     +0x85e: movaps  %xmm0,0x140(%rsp)
     +0x866: movaps  %xmm1,0x150(%rsp)
     +0x86e: movups  0x1f8(%rbx),%xmm0
     +0x875: movups  0x208(%rbx),%xmm1
     +0x87c: xorps   0x160(%rsp),%xmm0
     +0x884: xorps   0x170(%rsp),%xmm1
     +0x88c: movaps  %xmm0,0x160(%rsp)
     +0x894: movaps  %xmm1,0x170(%rsp)
     +0x89c: mov     0x218(%rbx),%rax
     +0x8a3: xor     %rax,0x180(%rsp)
     +0x8ab: mov     %r13,%rdi
     +0x8ae: call    <mldsa_keccakf1600_permute>
     +0x8b3: movups  0x220(%rbx),%xmm0
     +0x8ba: movups  0x230(%rbx),%xmm1
     +0x8c1: xorps   0x100(%rsp),%xmm0
     +0x8c9: xorps   0x110(%rsp),%xmm1
     +0x8d1: movaps  %xmm0,0x100(%rsp)
     +0x8d9: movaps  %xmm1,0x110(%rsp)
     +0x8e1: movups  0x240(%rbx),%xmm0
     +0x8e8: movups  0x250(%rbx),%xmm1
     +0x8ef: xorps   0x120(%rsp),%xmm0
     +0x8f7: xorps   0x130(%rsp),%xmm1
     +0x8ff: movaps  %xmm0,0x120(%rsp)
     +0x907: movaps  %xmm1,0x130(%rsp)
     +0x90f: movups  0x260(%rbx),%xmm0
     +0x916: movups  0x270(%rbx),%xmm1
     +0x91d: xorps   0x140(%rsp),%xmm0
     +0x925: xorps   0x150(%rsp),%xmm1
     +0x92d: movaps  %xmm0,0x140(%rsp)
     +0x935: movaps  %xmm1,0x150(%rsp)
     +0x93d: movups  0x280(%rbx),%xmm0
     +0x944: movups  0x290(%rbx),%xmm1
     +0x94b: xorps   0x160(%rsp),%xmm0
     +0x953: xorps   0x170(%rsp),%xmm1
     +0x95b: movaps  %xmm0,0x160(%rsp)
     +0x963: movaps  %xmm1,0x170(%rsp)
     +0x96b: mov     0x2a0(%rbx),%rax
     +0x972: xor     %rax,0x180(%rsp)
     +0x97a: mov     %r13,%rdi
     +0x97d: call    <mldsa_keccakf1600_permute>
     +0x982: movups  0x2a8(%rbx),%xmm0
     +0x989: movups  0x2b8(%rbx),%xmm1
     +0x990: xorps   0x100(%rsp),%xmm0
     +0x998: xorps   0x110(%rsp),%xmm1
     +0x9a0: movaps  %xmm0,0x100(%rsp)
     +0x9a8: movaps  %xmm1,0x110(%rsp)
     +0x9b0: movups  0x2c8(%rbx),%xmm0
     +0x9b7: movups  0x2d8(%rbx),%xmm1
     +0x9be: xorps   0x120(%rsp),%xmm0
     +0x9c6: xorps   0x130(%rsp),%xmm1
     +0x9ce: movaps  %xmm0,0x120(%rsp)
     +0x9d6: movaps  %xmm1,0x130(%rsp)
     +0x9de: movups  0x2e8(%rbx),%xmm0
     +0x9e5: movups  0x2f8(%rbx),%xmm1
     +0x9ec: xorps   0x140(%rsp),%xmm0
     +0x9f4: xorps   0x150(%rsp),%xmm1
     +0x9fc: movaps  %xmm0,0x140(%rsp)
     +0xa04: movaps  %xmm1,0x150(%rsp)
     +0xa0c: movups  0x308(%rbx),%xmm0
     +0xa13: movups  0x318(%rbx),%xmm1
     +0xa1a: xorps   0x160(%rsp),%xmm0
     +0xa22: xorps   0x170(%rsp),%xmm1
     +0xa2a: movaps  %xmm0,0x160(%rsp)
     +0xa32: movaps  %xmm1,0x170(%rsp)
     +0xa3a: mov     0x328(%rbx),%rax
     +0xa41: xor     %rax,0x180(%rsp)
     +0xa49: mov     %r13,%rdi
     +0xa4c: call    <mldsa_keccakf1600_permute>
     +0xa51: movups  0x330(%rbx),%xmm0
     +0xa58: movups  0x340(%rbx),%xmm1
     +0xa5f: xorps   0x100(%rsp),%xmm0
     +0xa67: xorps   0x110(%rsp),%xmm1
     +0xa6f: movaps  %xmm0,0x100(%rsp)
     +0xa77: movaps  %xmm1,0x110(%rsp)
     +0xa7f: movups  0x350(%rbx),%xmm0
     +0xa86: movups  0x360(%rbx),%xmm1
     +0xa8d: xorps   0x120(%rsp),%xmm0
     +0xa95: xorps   0x130(%rsp),%xmm1
     +0xa9d: movaps  %xmm0,0x120(%rsp)
     +0xaa5: movaps  %xmm1,0x130(%rsp)
     +0xaad: movups  0x370(%rbx),%xmm0
     +0xab4: movups  0x380(%rbx),%xmm1
     +0xabb: xorps   0x140(%rsp),%xmm0
     +0xac3: xorps   0x150(%rsp),%xmm1
     +0xacb: movaps  %xmm0,0x140(%rsp)
     +0xad3: movaps  %xmm1,0x150(%rsp)
     +0xadb: movups  0x390(%rbx),%xmm0
     +0xae2: movups  0x3a0(%rbx),%xmm1
     +0xae9: xorps   0x160(%rsp),%xmm0
     +0xaf1: xorps   0x170(%rsp),%xmm1
     +0xaf9: movaps  %xmm0,0x160(%rsp)
     +0xb01: movaps  %xmm1,0x170(%rsp)
     +0xb09: mov     0x3b0(%rbx),%rax
     +0xb10: xor     %rax,0x180(%rsp)
     +0xb18: mov     %r13,%rdi
     +0xb1b: call    <mldsa_keccakf1600_permute>
     +0xb20: movups  0x3b8(%rbx),%xmm0
     +0xb27: movups  0x3c8(%rbx),%xmm1
     +0xb2e: xorps   0x100(%rsp),%xmm0
     +0xb36: xorps   0x110(%rsp),%xmm1
     +0xb3e: movaps  %xmm0,0x100(%rsp)
     +0xb46: movaps  %xmm1,0x110(%rsp)
     +0xb4e: movups  0x3d8(%rbx),%xmm0
     +0xb55: movups  0x3e8(%rbx),%xmm1
     +0xb5c: xorps   0x120(%rsp),%xmm0
     +0xb64: xorps   0x130(%rsp),%xmm1
     +0xb6c: movaps  %xmm0,0x120(%rsp)
     +0xb74: movaps  %xmm1,0x130(%rsp)
     +0xb7c: movups  0x3f8(%rbx),%xmm0
     +0xb83: movups  0x408(%rbx),%xmm1
     +0xb8a: xorps   0x140(%rsp),%xmm0
     +0xb92: xorps   0x150(%rsp),%xmm1
     +0xb9a: movaps  %xmm0,0x140(%rsp)
     +0xba2: movaps  %xmm1,0x150(%rsp)
     +0xbaa: movups  0x418(%rbx),%xmm0
     +0xbb1: movups  0x428(%rbx),%xmm1
     +0xbb8: xorps   0x160(%rsp),%xmm0
     +0xbc0: xorps   0x170(%rsp),%xmm1
     +0xbc8: movaps  %xmm0,0x160(%rsp)
     +0xbd0: movaps  %xmm1,0x170(%rsp)
     +0xbd8: mov     0x438(%rbx),%rax
     +0xbdf: xor     %rax,0x180(%rsp)
     +0xbe7: mov     %r13,%rdi
     +0xbea: call    <mldsa_keccakf1600_permute>
     +0xbef: movups  0x440(%rbx),%xmm0
     +0xbf6: movups  0x450(%rbx),%xmm1
     +0xbfd: xorps   0x100(%rsp),%xmm0
     +0xc05: xorps   0x110(%rsp),%xmm1
     +0xc0d: movaps  %xmm0,0x100(%rsp)
     +0xc15: movaps  %xmm1,0x110(%rsp)
     +0xc1d: movups  0x460(%rbx),%xmm0
     +0xc24: movups  0x470(%rbx),%xmm1
     +0xc2b: xorps   0x120(%rsp),%xmm0
     +0xc33: xorps   0x130(%rsp),%xmm1
     +0xc3b: movaps  %xmm0,0x120(%rsp)
     +0xc43: movaps  %xmm1,0x130(%rsp)
     +0xc4b: movups  0x480(%rbx),%xmm0
     +0xc52: movups  0x490(%rbx),%xmm1
     +0xc59: xorps   0x140(%rsp),%xmm0
     +0xc61: xorps   0x150(%rsp),%xmm1
     +0xc69: movaps  %xmm0,0x140(%rsp)
     +0xc71: movaps  %xmm1,0x150(%rsp)
     +0xc79: movups  0x4a0(%rbx),%xmm0
     +0xc80: movups  0x4b0(%rbx),%xmm1
     +0xc87: xorps   0x160(%rsp),%xmm0
     +0xc8f: xorps   0x170(%rsp),%xmm1
     +0xc97: movaps  %xmm0,0x160(%rsp)
     +0xc9f: movaps  %xmm1,0x170(%rsp)
     +0xca7: mov     0x4c0(%rbx),%rax
     +0xcae: xor     %rax,0x180(%rsp)
     +0xcb6: mov     %r13,%rdi
     +0xcb9: call    <mldsa_keccakf1600_permute>
     +0xcbe: movups  0x4c8(%rbx),%xmm0
     +0xcc5: movups  0x4d8(%rbx),%xmm1
     +0xccc: xorps   0x100(%rsp),%xmm0
     +0xcd4: xorps   0x110(%rsp),%xmm1
     +0xcdc: movaps  %xmm0,0x100(%rsp)
     +0xce4: movaps  %xmm1,0x110(%rsp)
     +0xcec: movups  0x4e8(%rbx),%xmm0
     +0xcf3: movups  0x4f8(%rbx),%xmm1
     +0xcfa: xorps   0x120(%rsp),%xmm0
     +0xd02: xorps   0x130(%rsp),%xmm1
     +0xd0a: movaps  %xmm0,0x120(%rsp)
     +0xd12: movaps  %xmm1,0x130(%rsp)
     +0xd1a: movups  0x508(%rbx),%xmm0
     +0xd21: movups  0x518(%rbx),%xmm1
     +0xd28: xorps   0x140(%rsp),%xmm0
     +0xd30: xorps   0x150(%rsp),%xmm1
     +0xd38: movaps  %xmm0,0x140(%rsp)
     +0xd40: movaps  %xmm1,0x150(%rsp)
     +0xd48: movups  0x528(%rbx),%xmm0
     +0xd4f: movups  0x538(%rbx),%xmm1
     +0xd56: xorps   0x160(%rsp),%xmm0
     +0xd5e: xorps   0x170(%rsp),%xmm1
     +0xd66: movaps  %xmm0,0x160(%rsp)
     +0xd6e: movaps  %xmm1,0x170(%rsp)
     +0xd76: mov     0x548(%rbx),%rax
     +0xd7d: xor     %rax,0x180(%rsp)
     +0xd85: mov     %r13,%rdi
     +0xd88: call    <mldsa_keccakf1600_permute>
     +0xd8d: movups  0x550(%rbx),%xmm0
     +0xd94: movups  0x560(%rbx),%xmm1
     +0xd9b: xorps   0x100(%rsp),%xmm0
     +0xda3: xorps   0x110(%rsp),%xmm1
     +0xdab: movaps  %xmm0,0x100(%rsp)
     +0xdb3: movaps  %xmm1,0x110(%rsp)
     +0xdbb: movups  0x570(%rbx),%xmm0
     +0xdc2: movups  0x580(%rbx),%xmm1
     +0xdc9: xorps   0x120(%rsp),%xmm0
     +0xdd1: xorps   0x130(%rsp),%xmm1
     +0xdd9: movaps  %xmm0,0x120(%rsp)
     +0xde1: movaps  %xmm1,0x130(%rsp)
     +0xde9: movups  0x590(%rbx),%xmm0
     +0xdf0: movups  0x5a0(%rbx),%xmm1
     +0xdf7: xorps   0x140(%rsp),%xmm0
     +0xdff: xorps   0x150(%rsp),%xmm1
     +0xe07: movaps  %xmm0,0x140(%rsp)
     +0xe0f: movaps  %xmm1,0x150(%rsp)
     +0xe17: movups  0x5b0(%rbx),%xmm0
     +0xe1e: movups  0x5c0(%rbx),%xmm1
     +0xe25: xorps   0x160(%rsp),%xmm0
     +0xe2d: xorps   0x170(%rsp),%xmm1
     +0xe35: movaps  %xmm0,0x160(%rsp)
     +0xe3d: movaps  %xmm1,0x170(%rsp)
     +0xe45: mov     0x5d0(%rbx),%rax
     +0xe4c: xor     %rax,0x180(%rsp)
     +0xe54: mov     %r13,%rdi
     +0xe57: call    <mldsa_keccakf1600_permute>
     +0xe5c: movups  0x5d8(%rbx),%xmm0
     +0xe63: movups  0x5e8(%rbx),%xmm1
     +0xe6a: xorps   0x100(%rsp),%xmm0
     +0xe72: xorps   0x110(%rsp),%xmm1
     +0xe7a: movaps  %xmm0,0x100(%rsp)
     +0xe82: movaps  %xmm1,0x110(%rsp)
     +0xe8a: movups  0x5f8(%rbx),%xmm0
     +0xe91: movups  0x608(%rbx),%xmm1
     +0xe98: xorps   0x120(%rsp),%xmm0
     +0xea0: xorps   0x130(%rsp),%xmm1
     +0xea8: movaps  %xmm0,0x120(%rsp)
     +0xeb0: movaps  %xmm1,0x130(%rsp)
     +0xeb8: movups  0x618(%rbx),%xmm0
     +0xebf: movups  0x628(%rbx),%xmm1
     +0xec6: xorps   0x140(%rsp),%xmm0
     +0xece: xorps   0x150(%rsp),%xmm1
     +0xed6: movaps  %xmm0,0x140(%rsp)
     +0xede: movaps  %xmm1,0x150(%rsp)
     +0xee6: movups  0x638(%rbx),%xmm0
     +0xeed: movups  0x648(%rbx),%xmm1
     +0xef4: xorps   0x160(%rsp),%xmm0
     +0xefc: xorps   0x170(%rsp),%xmm1
     +0xf04: movaps  %xmm0,0x160(%rsp)
     +0xf0c: movaps  %xmm1,0x170(%rsp)
     +0xf14: mov     0x658(%rbx),%rax
     +0xf1b: xor     %rax,0x180(%rsp)
     +0xf23: mov     %r13,%rdi
     +0xf26: call    <mldsa_keccakf1600_permute>
     +0xf2b: movups  0x660(%rbx),%xmm0
     +0xf32: movups  0x670(%rbx),%xmm1
     +0xf39: xorps   0x100(%rsp),%xmm0
     +0xf41: xorps   0x110(%rsp),%xmm1
     +0xf49: movaps  %xmm0,0x100(%rsp)
     +0xf51: movaps  %xmm1,0x110(%rsp)
     +0xf59: movups  0x680(%rbx),%xmm0
     +0xf60: movups  0x690(%rbx),%xmm1
     +0xf67: xorps   0x120(%rsp),%xmm0
     +0xf6f: xorps   0x130(%rsp),%xmm1
     +0xf77: movaps  %xmm0,0x120(%rsp)
     +0xf7f: movaps  %xmm1,0x130(%rsp)
     +0xf87: movups  0x6a0(%rbx),%xmm0
     +0xf8e: movups  0x6b0(%rbx),%xmm1
     +0xf95: xorps   0x140(%rsp),%xmm0
     +0xf9d: xorps   0x150(%rsp),%xmm1
     +0xfa5: movaps  %xmm0,0x140(%rsp)
     +0xfad: movaps  %xmm1,0x150(%rsp)
     +0xfb5: movups  0x6c0(%rbx),%xmm0
     +0xfbc: movups  0x6d0(%rbx),%xmm1
     +0xfc3: xorps   0x160(%rsp),%xmm0
     +0xfcb: xorps   0x170(%rsp),%xmm1
     +0xfd3: movaps  %xmm0,0x160(%rsp)
     +0xfdb: movaps  %xmm1,0x170(%rsp)
     +0xfe3: mov     0x6e0(%rbx),%rax
     +0xfea: xor     %rax,0x180(%rsp)
     +0xff2: mov     %r13,%rdi
     +0xff5: call    <mldsa_keccakf1600_permute>
     +0xffa: movups  0x6e8(%rbx),%xmm0
    +0x1001: movups  0x6f8(%rbx),%xmm1
    +0x1008: xorps   0x100(%rsp),%xmm0
    +0x1010: xorps   0x110(%rsp),%xmm1
    +0x1018: movaps  %xmm0,0x100(%rsp)
    +0x1020: movaps  %xmm1,0x110(%rsp)
    +0x1028: movups  0x708(%rbx),%xmm0
    +0x102f: movups  0x718(%rbx),%xmm1
    +0x1036: xorps   0x120(%rsp),%xmm0
    +0x103e: xorps   0x130(%rsp),%xmm1
    +0x1046: movaps  %xmm0,0x120(%rsp)
    +0x104e: movaps  %xmm1,0x130(%rsp)
    +0x1056: movups  0x728(%rbx),%xmm0
    +0x105d: movups  0x738(%rbx),%xmm1
    +0x1064: xorps   0x140(%rsp),%xmm0
    +0x106c: xorps   0x150(%rsp),%xmm1
    +0x1074: movaps  %xmm0,0x140(%rsp)
    +0x107c: movaps  %xmm1,0x150(%rsp)
    +0x1084: movups  0x748(%rbx),%xmm0
    +0x108b: movups  0x758(%rbx),%xmm1
    +0x1092: xorps   0x160(%rsp),%xmm0
    +0x109a: xorps   0x170(%rsp),%xmm1
    +0x10a2: movaps  %xmm0,0x160(%rsp)
    +0x10aa: movaps  %xmm1,0x170(%rsp)
    +0x10b2: mov     0x768(%rbx),%rax
    +0x10b9: xor     %rax,0x180(%rsp)
    +0x10c1: mov     %r13,%rdi
    +0x10c4: call    <mldsa_keccakf1600_permute>
    +0x10c9: movups  0x770(%rbx),%xmm0
    +0x10d0: movups  0x780(%rbx),%xmm1
    +0x10d7: xorps   0x100(%rsp),%xmm0
    +0x10df: xorps   0x110(%rsp),%xmm1
    +0x10e7: movaps  %xmm0,0x100(%rsp)
    +0x10ef: movaps  %xmm1,0x110(%rsp)
    +0x10f7: movups  0x790(%rbx),%xmm0
    +0x10fe: movups  0x7a0(%rbx),%xmm1
    +0x1105: xorps   0x120(%rsp),%xmm0
    +0x110d: xorps   0x130(%rsp),%xmm1
    +0x1115: movaps  %xmm0,0x120(%rsp)
    +0x111d: movaps  %xmm1,0x130(%rsp)
    +0x1125: movups  0x7b0(%rbx),%xmm0
    +0x112c: movups  0x7c0(%rbx),%xmm1
    +0x1133: xorps   0x140(%rsp),%xmm0
    +0x113b: xorps   0x150(%rsp),%xmm1
    +0x1143: movaps  %xmm0,0x140(%rsp)
    +0x114b: movaps  %xmm1,0x150(%rsp)
    +0x1153: movups  0x7d0(%rbx),%xmm0
    +0x115a: movups  0x7e0(%rbx),%xmm1
    +0x1161: xorps   0x160(%rsp),%xmm0
    +0x1169: xorps   0x170(%rsp),%xmm1
    +0x1171: movaps  %xmm0,0x160(%rsp)
    +0x1179: movaps  %xmm1,0x170(%rsp)
    +0x1181: mov     0x7f0(%rbx),%rax
    +0x1188: xor     %rax,0x180(%rsp)
    +0x1190: mov     %r13,%rdi
    +0x1193: call    <mldsa_keccakf1600_permute>
    +0x1198: movups  0x7f8(%rbx),%xmm0
    +0x119f: movups  0x808(%rbx),%xmm1
    +0x11a6: xorps   0x100(%rsp),%xmm0
    +0x11ae: xorps   0x110(%rsp),%xmm1
    +0x11b6: movaps  %xmm0,0x100(%rsp)
    +0x11be: movaps  %xmm1,0x110(%rsp)
    +0x11c6: movups  0x818(%rbx),%xmm0
    +0x11cd: movups  0x828(%rbx),%xmm1
    +0x11d4: xorps   0x120(%rsp),%xmm0
    +0x11dc: xorps   0x130(%rsp),%xmm1
    +0x11e4: movaps  %xmm0,0x120(%rsp)
    +0x11ec: movaps  %xmm1,0x130(%rsp)
    +0x11f4: movups  0x838(%rbx),%xmm0
    +0x11fb: movups  0x848(%rbx),%xmm1
    +0x1202: xorps   0x140(%rsp),%xmm0
    +0x120a: xorps   0x150(%rsp),%xmm1
    +0x1212: movaps  %xmm0,0x140(%rsp)
    +0x121a: movaps  %xmm1,0x150(%rsp)
    +0x1222: movups  0x858(%rbx),%xmm0
    +0x1229: movups  0x868(%rbx),%xmm1
    +0x1230: xorps   0x160(%rsp),%xmm0
    +0x1238: xorps   0x170(%rsp),%xmm1
    +0x1240: movaps  %xmm0,0x160(%rsp)
    +0x1248: movaps  %xmm1,0x170(%rsp)
    +0x1250: mov     0x878(%rbx),%rax
    +0x1257: xor     %rax,0x180(%rsp)
    +0x125f: mov     %r13,%rdi
    +0x1262: call    <mldsa_keccakf1600_permute>
    +0x1267: movups  0x880(%rbx),%xmm0
    +0x126e: movups  0x890(%rbx),%xmm1
    +0x1275: xorps   0x100(%rsp),%xmm0
    +0x127d: xorps   0x110(%rsp),%xmm1
    +0x1285: movaps  %xmm0,0x100(%rsp)
    +0x128d: movaps  %xmm1,0x110(%rsp)
    +0x1295: movups  0x8a0(%rbx),%xmm0
    +0x129c: movups  0x8b0(%rbx),%xmm1
    +0x12a3: xorps   0x120(%rsp),%xmm0
    +0x12ab: xorps   0x130(%rsp),%xmm1
    +0x12b3: movaps  %xmm0,0x120(%rsp)
    +0x12bb: movaps  %xmm1,0x130(%rsp)
    +0x12c3: movups  0x8c0(%rbx),%xmm0
    +0x12ca: movups  0x8d0(%rbx),%xmm1
    +0x12d1: xorps   0x140(%rsp),%xmm0
    +0x12d9: xorps   0x150(%rsp),%xmm1
    +0x12e1: movaps  %xmm0,0x140(%rsp)
    +0x12e9: movaps  %xmm1,0x150(%rsp)
    +0x12f1: movups  0x8e0(%rbx),%xmm0
    +0x12f8: movups  0x8f0(%rbx),%xmm1
    +0x12ff: xorps   0x160(%rsp),%xmm0
    +0x1307: xorps   0x170(%rsp),%xmm1
    +0x130f: movaps  %xmm0,0x160(%rsp)
    +0x1317: movaps  %xmm1,0x170(%rsp)
    +0x131f: mov     0x900(%rbx),%rax
    +0x1326: xor     %rax,0x180(%rsp)
    +0x132e: mov     %r13,%rdi
    +0x1331: call    <mldsa_keccakf1600_permute>
    +0x1336: movups  0x908(%rbx),%xmm0
    +0x133d: movups  0x918(%rbx),%xmm1
    +0x1344: xorps   0x100(%rsp),%xmm0
    +0x134c: xorps   0x110(%rsp),%xmm1
    +0x1354: movaps  %xmm0,0x100(%rsp)
    +0x135c: movaps  %xmm1,0x110(%rsp)
    +0x1364: movups  0x928(%rbx),%xmm0
    +0x136b: movups  0x938(%rbx),%xmm1
    +0x1372: xorps   0x120(%rsp),%xmm0
    +0x137a: xorps   0x130(%rsp),%xmm1
    +0x1382: movaps  %xmm0,0x120(%rsp)
    +0x138a: movaps  %xmm1,0x130(%rsp)
    +0x1392: movups  0x948(%rbx),%xmm0
    +0x1399: movups  0x958(%rbx),%xmm1
    +0x13a0: xorps   0x140(%rsp),%xmm0
    +0x13a8: xorps   0x150(%rsp),%xmm1
    +0x13b0: movaps  %xmm0,0x140(%rsp)
    +0x13b8: movaps  %xmm1,0x150(%rsp)
    +0x13c0: movups  0x968(%rbx),%xmm0
    +0x13c7: movups  0x978(%rbx),%xmm1
    +0x13ce: xorps   0x160(%rsp),%xmm0
    +0x13d6: xorps   0x170(%rsp),%xmm1
    +0x13de: movaps  %xmm0,0x160(%rsp)
    +0x13e6: movaps  %xmm1,0x170(%rsp)
    +0x13ee: mov     0x988(%rbx),%rax
    +0x13f5: xor     %rax,0x180(%rsp)
    +0x13fd: mov     %r13,%rdi
    +0x1400: call    <mldsa_keccakf1600_permute>
    +0x1405: movups  0x990(%rbx),%xmm0
    +0x140c: movups  0x9a0(%rbx),%xmm1
    +0x1413: xorps   0x100(%rsp),%xmm0
    +0x141b: xorps   0x110(%rsp),%xmm1
    +0x1423: movaps  %xmm0,0x100(%rsp)
    +0x142b: movaps  %xmm1,0x110(%rsp)
    +0x1433: movups  0x9b0(%rbx),%xmm0
    +0x143a: movups  0x9c0(%rbx),%xmm1
    +0x1441: xorps   0x120(%rsp),%xmm0
    +0x1449: xorps   0x130(%rsp),%xmm1
    +0x1451: movaps  %xmm0,0x120(%rsp)
    +0x1459: movaps  %xmm1,0x130(%rsp)
    +0x1461: movups  0x9d0(%rbx),%xmm0
    +0x1468: movups  0x9e0(%rbx),%xmm1
    +0x146f: xorps   0x140(%rsp),%xmm0
    +0x1477: xorps   0x150(%rsp),%xmm1
    +0x147f: movaps  %xmm0,0x140(%rsp)
    +0x1487: movaps  %xmm1,0x150(%rsp)
    +0x148f: movups  0x9f0(%rbx),%xmm0
    +0x1496: movups  0xa00(%rbx),%xmm1
    +0x149d: xorps   0x160(%rsp),%xmm0
    +0x14a5: xorps   0x170(%rsp),%xmm1
    +0x14ad: movaps  %xmm0,0x160(%rsp)
    +0x14b5: movaps  %xmm1,0x170(%rsp)
    +0x14bd: mov     0xa10(%rbx),%rax
    +0x14c4: xor     %rax,0x180(%rsp)
    +0x14cc: mov     %r13,%rdi
    +0x14cf: call    <mldsa_keccakf1600_permute>
    +0x14d4: mov     0xa18(%rbx),%rax
    +0x14db: xor     %rax,0x100(%rsp)
    +0x14e3: xorb    $0x1f,0x108(%rsp)
    +0x14eb: xorb    $0x80,0x187(%rsp)
    +0x14f3: movl    $0x88,0x1c8(%rsp)
    +0x14fe: mov     %r13,%rdi
    +0x1501: call    <mldsa_keccakf1600_permute>
    +0x1506: movaps  0x100(%rsp),%xmm0
    +0x150e: movaps  0x110(%rsp),%xmm1
    +0x1516: movdqa  0x120(%rsp),%xmm2
    +0x151f: movaps  0x130(%rsp),%xmm3
    +0x1527: movaps  %xmm3,0xe30(%rsp)
    +0x152f: movdqa  %xmm2,0xe20(%rsp)
    +0x1538: movaps  %xmm1,0xe10(%rsp)
    +0x1540: movaps  %xmm0,0xe00(%rsp)
    +0x1548: xorps   %xmm0,%xmm0
    +0x154b: movaps  %xmm0,0x140(%rsp)
    +0x1553: movaps  %xmm0,0x150(%rsp)
    +0x155b: movaps  %xmm0,0x160(%rsp)
    +0x1563: movaps  %xmm0,0x170(%rsp)
    +0x156b: movaps  %xmm0,0x180(%rsp)
    +0x1573: movaps  %xmm0,0x190(%rsp)
    +0x157b: movaps  %xmm0,0x1a0(%rsp)
    +0x1583: movaps  %xmm0,0x1b0(%rsp)
    +0x158b: movaps  %xmm0,0x1c0(%rsp)
    +0x1593: movaps  %xmm0,0x100(%rsp)
    +0x159b: movaps  %xmm0,0x110(%rsp)
    +0x15a3: movaps  %xmm0,0x120(%rsp)
    +0x15ab: movaps  %xmm0,0x130(%rsp)
    +0x15b3: movaps  %xmm0,0x1c0(%rsp)
    +0x15bb: movaps  %xmm0,0x1b0(%rsp)
    +0x15c3: movaps  %xmm0,0x1a0(%rsp)
    +0x15cb: movaps  %xmm0,0x190(%rsp)
    +0x15d3: movaps  %xmm0,0x180(%rsp)
    +0x15db: movaps  %xmm0,0x170(%rsp)
    +0x15e3: movaps  %xmm0,0x160(%rsp)
    +0x15eb: movaps  %xmm0,0x150(%rsp)
    +0x15f3: movaps  %xmm0,0x140(%rsp)
    +0x15fb: movaps  %xmm0,0x130(%rsp)
    +0x1603: movaps  %xmm0,0x120(%rsp)
    +0x160b: movaps  %xmm0,0x110(%rsp)
    +0x1613: movaps  %xmm0,0x100(%rsp)
    +0x161b: mov     0x18(%rsp),%rax
    +0x1620: mov     %rax,(%rsp)
    +0x1624: lea     0x580(%rsp),%rdi
    +0x162c: lea     0xe00(%rsp),%r15
    +0x1634: mov     $0x40,%edx
    +0x1639: mov     %r15,%rsi
    +0x163c: mov     0x538(%rsp),%rcx
    +0x1644: mov     %r14,%r8
    +0x1647: mov     %r12,%r9
    +0x164a: call    <mld_H87>
    +0x164f: xorps   %xmm0,%xmm0
    +0x1652: movaps  %xmm0,0xe30(%rsp)
    +0x165a: movaps  %xmm0,0xe20(%rsp)
    +0x1662: movaps  %xmm0,0xe10(%rsp)
    +0x166a: movaps  %xmm0,0xe00(%rsp)
    +0x1672: movabs  $0x380200100000000,%r12
    +0x167c: lea     0x1600(%rsp),%r14
    +0x1684: mov     %r14,%rdi
    +0x1687: call    <mldsa_poly_ntt>
    +0x168c: lea     0x1a00(%rsp),%rdi
    +0x1694: call    <mldsa_poly_ntt>
    +0x1699: lea     0x1e00(%rsp),%rdi
    +0x16a1: call    <mldsa_poly_ntt>
    +0x16a6: lea     0x2200(%rsp),%rdi
    +0x16ae: call    <mldsa_poly_ntt>
    +0x16b3: lea     0x2600(%rsp),%rdi
    +0x16bb: call    <mldsa_poly_ntt>
    +0x16c0: lea     0x2a00(%rsp),%rdi
    +0x16c8: call    <mldsa_poly_ntt>
    +0x16cd: lea     0x2e00(%rsp),%rdi
    +0x16d5: call    <mldsa_poly_ntt>
    +0x16da: movdqu  (%rbx),%xmm0
    +0x16de: movups  0x10(%rbx),%xmm1
    +0x16e2: movaps  %xmm1,0x510(%rsp)
    +0x16ea: movdqa  %xmm0,0x500(%rsp)
    +0x16f3: lea     0x1200(%rsp),%r15
    +0x16fb: lea     0x540(%rsp),%rsi
    +0x1703: mov     %r15,%rdi
    +0x1706: call    <mldsa87_poly_challenge>
    +0x170b: mov     %r15,%rdi
    +0x170e: call    <mldsa_poly_ntt>
    +0x1713: add     $0x21,%rbx
    +0x1717: lea     0xe04(%rsp),%r15
    +0x171f: xor     %r13d,%r13d
    +0x1722: lea     0xa00(%rsp),%rdi
    +0x172a: lea     0x100(%rsp),%rsi
    +0x1732: mov     %r14,%rdx
    +0x1735: mov     %r13d,%ecx
    +0x1738: call    <mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy>
    +0x173d: mov     %rbx,%rax
    +0x1740: xor     %ecx,%ecx
    +0x1742: pxor    %xmm2,%xmm2
    +0x1746: movq    0x7072(%rip),%xmm3
    +0x174e: movq    0x707a(%rip),%xmm4
    +0x1756: cs      nopw 0x0(%rax,%rax,1)
    +0x1760: mov     (%rax),%edx
    +0x1762: movd    %edx,%xmm0
    +0x1766: movzbl  (%rax),%esi
    +0x1769: mov     %edx,%edi
    +0x176b: shr     $0x16,%edi
    +0x176e: and     $0x3,%edi
    +0x1771: shr     $0xc,%edx
    +0x1774: and     $0xf,%edx
    +0x1777: shr     $0x2,%esi
    +0x177a: punpcklbw %xmm2,%xmm0
    +0x177e: pmullw  %xmm3,%xmm0
    +0x1782: pand    %xmm4,%xmm0
    +0x1786: movzbl  -0x1(%rax),%r8d
    +0x178b: movd    %r8d,%xmm1
    +0x1790: pinsrw  $0x1,%esi,%xmm1
    +0x1795: pinsrw  $0x2,%edx,%xmm1
    +0x179a: pinsrw  $0x3,%edi,%xmm1
    +0x179f: por     %xmm0,%xmm1
    +0x17a3: punpcklwd %xmm2,%xmm1
    +0x17a7: movdqa  %xmm1,0x600(%rsp,%rcx,1)
    +0x17b0: add     $0x10,%rcx
    +0x17b4: add     $0x5,%rax
    +0x17b8: cmp     $0x400,%rcx
    +0x17bf: jne     <mldsa87_verify_internal+0x1760>
    +0x17c1: movdqa  0x600(%rsp),%xmm0
    +0x17ca: movdqa  0x610(%rsp),%xmm1
    +0x17d3: movdqa  0x620(%rsp),%xmm2
    +0x17dc: movdqa  0x630(%rsp),%xmm3
    +0x17e5: pslld   $0xd,%xmm0
    +0x17ea: pslld   $0xd,%xmm1
    +0x17ef: movdqa  %xmm0,0x600(%rsp)
    +0x17f8: movdqa  %xmm1,0x610(%rsp)
    +0x1801: pslld   $0xd,%xmm2
    +0x1806: pslld   $0xd,%xmm3
    +0x180b: movdqa  %xmm2,0x620(%rsp)
    +0x1814: movdqa  %xmm3,0x630(%rsp)
    +0x181d: movdqa  0x640(%rsp),%xmm0
    +0x1826: movdqa  0x650(%rsp),%xmm1
    +0x182f: pslld   $0xd,%xmm0
    +0x1834: pslld   $0xd,%xmm1
    +0x1839: movdqa  %xmm0,0x640(%rsp)
    +0x1842: movdqa  %xmm1,0x650(%rsp)
    +0x184b: movdqa  0x660(%rsp),%xmm0
    +0x1854: movdqa  0x670(%rsp),%xmm1
    +0x185d: pslld   $0xd,%xmm0
    +0x1862: pslld   $0xd,%xmm1
    +0x1867: movdqa  %xmm0,0x660(%rsp)
    +0x1870: movdqa  %xmm1,0x670(%rsp)
    +0x1879: movdqa  0x680(%rsp),%xmm0
    +0x1882: movdqa  0x690(%rsp),%xmm1
    +0x188b: pslld   $0xd,%xmm0
    +0x1890: pslld   $0xd,%xmm1
    +0x1895: movdqa  %xmm0,0x680(%rsp)
    +0x189e: movdqa  %xmm1,0x690(%rsp)
    +0x18a7: movdqa  0x6a0(%rsp),%xmm0
    +0x18b0: movdqa  0x6b0(%rsp),%xmm1
    +0x18b9: pslld   $0xd,%xmm0
    +0x18be: pslld   $0xd,%xmm1
    +0x18c3: movdqa  %xmm0,0x6a0(%rsp)
    +0x18cc: movdqa  %xmm1,0x6b0(%rsp)
    +0x18d5: movdqa  0x6c0(%rsp),%xmm0
    +0x18de: movdqa  0x6d0(%rsp),%xmm1
    +0x18e7: pslld   $0xd,%xmm0
    +0x18ec: pslld   $0xd,%xmm1
    +0x18f1: movdqa  %xmm0,0x6c0(%rsp)
    +0x18fa: movdqa  %xmm1,0x6d0(%rsp)
    +0x1903: movdqa  0x6e0(%rsp),%xmm0
    +0x190c: movdqa  0x6f0(%rsp),%xmm1
    +0x1915: pslld   $0xd,%xmm0
    +0x191a: pslld   $0xd,%xmm1
    +0x191f: movdqa  %xmm0,0x6e0(%rsp)
    +0x1928: movdqa  %xmm1,0x6f0(%rsp)
    +0x1931: movdqa  0x700(%rsp),%xmm0
    +0x193a: movdqa  0x710(%rsp),%xmm1
    +0x1943: pslld   $0xd,%xmm0
    +0x1948: pslld   $0xd,%xmm1
    +0x194d: movdqa  %xmm0,0x700(%rsp)
    +0x1956: movdqa  %xmm1,0x710(%rsp)
    +0x195f: movdqa  0x720(%rsp),%xmm0
    +0x1968: movdqa  0x730(%rsp),%xmm1
    +0x1971: pslld   $0xd,%xmm0
    +0x1976: pslld   $0xd,%xmm1
    +0x197b: movdqa  %xmm0,0x720(%rsp)
    +0x1984: movdqa  %xmm1,0x730(%rsp)
    +0x198d: movdqa  0x740(%rsp),%xmm0
    +0x1996: movdqa  0x750(%rsp),%xmm1
    +0x199f: pslld   $0xd,%xmm0
    +0x19a4: pslld   $0xd,%xmm1
    +0x19a9: movdqa  %xmm0,0x740(%rsp)
    +0x19b2: movdqa  %xmm1,0x750(%rsp)
    +0x19bb: movdqa  0x760(%rsp),%xmm0
    +0x19c4: movdqa  0x770(%rsp),%xmm1
    +0x19cd: pslld   $0xd,%xmm0
    +0x19d2: pslld   $0xd,%xmm1
    +0x19d7: movdqa  %xmm0,0x760(%rsp)
    +0x19e0: movdqa  %xmm1,0x770(%rsp)
    +0x19e9: movdqa  0x780(%rsp),%xmm0
    +0x19f2: movdqa  0x790(%rsp),%xmm1
    +0x19fb: pslld   $0xd,%xmm0
    +0x1a00: pslld   $0xd,%xmm1
    +0x1a05: movdqa  %xmm0,0x780(%rsp)
    +0x1a0e: movdqa  %xmm1,0x790(%rsp)
    +0x1a17: movdqa  0x7a0(%rsp),%xmm0
    +0x1a20: movdqa  0x7b0(%rsp),%xmm1
    +0x1a29: pslld   $0xd,%xmm0
    +0x1a2e: pslld   $0xd,%xmm1
    +0x1a33: movdqa  %xmm0,0x7a0(%rsp)
    +0x1a3c: movdqa  %xmm1,0x7b0(%rsp)
    +0x1a45: movdqa  0x7c0(%rsp),%xmm0
    +0x1a4e: movdqa  0x7d0(%rsp),%xmm1
    +0x1a57: pslld   $0xd,%xmm0
    +0x1a5c: pslld   $0xd,%xmm1
    +0x1a61: movdqa  %xmm0,0x7c0(%rsp)
    +0x1a6a: movdqa  %xmm1,0x7d0(%rsp)
    +0x1a73: movdqa  0x7e0(%rsp),%xmm0
    +0x1a7c: movdqa  0x7f0(%rsp),%xmm1
    +0x1a85: pslld   $0xd,%xmm0
    +0x1a8a: pslld   $0xd,%xmm1
    +0x1a8f: movdqa  %xmm0,0x7e0(%rsp)
    +0x1a98: movdqa  %xmm1,0x7f0(%rsp)
    +0x1aa1: movdqa  0x800(%rsp),%xmm0
    +0x1aaa: movdqa  0x810(%rsp),%xmm1
    +0x1ab3: pslld   $0xd,%xmm0
    +0x1ab8: pslld   $0xd,%xmm1
    +0x1abd: movdqa  %xmm0,0x800(%rsp)
    +0x1ac6: movdqa  %xmm1,0x810(%rsp)
    +0x1acf: movdqa  0x820(%rsp),%xmm0
    +0x1ad8: movdqa  0x830(%rsp),%xmm1
    +0x1ae1: pslld   $0xd,%xmm0
    +0x1ae6: pslld   $0xd,%xmm1
    +0x1aeb: movdqa  %xmm0,0x820(%rsp)
    +0x1af4: movdqa  %xmm1,0x830(%rsp)
    +0x1afd: movdqa  0x840(%rsp),%xmm0
    +0x1b06: movdqa  0x850(%rsp),%xmm1
    +0x1b0f: pslld   $0xd,%xmm0
    +0x1b14: pslld   $0xd,%xmm1
    +0x1b19: movdqa  %xmm0,0x840(%rsp)
    +0x1b22: movdqa  %xmm1,0x850(%rsp)
    +0x1b2b: movdqa  0x860(%rsp),%xmm0
    +0x1b34: movdqa  0x870(%rsp),%xmm1
    +0x1b3d: pslld   $0xd,%xmm0
    +0x1b42: pslld   $0xd,%xmm1
    +0x1b47: movdqa  %xmm0,0x860(%rsp)
    +0x1b50: movdqa  %xmm1,0x870(%rsp)
    +0x1b59: movdqa  0x880(%rsp),%xmm0
    +0x1b62: movdqa  0x890(%rsp),%xmm1
    +0x1b6b: pslld   $0xd,%xmm0
    +0x1b70: pslld   $0xd,%xmm1
    +0x1b75: movdqa  %xmm0,0x880(%rsp)
    +0x1b7e: movdqa  %xmm1,0x890(%rsp)
    +0x1b87: movdqa  0x8a0(%rsp),%xmm0
    +0x1b90: movdqa  0x8b0(%rsp),%xmm1
    +0x1b99: pslld   $0xd,%xmm0
    +0x1b9e: pslld   $0xd,%xmm1
    +0x1ba3: movdqa  %xmm0,0x8a0(%rsp)
    +0x1bac: movdqa  %xmm1,0x8b0(%rsp)
    +0x1bb5: movdqa  0x8c0(%rsp),%xmm0
    +0x1bbe: movdqa  0x8d0(%rsp),%xmm1
    +0x1bc7: pslld   $0xd,%xmm0
    +0x1bcc: pslld   $0xd,%xmm1
    +0x1bd1: movdqa  %xmm0,0x8c0(%rsp)
    +0x1bda: movdqa  %xmm1,0x8d0(%rsp)
    +0x1be3: movdqa  0x8e0(%rsp),%xmm0
    +0x1bec: movdqa  0x8f0(%rsp),%xmm1
    +0x1bf5: pslld   $0xd,%xmm0
    +0x1bfa: pslld   $0xd,%xmm1
    +0x1bff: movdqa  %xmm0,0x8e0(%rsp)
    +0x1c08: movdqa  %xmm1,0x8f0(%rsp)
    +0x1c11: movdqa  0x900(%rsp),%xmm0
    +0x1c1a: movdqa  0x910(%rsp),%xmm1
    +0x1c23: pslld   $0xd,%xmm0
    +0x1c28: pslld   $0xd,%xmm1
    +0x1c2d: movdqa  %xmm0,0x900(%rsp)
    +0x1c36: movdqa  %xmm1,0x910(%rsp)
    +0x1c3f: movdqa  0x920(%rsp),%xmm0
    +0x1c48: movdqa  0x930(%rsp),%xmm1
    +0x1c51: pslld   $0xd,%xmm0
    +0x1c56: pslld   $0xd,%xmm1
    +0x1c5b: movdqa  %xmm0,0x920(%rsp)
    +0x1c64: movdqa  %xmm1,0x930(%rsp)
    +0x1c6d: movdqa  0x940(%rsp),%xmm0
    +0x1c76: movdqa  0x950(%rsp),%xmm1
    +0x1c7f: pslld   $0xd,%xmm0
    +0x1c84: pslld   $0xd,%xmm1
    +0x1c89: movdqa  %xmm0,0x940(%rsp)
    +0x1c92: movdqa  %xmm1,0x950(%rsp)
    +0x1c9b: movdqa  0x960(%rsp),%xmm0
    +0x1ca4: movdqa  0x970(%rsp),%xmm1
    +0x1cad: pslld   $0xd,%xmm0
    +0x1cb2: pslld   $0xd,%xmm1
    +0x1cb7: movdqa  %xmm0,0x960(%rsp)
    +0x1cc0: movdqa  %xmm1,0x970(%rsp)
    +0x1cc9: movdqa  0x980(%rsp),%xmm0
    +0x1cd2: movdqa  0x990(%rsp),%xmm1
    +0x1cdb: pslld   $0xd,%xmm0
    +0x1ce0: pslld   $0xd,%xmm1
    +0x1ce5: movdqa  %xmm0,0x980(%rsp)
    +0x1cee: movdqa  %xmm1,0x990(%rsp)
    +0x1cf7: movdqa  0x9a0(%rsp),%xmm0
    +0x1d00: movdqa  0x9b0(%rsp),%xmm1
    +0x1d09: pslld   $0xd,%xmm0
    +0x1d0e: pslld   $0xd,%xmm1
    +0x1d13: movdqa  %xmm0,0x9a0(%rsp)
    +0x1d1c: movdqa  %xmm1,0x9b0(%rsp)
    +0x1d25: movdqa  0x9c0(%rsp),%xmm0
    +0x1d2e: movdqa  0x9d0(%rsp),%xmm1
    +0x1d37: pslld   $0xd,%xmm0
    +0x1d3c: pslld   $0xd,%xmm1
    +0x1d41: movdqa  %xmm0,0x9c0(%rsp)
    +0x1d4a: movdqa  %xmm1,0x9d0(%rsp)
    +0x1d53: movdqa  0x9e0(%rsp),%xmm0
    +0x1d5c: movdqa  0x9f0(%rsp),%xmm1
    +0x1d65: pslld   $0xd,%xmm0
    +0x1d6a: pslld   $0xd,%xmm1
    +0x1d6f: movdqa  %xmm0,0x9e0(%rsp)
    +0x1d78: movdqa  %xmm1,0x9f0(%rsp)
    +0x1d81: lea     0x600(%rsp),%rdi
    +0x1d89: call    <mldsa_poly_ntt>
    +0x1d8e: mov     $0x1,%eax
    +0x1d93: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1da0: movslq  0x5fc(%rsp,%rax,4),%rcx
    +0x1da8: movslq  0x11fc(%rsp,%rax,4),%rdx
    +0x1db0: imul    %rcx,%rdx
    +0x1db4: mov     %rdx,%rcx
    +0x1db7: imul    %r12,%rcx
    +0x1dbb: sar     $0x20,%rcx
    +0x1dbf: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x1dc6: add     %rdx,%rcx
    +0x1dc9: shr     $0x20,%rcx
    +0x1dcd: mov     %ecx,0x5fc(%rsp,%rax,4)
    +0x1dd4: movslq  0x600(%rsp,%rax,4),%rcx
    +0x1ddc: movslq  0x1200(%rsp,%rax,4),%rdx
    +0x1de4: imul    %rcx,%rdx
    +0x1de8: mov     %rdx,%rcx
    +0x1deb: imul    %r12,%rcx
    +0x1def: sar     $0x20,%rcx
    +0x1df3: imul    $0xffffffffff801fff,%rcx,%rcx
    +0x1dfa: add     %rdx,%rcx
    +0x1dfd: shr     $0x20,%rcx
    +0x1e01: mov     %ecx,0x600(%rsp,%rax,4)
    +0x1e08: add     $0x2,%rax
    +0x1e0c: cmp     $0x101,%rax
    +0x1e12: jne     <mldsa87_verify_internal+0x1da0>
    +0x1e14: mov     $0xc,%eax
    +0x1e19: lea     0xa00(%rsp),%rdi
    +0x1e21: movdqa  0x6957(%rip),%xmm5
    +0x1e29: movdqa  0x695f(%rip),%xmm6
    +0x1e31: data16  data16 data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1e40: movdqa  0x9d0(%rsp,%rax,4),%xmm0
    +0x1e49: movdqa  0x9e0(%rsp,%rax,4),%xmm1
    +0x1e52: movdqa  0x9f0(%rsp,%rax,4),%xmm2
    +0x1e5b: movdqa  0xa00(%rsp,%rax,4),%xmm3
    +0x1e64: psubd   0x5d0(%rsp,%rax,4),%xmm0
    +0x1e6d: psubd   0x5e0(%rsp,%rax,4),%xmm1
    +0x1e76: movdqa  %xmm0,0x9d0(%rsp,%rax,4)
    +0x1e7f: movdqa  %xmm1,0x9e0(%rsp,%rax,4)
    +0x1e88: psubd   0x5f0(%rsp,%rax,4),%xmm2
    +0x1e91: psubd   0x600(%rsp,%rax,4),%xmm3
    +0x1e9a: movdqa  %xmm2,0x9f0(%rsp,%rax,4)
    +0x1ea3: movdqa  %xmm3,0xa00(%rsp,%rax,4)
    +0x1eac: add     $0x10,%rax
    +0x1eb0: cmp     $0x10c,%rax
    +0x1eb6: jne     <mldsa87_verify_internal+0x1e40>
    +0x1eb8: mov     $0x4,%eax
    +0x1ebd: nopl    (%rax)
    +0x1ec0: movdqa  0x9f0(%rsp,%rax,4),%xmm0
    +0x1ec9: movdqa  0xa00(%rsp,%rax,4),%xmm1
    +0x1ed2: movdqa  %xmm0,%xmm2
    +0x1ed6: paddd   %xmm5,%xmm2
    +0x1eda: movdqa  %xmm1,%xmm3
    +0x1ede: paddd   %xmm5,%xmm3
    +0x1ee2: psrad   $0x17,%xmm2
    +0x1ee7: psrad   $0x17,%xmm3
    +0x1eec: pshufd  $0xf5,%xmm2,%xmm4
    +0x1ef1: pmuludq %xmm6,%xmm2
    +0x1ef5: pshufd  $0xe8,%xmm2,%xmm2
    +0x1efa: pmuludq %xmm6,%xmm4
    +0x1efe: pshufd  $0xe8,%xmm4,%xmm4
    +0x1f03: punpckldq %xmm4,%xmm2
    +0x1f07: pshufd  $0xf5,%xmm3,%xmm4
    +0x1f0c: pmuludq %xmm6,%xmm3
    +0x1f10: pshufd  $0xe8,%xmm3,%xmm3
    +0x1f15: pmuludq %xmm6,%xmm4
    +0x1f19: pshufd  $0xe8,%xmm4,%xmm4
    +0x1f1e: punpckldq %xmm4,%xmm3
    +0x1f22: paddd   %xmm0,%xmm2
    +0x1f26: paddd   %xmm1,%xmm3
    +0x1f2a: movdqa  %xmm2,0x9f0(%rsp,%rax,4)
    +0x1f33: movdqa  %xmm3,0xa00(%rsp,%rax,4)
    +0x1f3c: add     $0x8,%rax
    +0x1f40: cmp     $0x104,%rax
    +0x1f46: jne     <mldsa87_verify_internal+0x1ec0>
    +0x1f4c: call    <mldsa_poly_invntt_tomont>
    +0x1f51: xor     %eax,%eax
    +0x1f53: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x1f60: movslq  0xa00(%rsp,%rax,4),%rcx
    +0x1f68: lea     0x7fe001(%rcx),%edx
    +0x1f6e: mov     %rcx,%rsi
    +0x1f71: shr     $0x1f,%rsi
    +0x1f75: xor     %ecx,%edx
    +0x1f77: and     %esi,%edx
    +0x1f79: xor     %ecx,%edx
    +0x1f7b: mov     %edx,0xa00(%rsp,%rax,4)
    +0x1f82: inc     %rax
    +0x1f85: cmp     $0x100,%rax
    +0x1f8b: jne     <mldsa87_verify_internal+0x1f60>
    +0x1f8d: test    %r13,%r13
    +0x1f90: mov     0xf8(%rsp),%rax
    +0x1f98: mov     %rbx,0x18(%rsp)
    +0x1f9d: je      <mldsa87_verify_internal+0x1fc0>
    +0x1f9f: movzbl  0x120a(%rax,%r13,1),%r14d
    +0x1fa8: mov     %r13,%rbx
    +0x1fab: movzbl  0x120b(%rax,%r13,1),%r13d
    +0x1fb4: cmp     $0x4b,%r13d
    +0x1fb8: jbe     <mldsa87_verify_internal+0x1fd9>
    +0x1fba: jmp     <mldsa87_verify_internal+0x3ac>
    +0x1fbf: nop     
    +0x1fc0: xor     %r14d,%r14d
    +0x1fc3: mov     %r13,%rbx
    +0x1fc6: movzbl  0x120b(%rax,%r13,1),%r13d
    +0x1fcf: cmp     $0x4b,%r13d
    +0x1fd3: ja      <mldsa87_verify_internal+0x3ac>
    +0x1fd9: cmp     %r13d,%r14d
    +0x1fdc: ja      <mldsa87_verify_internal+0x3ac>
    +0x1fe2: mov     $0x400,%edx
    +0x1fe7: lea     0x600(%rsp),%rdi
    +0x1fef: xor     %esi,%esi
    +0x1ff1: call    <memset>
    +0x1ff6: mov     0xf8(%rsp),%r8
    +0x1ffe: cmp     %r13d,%r14d
    +0x2001: movdqa  0x6a77(%rip),%xmm5
    +0x2009: jae     <mldsa87_verify_internal+0x202e>
    +0x200b: mov     %r14d,%eax
    +0x200e: movzbl  0x11c0(%r8,%rax,1),%ecx
    +0x2017: movl    $0x1,0x600(%rsp,%rcx,4)
    +0x2022: inc     %r14d
    +0x2025: cmp     %r13d,%r14d
    +0x2028: jne     <mldsa87_verify_internal+0x21a0>
    +0x202e: cmp     $0x7,%rbx
    +0x2032: jne     <mldsa87_verify_internal+0x2058>
    +0x2034: cmp     $0x4b,%r13b
    +0x2038: jae     <mldsa87_verify_internal+0x2058>
    +0x203a: mov     %r13d,%eax
    +0x203d: nopl    (%rax)
    +0x2040: cmpb    $0x0,0x11c0(%r8,%rax,1)
    +0x2049: jne     <mldsa87_verify_internal+0x3ac>
    +0x204f: inc     %rax
    +0x2052: cmp     $0x4b,%rax
    +0x2056: jne     <mldsa87_verify_internal+0x2040>
    +0x2058: xor     %eax,%eax
    +0x205a: lea     0x1600(%rsp),%r14
    +0x2062: mov     %rbx,%r13
    +0x2065: mov     0x18(%rsp),%rbx
    +0x206a: jmp     <mldsa87_verify_internal+0x2089>
    +0x206c: nopl    0x0(%rax)
    +0x2070: inc     %ecx
    +0x2072: and     $0xf,%ecx
    +0x2075: mov     %ecx,%esi
    +0x2077: mov     %esi,0xa00(%rsp,%rax,4)
    +0x207e: inc     %rax
    +0x2081: cmp     $0x100,%rax
    +0x2087: je      <mldsa87_verify_internal+0x20e0>
    +0x2089: mov     0xa00(%rsp,%rax,4),%edi
    +0x2090: lea     0x7f(%rdi),%ecx
    +0x2093: sar     $0x7,%ecx
    +0x2096: mov     %ecx,%edx
    +0x2098: shl     $0xa,%ecx
    +0x209b: add     %edx,%ecx
    +0x209d: add     $0x200000,%ecx
    +0x20a3: shr     $0x16,%ecx
    +0x20a6: mov     %ecx,%esi
    +0x20a8: and     $0xf,%esi
    +0x20ab: imul    $0xfff80200,%esi,%edx
    +0x20b1: add     %edi,%edx
    +0x20b3: mov     $0x3ff000,%edi
    +0x20b8: sub     %edx,%edi
    +0x20ba: movslq  %edi,%rdi
    +0x20bd: mov     0x600(%rsp,%rax,4),%r8d
    +0x20c5: shr     $0x1f,%rdi
    +0x20c9: test    %r8d,%r8d
    +0x20cc: je      <mldsa87_verify_internal+0x2077>
    +0x20ce: lea     -0x7fe001(%rdx),%esi
    +0x20d4: xor     %edx,%esi
    +0x20d6: and     %edi,%esi
    +0x20d8: xor     %edx,%esi
    +0x20da: jg      <mldsa87_verify_internal+0x2070>
    +0x20dc: dec     %ecx
    +0x20de: jmp     <mldsa87_verify_internal+0x2072>
    +0x20e0: xor     %eax,%eax
    +0x20e2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x20f0: movaps  0xa00(%rsp,%rax,8),%xmm0
    +0x20f8: movaps  0xa10(%rsp,%rax,8),%xmm1
    +0x2100: movaps  0xa20(%rsp,%rax,8),%xmm2
    +0x2108: movaps  0xa30(%rsp,%rax,8),%xmm3
    +0x2110: movaps  %xmm0,%xmm4
    +0x2113: shufps  $0x88,%xmm1,%xmm4
    +0x2117: shufps  $0xdd,%xmm1,%xmm0
    +0x211b: movaps  %xmm2,%xmm1
    +0x211e: shufps  $0x88,%xmm3,%xmm1
    +0x2122: shufps  $0xdd,%xmm3,%xmm2
    +0x2126: pslld   $0x4,%xmm0
    +0x212b: por     %xmm4,%xmm0
    +0x212f: pslld   $0x4,%xmm2
    +0x2134: por     %xmm1,%xmm2
    +0x2138: pand    %xmm5,%xmm0
    +0x213c: packuswb %xmm0,%xmm0
    +0x2140: packuswb %xmm0,%xmm0
    +0x2144: pand    %xmm5,%xmm2
    +0x2148: packuswb %xmm2,%xmm2
    +0x214c: packuswb %xmm2,%xmm2
    +0x2150: movd    %xmm0,-0x4(%r15,%rax,1)
    +0x2157: movd    %xmm2,(%r15,%rax,1)
    +0x215d: add     $0x8,%rax
    +0x2161: cmp     $0x80,%rax
    +0x2167: jne     <mldsa87_verify_internal+0x20f0>
    +0x2169: inc     %r13
    +0x216c: add     $0x140,%rbx
    +0x2173: sub     $0xffffffffffffff80,%r15
    +0x2177: cmp     $0x8,%r13
    +0x217b: lea     0xa00(%rsp),%rdi
    +0x2183: lea     0x100(%rsp),%rsi
    +0x218b: jne     <mldsa87_verify_internal+0x1732>
    +0x2191: jmp     <mldsa87_verify_internal+0x21e8>
    +0x2193: data16  data16 data16 cs nopw 0x0(%rax,%rax,1)
    +0x21a0: lea     -0x1(%r13),%rcx
    +0x21a4: mov     %rax,%rdx
    +0x21a7: jmp     <mldsa87_verify_internal+0x21c7>
    +0x21a9: nopl    0x0(%rax)
    +0x21b0: movl    $0x1,0x600(%rsp,%rdi,4)
    +0x21bb: mov     %rsi,%rdx
    +0x21be: cmp     %rsi,%rcx
    +0x21c1: je      <mldsa87_verify_internal+0x202e>
    +0x21c7: lea     0x1(%rdx),%rsi
    +0x21cb: movzbl  0x11c1(%r8,%rdx,1),%edi
    +0x21d4: cmp     %rax,%rsi
    +0x21d7: jbe     <mldsa87_verify_internal+0x21b0>
    +0x21d9: cmp     0x11c0(%r8,%rdx,1),%dil
    +0x21e1: ja      <mldsa87_verify_internal+0x21b0>
    +0x21e3: jmp     <mldsa87_verify_internal+0x3ac>
    +0x21e8: pxor    %xmm0,%xmm0
    +0x21ec: movdqu  %xmm0,0xdc(%rsp)
    +0x21f5: movdqa  %xmm0,0xd0(%rsp)
    +0x21fe: movdqa  %xmm0,0xc0(%rsp)
    +0x2207: movdqa  %xmm0,0xb0(%rsp)
    +0x2210: movdqa  %xmm0,0xa0(%rsp)
    +0x2219: movdqa  %xmm0,0x90(%rsp)
    +0x2222: movdqa  %xmm0,0x80(%rsp)
    +0x222b: movdqa  %xmm0,0x70(%rsp)
    +0x2231: movdqa  %xmm0,0x60(%rsp)
    +0x2237: movdqa  %xmm0,0x50(%rsp)
    +0x223d: movdqa  %xmm0,0x40(%rsp)
    +0x2243: movaps  0x580(%rsp),%xmm0
    +0x224b: movaps  0x590(%rsp),%xmm1
    +0x2253: movaps  0x5a0(%rsp),%xmm2
    +0x225b: movaps  0x5b0(%rsp),%xmm3
    +0x2263: movaps  %xmm0,0x20(%rsp)
    +0x2268: movaps  %xmm1,0x30(%rsp)
    +0x226d: movaps  %xmm2,0x40(%rsp)
    +0x2272: movaps  %xmm3,0x50(%rsp)
    +0x2277: movl    $0x40,0xe8(%rsp)
    +0x2282: movaps  0x60(%rsp),%xmm0
    +0x2287: movaps  0x70(%rsp),%xmm1
    +0x228c: movaps  0x80(%rsp),%xmm2
    +0x2294: xorps   0xe00(%rsp),%xmm0
    +0x229c: movaps  0x90(%rsp),%xmm3
    +0x22a4: xorps   0xe10(%rsp),%xmm1
    +0x22ac: movaps  %xmm0,0x60(%rsp)
    +0x22b1: xorps   0xe20(%rsp),%xmm2
    +0x22b9: xorps   0xe30(%rsp),%xmm3
    +0x22c1: movaps  %xmm1,0x70(%rsp)
    +0x22c6: movaps  %xmm2,0x80(%rsp)
    +0x22ce: movaps  %xmm3,0x90(%rsp)
    +0x22d6: mov     0xe40(%rsp),%rax
    +0x22de: xor     %rax,0xa0(%rsp)
    +0x22e6: lea     0xe48(%rsp),%r14
    +0x22ee: lea     0x20(%rsp),%rbx
    +0x22f3: mov     %rbx,%rdi
    +0x22f6: call    <mldsa_keccakf1600_permute>
    +0x22fb: mov     $0x3b8,%r15d
    +0x2301: mov     $0x330,%eax
    +0x2306: cs      nopw 0x0(%rax,%rax,1)
    +0x2310: movups  (%r14),%xmm0
    +0x2314: movups  0x10(%r14),%xmm1
    +0x2319: xorps   0x20(%rsp),%xmm0
    +0x231e: xorps   0x30(%rsp),%xmm1
    +0x2323: movaps  %xmm0,0x20(%rsp)
    +0x2328: movaps  %xmm1,0x30(%rsp)
    +0x232d: movups  0x20(%r14),%xmm0
    +0x2332: movups  0x30(%r14),%xmm1
    +0x2337: xorps   0x40(%rsp),%xmm0
    +0x233c: xorps   0x50(%rsp),%xmm1
    +0x2341: movaps  %xmm0,0x40(%rsp)
    +0x2346: movaps  %xmm1,0x50(%rsp)
    +0x234b: movups  0x40(%r14),%xmm0
    +0x2350: movups  0x50(%r14),%xmm1
    +0x2355: xorps   0x60(%rsp),%xmm0
    +0x235a: xorps   0x70(%rsp),%xmm1
    +0x235f: movaps  %xmm0,0x60(%rsp)
    +0x2364: movaps  %xmm1,0x70(%rsp)
    +0x2369: movups  0x60(%r14),%xmm0
    +0x236e: movups  0x70(%r14),%xmm1
    +0x2373: xorps   0x80(%rsp),%xmm0
    +0x237b: xorps   0x90(%rsp),%xmm1
    +0x2383: movaps  %xmm0,0x80(%rsp)
    +0x238b: movaps  %xmm1,0x90(%rsp)
    +0x2393: mov     0x80(%r14),%rcx
    +0x239a: xor     %rcx,0xa0(%rsp)
    +0x23a2: mov     %r15,%r13
    +0x23a5: mov     %rax,%r12
    +0x23a8: add     $0xffffffffffffff78,%r15
    +0x23af: add     $0x88,%r14
    +0x23b6: mov     %rbx,%rdi
    +0x23b9: call    <mldsa_keccakf1600_permute>
    +0x23be: lea     -0x88(%r12),%rax
    +0x23c6: cmp     $0x10f,%r13
    +0x23cd: jg      <mldsa87_verify_internal+0x2310>
    +0x23d3: test    %r15,%r15
    +0x23d6: je      <mldsa87_verify_internal+0x2461>
    +0x23dc: cmp     $0x20,%r15
    +0x23e0: jae     <mldsa87_verify_internal+0x23e6>
    +0x23e2: xor     %eax,%eax
    +0x23e4: jmp     <mldsa87_verify_internal+0x2437>
    +0x23e6: mov     %r15d,%eax
    +0x23e9: and     $0xe0,%eax
    +0x23ee: mov     %r12d,%ecx
    +0x23f1: and     $0xe0,%ecx
    +0x23f7: xor     %edx,%edx
    +0x23f9: nopl    0x0(%rax)
    +0x2400: movups  (%r14,%rdx,1),%xmm0
    +0x2405: movups  0x10(%r14,%rdx,1),%xmm1
    +0x240b: xorps   0x20(%rsp,%rdx,1),%xmm0
    +0x2410: xorps   0x30(%rsp,%rdx,1),%xmm1
    +0x2415: movaps  %xmm0,0x20(%rsp,%rdx,1)
    +0x241a: movaps  %xmm1,0x30(%rsp,%rdx,1)
    +0x241f: add     $0x20,%rdx
    +0x2423: cmp     %rdx,%rcx
    +0x2426: jne     <mldsa87_verify_internal+0x2400>
    +0x2428: cmp     %rax,%r15
    +0x242b: je      <mldsa87_verify_internal+0x2461>
    +0x242d: test    $0x18,%r15b
    +0x2431: je      <mldsa87_verify_internal+0x2659>
    +0x2437: sub     %rax,%r12
    +0x243a: lea     (%rsp,%rax,1),%rcx
    +0x243e: add     $0x20,%rcx
    +0x2442: add     %rax,%r14
    +0x2445: xor     %eax,%eax
    +0x2447: nopw    0x0(%rax,%rax,1)
    +0x2450: mov     (%r14,%rax,1),%rdx
    +0x2454: xor     %rdx,(%rcx,%rax,1)
    +0x2458: add     $0x8,%rax
    +0x245c: cmp     %rax,%r12
    +0x245f: jne     <mldsa87_verify_internal+0x2450>
    +0x2461: mov     %r15d,0xe8(%rsp)
    +0x2469: xorb    $0x1f,0x20(%rsp,%r15,1)
    +0x246f: xorb    $0x80,0xa7(%rsp)
    +0x2477: movl    $0x88,0xe8(%rsp)
    +0x2482: lea     0x20(%rsp),%rbx
    +0x2487: mov     %rbx,%rdi
    +0x248a: call    <mldsa_keccakf1600_permute>
    +0x248f: movaps  0x20(%rsp),%xmm0
    +0x2494: movaps  0x30(%rsp),%xmm1
    +0x2499: movaps  0x40(%rsp),%xmm2
    +0x249e: movaps  0x50(%rsp),%xmm3
    +0x24a3: movaps  %xmm3,0x5f0(%rsp)
    +0x24ab: movaps  %xmm2,0x5e0(%rsp)
    +0x24b3: movaps  %xmm1,0x5d0(%rsp)
    +0x24bb: movaps  %xmm0,0x5c0(%rsp)
    +0x24c3: xorps   %xmm0,%xmm0
    +0x24c6: movaps  %xmm0,0x60(%rsp)
    +0x24cb: movaps  %xmm0,0x70(%rsp)
    +0x24d0: movaps  %xmm0,0x80(%rsp)
    +0x24d8: movaps  %xmm0,0x90(%rsp)
    +0x24e0: movaps  %xmm0,0xa0(%rsp)
    +0x24e8: movaps  %xmm0,0xb0(%rsp)
    +0x24f0: movaps  %xmm0,0xc0(%rsp)
    +0x24f8: movaps  %xmm0,0xd0(%rsp)
    +0x2500: movaps  %xmm0,0xe0(%rsp)
    +0x2508: movaps  %xmm0,0x20(%rsp)
    +0x250d: movaps  %xmm0,0x30(%rsp)
    +0x2512: movaps  %xmm0,0x40(%rsp)
    +0x2517: movaps  %xmm0,0x50(%rsp)
    +0x251c: movaps  %xmm0,0xe0(%rsp)
    +0x2524: movaps  %xmm0,0xd0(%rsp)
    +0x252c: movaps  %xmm0,0xc0(%rsp)
    +0x2534: movaps  %xmm0,0xb0(%rsp)
    +0x253c: movaps  %xmm0,0xa0(%rsp)
    +0x2544: movaps  %xmm0,0x90(%rsp)
    +0x254c: movaps  %xmm0,0x80(%rsp)
    +0x2554: movaps  %xmm0,0x70(%rsp)
    +0x2559: movaps  %xmm0,0x60(%rsp)
    +0x255e: movaps  %xmm0,0x50(%rsp)
    +0x2563: movaps  %xmm0,0x40(%rsp)
    +0x2568: movaps  %xmm0,0x30(%rsp)
    +0x256d: movaps  %xmm0,0x20(%rsp)
    +0x2572: movdqa  0x5c0(%rsp),%xmm2
    +0x257b: movdqa  0x5d0(%rsp),%xmm1
    +0x2584: movdqa  0x5e0(%rsp),%xmm0
    +0x258d: pxor    0x540(%rsp),%xmm2
    +0x2596: pxor    0x550(%rsp),%xmm1
    +0x259f: pxor    0x560(%rsp),%xmm0
    +0x25a8: movdqa  0x5f0(%rsp),%xmm3
    +0x25b1: pxor    0x570(%rsp),%xmm3
    +0x25ba: movdqa  %xmm0,%xmm4
    +0x25be: por     %xmm2,%xmm4
    +0x25c2: pxor    %xmm2,%xmm0
    +0x25c6: movdqa  %xmm1,%xmm2
    +0x25ca: por     %xmm3,%xmm2
    +0x25ce: por     %xmm4,%xmm2
    +0x25d2: pshufd  $0xee,%xmm2,%xmm4
    +0x25d7: por     %xmm2,%xmm4
    +0x25db: pshufd  $0x55,%xmm4,%xmm2
    +0x25e0: por     %xmm4,%xmm2
    +0x25e4: movdqa  %xmm2,%xmm4
    +0x25e8: psrld   $0x10,%xmm4
    +0x25ed: por     %xmm2,%xmm4
    +0x25f1: movdqa  %xmm4,%xmm2
    +0x25f5: psrlw   $0x8,%xmm2
    +0x25fa: por     %xmm4,%xmm2
    +0x25fe: movd    %xmm2,%eax
    +0x2602: pxor    %xmm1,%xmm3
    +0x2606: pxor    %xmm0,%xmm3
    +0x260a: pshufd  $0xee,%xmm3,%xmm0
    +0x260f: pxor    %xmm3,%xmm0
    +0x2613: pshufd  $0x55,%xmm0,%xmm1
    +0x2618: pxor    %xmm0,%xmm1
    +0x261c: movdqa  %xmm1,%xmm0
    +0x2620: psrld   $0x10,%xmm0
    +0x2625: pxor    %xmm1,%xmm0
    +0x2629: movdqa  %xmm0,%xmm1
    +0x262d: psrlw   $0x8,%xmm1
    +0x2632: pxor    %xmm0,%xmm1
    +0x2636: movd    %xmm1,%ecx
    +0x263a: movzbl  %al,%eax
    +0x263d: neg     %rax
    +0x2640: shr     $0x20,%rax
    +0x2644: xor     %cl,%al
    +0x2646: xor     %edx,%edx
    +0x2648: cmp     %cl,%al
    +0x264a: mov     $0xfffffffa,%r14d
    +0x2650: cmove   %edx,%r14d
    +0x2654: jmp     <mldsa87_verify_internal+0x3b2>
    +0x2659: movzbl  (%r14,%rax,1),%ecx
    +0x265e: xor     %cl,0x20(%rsp,%rax,1)
    +0x2662: inc     %rax
    +0x2665: cmp     %rax,%r15
    +0x2668: jne     <mldsa87_verify_internal+0x2659>
    +0x266a: jmp     <mldsa87_verify_internal+0x2461>
 ***)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa87_verify_internal";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* signature sigb at sig (4627 bytes), the message M of mlen bytes at m and  *)
(* the prefix PRE of prelen bytes at pre (or, if ext is nonzero as a 32-bit  *)
(* integer, mu in the first 64 bytes at m), and the public key pkb at pk     *)
(* (2592 bytes): the result is 0 if the signature is accepted, and -6        *)
(* otherwise. ext, the seventh argument, is on the stack above the return    *)
(* address, and the code reads its low 32 bits. The function aligns the      *)
(* stack pointer down to a multiple of 32, which may lower it by up to 31    *)
(* bytes, saves RBP, the frame pointer, and five more registers, and         *)
(* reserves its buffers, below which the callees use theirs: 14565 bytes of  *)
(* stack below the return address in all (the figure of stackx.py, which     *)
(* counts the red zone that mldsa_keccakf1600_permute writes below RSP). The *)
(* GOT entries of memset and memcpy, which the PLT stubs read, and the       *)
(* region (ea,el) that they may read are apart from the stack.               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 8 7 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 60 64
           (num_of_bytelist(list_of_seq sigb 64)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 14565),14565))
              [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa87_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes32(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mld_verify_internal_ok 8 7 64
                           mld_polyz_unpack_19 640 524168
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60
                           sigb pkb
                           (if ext = (word 0:int32)
                            then mld_verify_mu 2592 pkb prelen PRE mlen M
                            else M MOD 2 EXP 512)
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 14565),14565)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the flag ext, the    *)
(* signature, the message, the prefix and the public key, all public, the    *)
(* addresses of memset and memcpy and the stack, with all accesses within    *)
(* the arguments, the stack, the return address and ext above it, the GOT    *)
(* entries of memset and memcpy, the region (ea,el) that they may read and   *)
(* the constants of the callees, and the writes within the stack.            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 8 7 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 60 64
           (num_of_bytelist(list_of_seq sigb 64)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 14565),14565))
              [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa87_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes32(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mld_verify_internal_ok 8 7 64
                           mld_polyz_unpack_19 640 524168
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60
                           sigb pkb
                           (if ext = (word 0:int32)
                            then mld_verify_mu 2592 pkb prelen PRE mlen M
                            else M MOD 2 EXP 512)
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE
                              mf mc pc (word_sub stackpointer (word 14565))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; pk,2592;
                         word_sub stackpointer (word 14565),14565;
                         stackpointer,8; word_add stackpointer (word 8),4;
                         word(pc + got_memset),8;
                          word(pc + got_memcpy),8; ea,el;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc +
                            mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy_consts),
                          32;
                          word(pc + mldsa87_verify_internal_consts),784]
                        [word_sub stackpointer (word 14565),14565]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 14565),14565)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 8 7 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 60 64
           (num_of_bytelist(list_of_seq sigb 64)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 14565),14565))
              [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa87_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes32(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen pk (ext:int32) sigb pkb M PRE
                              mf mc pc (word_sub stackpointer (word 14565))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; pk,2592;
                         word_sub stackpointer (word 14565),14565;
                         stackpointer,8; word_add stackpointer (word 8),4;
                         word(pc + got_memset),8;
                          word(pc + got_memcpy),8; ea,el;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc +
                            mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy_consts),
                          32;
                          word(pc + mldsa87_verify_internal_consts),784]
                        [word_sub stackpointer (word 14565),14565]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 14565),14565)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
