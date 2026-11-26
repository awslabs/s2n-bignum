(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Product of a row of the matrix with a vector, in the NTT domain, with the *)
(* entries sampled on demand: the statement. This is the code for            *)
(* mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy                      *)
(* (mld_polyvec_matrix_pointwise_montgomery_row_lazy in polyvec_lazy.c) from *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3    *)
(* and MLD_CONFIG_REDUCE_RAM (the monolithic build, see                      *)
(* mldsa_native/README.md). It copies the seed rho from the structure        *)
(* mld_polymat_lazy at mat into a buffer of 64 bytes on the stack, samples   *)
(* entry (i,0) of the matrix into t with mldsa_poly_uniform (with the bytes  *)
(* 0 and i after rho) and multiplies it by polynomial 0 of v, and then for   *)
(* each column j = 1, ..., 3 samples entry (i,j) into the polynomial of the  *)
(* structure, multiplies it by polynomial j of v and adds it to t, and       *)
(* finally reduces t and zeroes the buffer. Clang has inlined the products,  *)
(* the sums (a vector loop, and a scalar loop for the case that t and the    *)
(* polynomial of the structure overlap, which the sums do not take) and the  *)
(* reduction, and the frame is aligned to 32 bytes. It is verified in the    *)
(* whole image (see libmldsa.ml) against mld_polyvec_matrix_row_lazy of      *)
(* common/mldsa_native_lazy.ml, using the theorems for the callee and for    *)
(* the inlined loops, and shown to be constant time and memory safe, with    *)
(* the events depending on rho (from which the matrix is public) and the     *)
(* addresses.                                                                *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_lazy.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy:
       +0x0: push    %rbp
       +0x1: mov     %rsp,%rbp
       +0x4: push    %r15
       +0x6: push    %r14
       +0x8: push    %r13
       +0xa: push    %r12
       +0xc: push    %rbx
       +0xd: and     $0xffffffffffffffe0,%rsp
      +0x11: sub     $0x60,%rsp
      +0x15: mov     %ecx,%r12d
      +0x18: mov     %rdx,%r15
      +0x1b: mov     %rsi,%r14
      +0x1e: mov     %rdi,%rbx
      +0x21: movabs  $0x380200100000000,%r13
      +0x2b: movdqa  0x400(%rsi),%xmm0
      +0x33: movdqa  0x410(%rsi),%xmm1
      +0x3b: movdqa  %xmm1,0x10(%rsp)
      +0x41: movdqa  %xmm0,(%rsp)
      +0x46: movb    $0x0,0x20(%rsp)
      +0x4b: mov     %r12b,0x21(%rsp)
      +0x50: mov     %rsp,%rsi
      +0x53: call    <mldsa_poly_uniform>
      +0x58: mov     $0x1,%eax
      +0x5d: nopl    (%rax)
      +0x60: movslq  -0x4(%rbx,%rax,4),%rcx
      +0x65: movslq  -0x4(%r15,%rax,4),%rdx
      +0x6a: imul    %rcx,%rdx
      +0x6e: mov     %rdx,%rcx
      +0x71: imul    %r13,%rcx
      +0x75: sar     $0x20,%rcx
      +0x79: imul    $0xffffffffff801fff,%rcx,%rcx
      +0x80: add     %rdx,%rcx
      +0x83: shr     $0x20,%rcx
      +0x87: mov     %ecx,-0x4(%rbx,%rax,4)
      +0x8b: movslq  (%rbx,%rax,4),%rcx
      +0x8f: movslq  (%r15,%rax,4),%rdx
      +0x93: imul    %rcx,%rdx
      +0x97: mov     %rdx,%rcx
      +0x9a: imul    %r13,%rcx
      +0x9e: sar     $0x20,%rcx
      +0xa2: imul    $0xffffffffff801fff,%rcx,%rcx
      +0xa9: add     %rdx,%rcx
      +0xac: shr     $0x20,%rcx
      +0xb0: mov     %ecx,(%rbx,%rax,4)
      +0xb3: add     $0x2,%rax
      +0xb7: cmp     $0x101,%rax
      +0xbd: jne     <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x60>
      +0xbf: movb    $0x1,0x20(%rsp)
      +0xc4: mov     %r12b,0x21(%rsp)
      +0xc9: mov     %rsp,%rsi
      +0xcc: mov     %r14,%rdi
      +0xcf: call    <mldsa_poly_uniform>
      +0xd4: xor     %eax,%eax
      +0xd6: cs      nopw 0x0(%rax,%rax,1)
      +0xe0: movslq  (%r14,%rax,4),%rcx
      +0xe4: movslq  0x400(%r15,%rax,4),%rdx
      +0xec: imul    %rcx,%rdx
      +0xf0: mov     %rdx,%rcx
      +0xf3: imul    %r13,%rcx
      +0xf7: sar     $0x20,%rcx
      +0xfb: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x102: add     %rdx,%rcx
     +0x105: shr     $0x20,%rcx
     +0x109: mov     %ecx,(%r14,%rax,4)
     +0x10d: movslq  0x4(%r14,%rax,4),%rcx
     +0x112: movslq  0x404(%r15,%rax,4),%rdx
     +0x11a: imul    %rcx,%rdx
     +0x11e: mov     %rdx,%rcx
     +0x121: imul    %r13,%rcx
     +0x125: sar     $0x20,%rcx
     +0x129: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x130: add     %rdx,%rcx
     +0x133: shr     $0x20,%rcx
     +0x137: mov     %ecx,0x4(%r14,%rax,4)
     +0x13c: add     $0x2,%rax
     +0x140: cmp     $0x100,%rax
     +0x146: jne     <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0xe0>
     +0x148: lea     0x400(%rbx),%rcx
     +0x14f: lea     0x400(%r14),%rax
     +0x156: cmp     %rax,%rbx
     +0x159: setb    %al
     +0x15c: cmp     %rcx,%r14
     +0x15f: setb    %cl
     +0x162: test    %cl,%al
     +0x164: je      <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x1a0>
     +0x166: xor     %eax,%eax
     +0x168: nopl    0x0(%rax,%rax,1)
     +0x170: mov     (%r14,%rax,4),%ecx
     +0x174: add     %ecx,(%rbx,%rax,4)
     +0x177: mov     0x4(%r14,%rax,4),%ecx
     +0x17c: add     %ecx,0x4(%rbx,%rax,4)
     +0x180: mov     0x8(%r14,%rax,4),%ecx
     +0x185: add     %ecx,0x8(%rbx,%rax,4)
     +0x189: mov     0xc(%r14,%rax,4),%ecx
     +0x18e: add     %ecx,0xc(%rbx,%rax,4)
     +0x192: add     $0x4,%rax
     +0x196: cmp     $0x100,%rax
     +0x19c: jne     <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x170>
     +0x19e: jmp     <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x215>
     +0x1a0: xor     %eax,%eax
     +0x1a2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x1b0: movdqu  (%r14,%rax,4),%xmm0
     +0x1b6: movdqu  0x10(%r14,%rax,4),%xmm1
     +0x1bd: movdqu  (%rbx,%rax,4),%xmm2
     +0x1c2: paddd   %xmm0,%xmm2
     +0x1c6: movdqu  0x10(%rbx,%rax,4),%xmm0
     +0x1cc: paddd   %xmm1,%xmm0
     +0x1d0: movdqu  0x20(%rbx,%rax,4),%xmm1
     +0x1d6: movdqu  0x30(%rbx,%rax,4),%xmm3
     +0x1dc: movdqu  %xmm2,(%rbx,%rax,4)
     +0x1e1: movdqu  %xmm0,0x10(%rbx,%rax,4)
     +0x1e7: movdqu  0x20(%r14,%rax,4),%xmm0
     +0x1ee: paddd   %xmm1,%xmm0
     +0x1f2: movdqu  0x30(%r14,%rax,4),%xmm1
     +0x1f9: paddd   %xmm3,%xmm1
     +0x1fd: movdqu  %xmm0,0x20(%rbx,%rax,4)
     +0x203: movdqu  %xmm1,0x30(%rbx,%rax,4)
     +0x209: add     $0x10,%rax
     +0x20d: cmp     $0x100,%rax
     +0x213: jne     <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x1b0>
     +0x215: movb    $0x2,0x20(%rsp)
     +0x21a: mov     %r12b,0x21(%rsp)
     +0x21f: mov     %rsp,%rsi
     +0x222: mov     %r14,%rdi
     +0x225: call    <mldsa_poly_uniform>
     +0x22a: xor     %eax,%eax
     +0x22c: nopl    0x0(%rax)
     +0x230: movslq  (%r14,%rax,4),%rcx
     +0x234: movslq  0x800(%r15,%rax,4),%rdx
     +0x23c: imul    %rcx,%rdx
     +0x240: mov     %rdx,%rcx
     +0x243: imul    %r13,%rcx
     +0x247: sar     $0x20,%rcx
     +0x24b: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x252: add     %rdx,%rcx
     +0x255: shr     $0x20,%rcx
     +0x259: mov     %ecx,(%r14,%rax,4)
     +0x25d: movslq  0x4(%r14,%rax,4),%rcx
     +0x262: movslq  0x804(%r15,%rax,4),%rdx
     +0x26a: imul    %rcx,%rdx
     +0x26e: mov     %rdx,%rcx
     +0x271: imul    %r13,%rcx
     +0x275: sar     $0x20,%rcx
     +0x279: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x280: add     %rdx,%rcx
     +0x283: shr     $0x20,%rcx
     +0x287: mov     %ecx,0x4(%r14,%rax,4)
     +0x28c: add     $0x2,%rax
     +0x290: cmp     $0x100,%rax
     +0x296: jne     <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x230>
     +0x298: lea     0x400(%r14),%rax
     +0x29f: cmp     %rax,%rbx
     +0x2a2: setb    %al
     +0x2a5: lea     0x400(%rbx),%rcx
     +0x2ac: cmp     %rcx,%r14
     +0x2af: setb    %cl
     +0x2b2: test    %cl,%al
     +0x2b4: je      <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x2f0>
     +0x2b6: xor     %eax,%eax
     +0x2b8: nopl    0x0(%rax,%rax,1)
     +0x2c0: mov     (%r14,%rax,4),%ecx
     +0x2c4: add     %ecx,(%rbx,%rax,4)
     +0x2c7: mov     0x4(%r14,%rax,4),%ecx
     +0x2cc: add     %ecx,0x4(%rbx,%rax,4)
     +0x2d0: mov     0x8(%r14,%rax,4),%ecx
     +0x2d5: add     %ecx,0x8(%rbx,%rax,4)
     +0x2d9: mov     0xc(%r14,%rax,4),%ecx
     +0x2de: add     %ecx,0xc(%rbx,%rax,4)
     +0x2e2: add     $0x4,%rax
     +0x2e6: cmp     $0x100,%rax
     +0x2ec: jne     <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x2c0>
     +0x2ee: jmp     <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x365>
     +0x2f0: xor     %eax,%eax
     +0x2f2: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x300: movdqu  (%r14,%rax,4),%xmm0
     +0x306: movdqu  0x10(%r14,%rax,4),%xmm1
     +0x30d: movdqu  (%rbx,%rax,4),%xmm2
     +0x312: paddd   %xmm0,%xmm2
     +0x316: movdqu  0x10(%rbx,%rax,4),%xmm0
     +0x31c: paddd   %xmm1,%xmm0
     +0x320: movdqu  0x20(%rbx,%rax,4),%xmm1
     +0x326: movdqu  0x30(%rbx,%rax,4),%xmm3
     +0x32c: movdqu  %xmm2,(%rbx,%rax,4)
     +0x331: movdqu  %xmm0,0x10(%rbx,%rax,4)
     +0x337: movdqu  0x20(%r14,%rax,4),%xmm0
     +0x33e: paddd   %xmm1,%xmm0
     +0x342: movdqu  0x30(%r14,%rax,4),%xmm1
     +0x349: paddd   %xmm3,%xmm1
     +0x34d: movdqu  %xmm0,0x20(%rbx,%rax,4)
     +0x353: movdqu  %xmm1,0x30(%rbx,%rax,4)
     +0x359: add     $0x10,%rax
     +0x35d: cmp     $0x100,%rax
     +0x363: jne     <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x300>
     +0x365: movb    $0x3,0x20(%rsp)
     +0x36a: mov     %r12b,0x21(%rsp)
     +0x36f: mov     %rsp,%rsi
     +0x372: mov     %r14,%rdi
     +0x375: call    <mldsa_poly_uniform>
     +0x37a: xor     %eax,%eax
     +0x37c: nopl    0x0(%rax)
     +0x380: movslq  (%r14,%rax,4),%rcx
     +0x384: movslq  0xc00(%r15,%rax,4),%rdx
     +0x38c: imul    %rcx,%rdx
     +0x390: mov     %rdx,%rcx
     +0x393: imul    %r13,%rcx
     +0x397: sar     $0x20,%rcx
     +0x39b: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x3a2: add     %rdx,%rcx
     +0x3a5: shr     $0x20,%rcx
     +0x3a9: mov     %ecx,(%r14,%rax,4)
     +0x3ad: movslq  0x4(%r14,%rax,4),%rcx
     +0x3b2: movslq  0xc04(%r15,%rax,4),%rdx
     +0x3ba: imul    %rcx,%rdx
     +0x3be: mov     %rdx,%rcx
     +0x3c1: imul    %r13,%rcx
     +0x3c5: sar     $0x20,%rcx
     +0x3c9: imul    $0xffffffffff801fff,%rcx,%rcx
     +0x3d0: add     %rdx,%rcx
     +0x3d3: shr     $0x20,%rcx
     +0x3d7: mov     %ecx,0x4(%r14,%rax,4)
     +0x3dc: add     $0x2,%rax
     +0x3e0: cmp     $0x100,%rax
     +0x3e6: jne     <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x380>
     +0x3e8: lea     0x400(%r14),%rax
     +0x3ef: cmp     %rax,%rbx
     +0x3f2: setb    %al
     +0x3f5: lea     0x400(%rbx),%rcx
     +0x3fc: cmp     %rcx,%r14
     +0x3ff: setb    %cl
     +0x402: test    %cl,%al
     +0x404: je      <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x440>
     +0x406: xor     %eax,%eax
     +0x408: nopl    0x0(%rax,%rax,1)
     +0x410: mov     (%r14,%rax,4),%ecx
     +0x414: add     %ecx,(%rbx,%rax,4)
     +0x417: mov     0x4(%r14,%rax,4),%ecx
     +0x41c: add     %ecx,0x4(%rbx,%rax,4)
     +0x420: mov     0x8(%r14,%rax,4),%ecx
     +0x425: add     %ecx,0x8(%rbx,%rax,4)
     +0x429: mov     0xc(%r14,%rax,4),%ecx
     +0x42e: add     %ecx,0xc(%rbx,%rax,4)
     +0x432: add     $0x4,%rax
     +0x436: cmp     $0x100,%rax
     +0x43c: jne     <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x410>
     +0x43e: jmp     <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x4b5>
     +0x440: xor     %eax,%eax
     +0x442: data16  data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
     +0x450: movdqu  (%r14,%rax,4),%xmm0
     +0x456: movdqu  0x10(%r14,%rax,4),%xmm1
     +0x45d: movdqu  (%rbx,%rax,4),%xmm2
     +0x462: paddd   %xmm0,%xmm2
     +0x466: movdqu  0x10(%rbx,%rax,4),%xmm0
     +0x46c: paddd   %xmm1,%xmm0
     +0x470: movdqu  0x20(%rbx,%rax,4),%xmm1
     +0x476: movdqu  0x30(%rbx,%rax,4),%xmm3
     +0x47c: movdqu  %xmm2,(%rbx,%rax,4)
     +0x481: movdqu  %xmm0,0x10(%rbx,%rax,4)
     +0x487: movdqu  0x20(%r14,%rax,4),%xmm0
     +0x48e: paddd   %xmm1,%xmm0
     +0x492: movdqu  0x30(%r14,%rax,4),%xmm1
     +0x499: paddd   %xmm3,%xmm1
     +0x49d: movdqu  %xmm0,0x20(%rbx,%rax,4)
     +0x4a3: movdqu  %xmm1,0x30(%rbx,%rax,4)
     +0x4a9: add     $0x10,%rax
     +0x4ad: cmp     $0x100,%rax
     +0x4b3: jne     <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x450>
     +0x4b5: xor     %eax,%eax
     +0x4b7: movdqa  0x1bf81(%rip),%xmm0
     +0x4bf: movdqa  0x1bf89(%rip),%xmm1
     +0x4c7: nopw    0x0(%rax,%rax,1)
     +0x4d0: movdqu  (%rbx,%rax,4),%xmm2
     +0x4d5: movdqu  0x10(%rbx,%rax,4),%xmm3
     +0x4db: movdqa  %xmm2,%xmm4
     +0x4df: paddd   %xmm0,%xmm4
     +0x4e3: movdqa  %xmm3,%xmm5
     +0x4e7: paddd   %xmm0,%xmm5
     +0x4eb: psrad   $0x17,%xmm4
     +0x4f0: psrad   $0x17,%xmm5
     +0x4f5: pshufd  $0xf5,%xmm4,%xmm6
     +0x4fa: pmuludq %xmm1,%xmm4
     +0x4fe: pshufd  $0xe8,%xmm4,%xmm4
     +0x503: pmuludq %xmm1,%xmm6
     +0x507: pshufd  $0xe8,%xmm6,%xmm6
     +0x50c: punpckldq %xmm6,%xmm4
     +0x510: pshufd  $0xf5,%xmm5,%xmm6
     +0x515: pmuludq %xmm1,%xmm5
     +0x519: pshufd  $0xe8,%xmm5,%xmm5
     +0x51e: pmuludq %xmm1,%xmm6
     +0x522: pshufd  $0xe8,%xmm6,%xmm6
     +0x527: punpckldq %xmm6,%xmm5
     +0x52b: paddd   %xmm2,%xmm4
     +0x52f: paddd   %xmm3,%xmm5
     +0x533: movdqu  %xmm4,(%rbx,%rax,4)
     +0x538: movdqu  %xmm5,0x10(%rbx,%rax,4)
     +0x53e: add     $0x8,%rax
     +0x542: cmp     $0x100,%rax
     +0x548: jne     <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x4d0>
     +0x54a: pxor    %xmm0,%xmm0
     +0x54e: movdqa  %xmm0,0x30(%rsp)
     +0x554: movdqa  %xmm0,0x20(%rsp)
     +0x55a: movdqa  %xmm0,0x10(%rsp)
     +0x560: movdqa  %xmm0,(%rsp)
     +0x565: mov     %rsp,%rax
     +0x568: lea     -0x28(%rbp),%rsp
     +0x56c: pop     %rbx
     +0x56d: pop     %r12
     +0x56f: pop     %r13
     +0x571: pop     %r14
     +0x573: pop     %r15
     +0x575: pop     %rbp
     +0x576: xor     %eax,%eax
     +0x578: xor     %ecx,%ecx
     +0x57a: xor     %edi,%edi
     +0x57c: xor     %edx,%edx
     +0x57e: xor     %esi,%esi
     +0x580: ret     
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. Row i of the matrix of 4 rows and 4 columns expanded from    *)
(* the seed rho (32 bytes at mat + 1024, after the polynomial of the         *)
(* structure) times the vector y at v (4 polynomials, in the NTT domain): t  *)
(* becomes mld_polyvec_matrix_row_lazy 4 rho y i, and the polynomial of the  *)
(* structure is overwritten. The sampling of the entries of the matrix must  *)
(* terminate, t and the structure be aligned to 16 bytes (as the SSE loops  *)
(* for the addition and the reduction require) and the direction flag be     *)
(* clear (as for mldsa_poly_uniform). The stack is the 1646 bytes below the return     *)
(* address, including the up to 31 bytes by which the code aligns RSP.       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !t mat v rho y i pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 4 /\ mld_matrix_terminates 4 4 rho /\
        aligned 16 t /\ aligned 16 mat /\
        PAIRWISE nonoverlapping
         [(t,1024); (mat,1024); (word_sub stackpointer (word 1646),1646)] /\
        ALLPAIRS nonoverlapping
         [(t,1024); (mat,1024); (word_sub stackpointer (word 1646),1646)]
         [(word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el); (word_add mat (word 1024),32); (v,4096)] /\
        ALL (nonoverlapping (stackpointer,8)) [(t,1024); (mat,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s =
                  word(pc +
                   mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [t; mat; v; word i] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(word_add mat (word 1024),32)) s =
                  rho /\
                  (!j. j < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * j))))
                             s = y j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!k. k < 256
                       ==> read(memory :> bytes32(word_add t (word(4 * k))))
                             s =
                           mld_polyvec_matrix_row_lazy 4 rho y i k))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(t,1024); memory :> bytes(mat,1024);
                memory :> bytes(word_sub stackpointer (word 1646),1646)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of rho, i and the addresses, with all accesses      *)
(* within the arguments, the stack, the return address and the constants of  *)
(* the callees, and the writes within t, the polynomial of the structure and *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e t mat v rho y i pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 4 /\ mld_matrix_terminates 4 4 rho /\
        aligned 16 t /\ aligned 16 mat /\
        PAIRWISE nonoverlapping
         [(t,1024); (mat,1024); (word_sub stackpointer (word 1646),1646)] /\
        ALLPAIRS nonoverlapping
         [(t,1024); (mat,1024); (word_sub stackpointer (word 1646),1646)]
         [(word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el); (word_add mat (word 1024),32); (v,4096)] /\
        ALL (nonoverlapping (stackpointer,8)) [(t,1024); (mat,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s =
                  word(pc +
                   mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [t; mat; v; word i] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(word_add mat (word 1024),32)) s =
                  rho /\
                  (!j. j < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * j))))
                             s = y j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!k. k < 256
                       ==> read(memory :> bytes32(word_add t (word(4 * k))))
                             s =
                           mld_polyvec_matrix_row_lazy 4 rho y i k) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events t mat v rho i mf mc pc
                                   (word_sub stackpointer (word 1646))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [t,1024; mat,1024; word_add mat (word 1024),32; v,4096;
                       word_sub stackpointer (word 1646),1646; stackpointer,8;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32]
                      [t,1024; mat,1024;
                       word_sub stackpointer (word 1646),1646]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(t,1024); memory :> bytes(mat,1024);
                memory :> bytes(word_sub stackpointer (word 1646),1646)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e t mat v rho i pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 4 /\ mld_matrix_terminates 4 4 rho /\
        aligned 16 t /\ aligned 16 mat /\
        PAIRWISE nonoverlapping
         [(t,1024); (mat,1024); (word_sub stackpointer (word 1646),1646)] /\
        ALLPAIRS nonoverlapping
         [(t,1024); (mat,1024); (word_sub stackpointer (word 1646),1646)]
         [(word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el); (word_add mat (word 1024),32); (v,4096)] /\
        ALL (nonoverlapping (stackpointer,8)) [(t,1024); (mat,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s =
                  word(pc +
                   mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [t; mat; v; word i] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(word_add mat (word 1024),32)) s =
                  rho /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events t mat v rho i mf mc pc
                                   (word_sub stackpointer (word 1646))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [t,1024; mat,1024; word_add mat (word 1024),32; v,4096;
                       word_sub stackpointer (word 1646),1646; stackpointer,8;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32]
                      [t,1024; mat,1024;
                       word_sub stackpointer (word 1646),1646]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(t,1024); memory :> bytes(mat,1024);
                memory :> bytes(word_sub stackpointer (word 1646),1646)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
