(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing: the statement. This is the code for mldsa65_signature_internal   *)
(* (mld_sign_signature_internal in sign.c, with                              *)
(* mld_attempt_signature_generation and mld_compute_pack_z inlined) from     *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which aligns its stack frame to 32 bytes,        *)
(* unpacks the secret key, computes mu (or takes it from m if ext is         *)
(* nonzero) and rho'', expands the matrix from rho, and makes up to 13106    *)
(* attempts: each samples y, computes w = A y, w1 packed, c~ and the         *)
(* challenge, then z, checking and packing each polynomial, and for each row *)
(* checks w0 - c s2 and c t0, and finally packs c~ and the hints, rejecting  *)
(* at the first check that fails. It returns 0 with the signature of the     *)
(* first attempt that succeeds, or -4 (MLD_ERR_SIGN_ATTEMPTS_EXHAUSTED) with *)
(* the signature zeroed, and zeroes its buffers: the matrix with memset,     *)
(* which it calls through the PLT, and the others with memsets that gcc      *)
(* inlines with REP STOSQ, as it inlines the copies of polynomials with REP  *)
(* MOVSQ, so the direction flag must be clear, as the ABI requires on entry. *)
(* It is verified in the whole image (see libmldsa.ml) against mld_sign_ok   *)
(* and mld_sign_sig of common/mldsa_native_sign.ml, using the theorems for   *)
(* the callees and the contract memset_full_contract of                      *)
(* utils/mldsa_native_libc.ml for memset, assuming that the expansion of the *)
(* matrix and the sampling of the challenge in each attempt terminate, and   *)
(* shown to be constant time and memory safe, with the events depending only *)
(* on public values and those that the C code declassifies                   *)
(* (mld_sign_declass).                                                       *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/unpack_sk_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/H_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvec_matrix_expand_eager_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_uniform_gamma1_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvec_matrix_pointwise_montgomery_yvec_eager_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyveck_caddq_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyveck_decompose_pack_w1_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_absorb_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_challenge_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_pointwise_montgomery_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_add_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_sub_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_reduce_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_chknorm_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/pack_sig_z_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/pack_sig_c_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/pack_sig_h_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa65_signature_internal:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  push    QWORD PTR [r10-0x8]
       +0xd  push    rbp
       +0xe  mov     rbp, rsp
      +0x11  push    r15
      +0x13  push    r14
      +0x15  lea     rax, [rbp-0xfc30]
      +0x1c  lea     r14, [rbp-0x107d0]
      +0x23  push    r13
      +0x25  lea     r15, [rbp-0x10810]
      +0x2c  push    r12
      +0x2e  mov     r12, rsi
      +0x31  lea     rsi, [rbp-0x10830]
      +0x38  push    r10
      +0x3a  push    rbx
      +0x3b  mov     rbx, r9
      +0x3e  lea     r9, [rbp-0xa830]
      +0x45  sub     rsp, 0x108c8
      +0x4c  mov     QWORD PTR [rbp-0x10880], rcx
      +0x53  lea     rcx, [rbp-0xc030]
      +0x5a  mov     r13d, DWORD PTR [r10+0x8]
      +0x5e  mov     QWORD PTR [rbp-0x108a0], rdi
      +0x65  mov     rdi, rsi
      +0x68  mov     QWORD PTR [rbp-0x10878], rdx
      +0x6f  mov     rdx, r14
      +0x72  mov     QWORD PTR [rbp-0x10888], r8
      +0x79  mov     r8, rax
      +0x7c  mov     QWORD PTR [rbp-0x108f0], rsi
      +0x83  mov     rsi, r15
      +0x86  mov     QWORD PTR [rbp-0x108c0], r9
      +0x8d  mov     QWORD PTR [rbp-0x108a8], rax
      +0x94  mov     QWORD PTR [rbp-0x108c8], rcx
      +0x9b  push    QWORD PTR [r10]
      +0x9e  call    mldsa65_unpack_sk
     after_mldsa65_unpack_sk:
      +0xa3  pop     rdi
      +0xa4  pop     r8
      +0xa6  test    r13d, r13d
      +0xa9  jne     +0x5e7
      +0xaf  lea     rax, [rbp-0x107b0]
      +0xb6  mov     r9, QWORD PTR [rbp-0x10888]
      +0xbd  mov     ecx, 0x40
      +0xc2  mov     rdx, r15
      +0xc5  mov     QWORD PTR [rbp-0x108e0], rax
      +0xcc  mov     r8, QWORD PTR [rbp-0x10880]
      +0xd3  mov     esi, 0x40
      +0xd8  mov     rdi, rax
      +0xdb  push    QWORD PTR [rbp-0x10878]
      +0xe1  push    r12
      +0xe3  call    mld_H65
     after_mld_H65_1:
      +0xe8  pop     rcx
      +0xe9  pop     rsi
     join1:
      +0xea  mov     rdx, r14
      +0xed  mov     r8, rbx
      +0xf0  mov     ecx, 0x20
      +0xf5  mov     esi, 0x40
      +0xfa  lea     rax, [rbp-0x10770]
     +0x101  mov     r9d, 0x20
     +0x107  lea     rbx, [rbp-0xd430]
     +0x10e  mov     QWORD PTR [rbp-0x108e8], rax
     +0x115  mov     rdi, rax
     +0x118  lea     r15, [rbp-0x10030]
     +0x11f  lea     r14, [rbp-0x10430]
     +0x126  push    0x40
     +0x128  mov     r12, r15
     +0x12b  push    QWORD PTR [rbp-0x108e0]
     +0x131  call    mld_H65
     after_mld_H65_2:
     +0x136  lea     rax, [rbp-0x7830]
     +0x13d  mov     rsi, QWORD PTR [rbp-0x108f0]
     +0x144  mov     rdi, rax
     +0x147  mov     QWORD PTR [rbp-0x108d8], rax
     +0x14e  call    mldsa65_polyvec_matrix_expand_eager
     after_mldsa65_polyvec_matrix_expand_eager:
     +0x153  pop     rax
     +0x154  lea     rax, [rbp-0xe830]
     +0x15b  pop     rdx
     +0x15c  mov     QWORD PTR [rbp-0x10888], rax
     +0x163  lea     rax, [rbp-0x9030]
     +0x16a  mov     QWORD PTR [rbp-0x10890], rax
     +0x171  lea     rax, [rbp-0x10730]
     +0x178  mov     QWORD PTR [rbp-0x108b8], rax
     +0x17f  lea     rax, [rbp-0x10870]
     +0x186  mov     DWORD PTR [rbp-0x108ac], 0x0
     +0x190  mov     QWORD PTR [rbp-0x10878], rbx
     +0x197  mov     QWORD PTR [rbp-0x108d0], rax
     +0x19e  xchg    ax, ax
     join2:
     +0x1a0  mov     r13, QWORD PTR [rbp-0x10888]
     +0x1a7  mov     edx, DWORD PTR [rbp-0x108ac]
     +0x1ad  mov     rsi, QWORD PTR [rbp-0x108e8]
     +0x1b4  mov     rdi, r13
     +0x1b7  call    mldsa65_polyvecl_uniform_gamma1
     after_mldsa65_polyvecl_uniform_gamma1:
     +0x1bc  mov     rdx, r13
     +0x1bf  mov     r13, QWORD PTR [rbp-0x10890]
     +0x1c6  mov     rcx, QWORD PTR [rbp-0x10878]
     +0x1cd  mov     rsi, QWORD PTR [rbp-0x108d8]
     +0x1d4  mov     rdi, r13
     +0x1d7  call    mldsa65_polyvec_matrix_pointwise_montgomery_yvec_eager
     after_mldsa65_polyvec_matrix_pointwise_montgomery_yvec_eager:
     +0x1dc  mov     rdi, r13
     +0x1df  call    mldsa65_polyveck_caddq
     after_mldsa65_polyveck_caddq:
     +0x1e4  mov     rsi, r13
     +0x1e7  mov     r13, QWORD PTR [rbp-0x108b8]
     +0x1ee  mov     rdx, QWORD PTR [rbp-0x10878]
     +0x1f5  mov     rdi, r13
     +0x1f8  call    mldsa65_polyveck_decompose_pack_w1
     after_mldsa65_polyveck_decompose_pack_w1:
     +0x1fd  mov     rdi, r15
     +0x200  call    mldsa_shake256_init
     after_mldsa_shake256_init:
     +0x205  mov     rsi, QWORD PTR [rbp-0x108e0]
     +0x20c  mov     rdi, r15
     +0x20f  mov     edx, 0x40
     +0x214  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_1:
     +0x219  mov     rsi, r13
     +0x21c  mov     edx, 0x300
     +0x221  mov     rdi, r15
     +0x224  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_2:
     +0x229  mov     rdi, r15
     +0x22c  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize:
     +0x231  mov     r13, QWORD PTR [rbp-0x108d0]
     +0x238  mov     rdx, r15
     +0x23b  mov     esi, 0x30
     +0x240  mov     rdi, r13
     +0x243  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze:
     +0x248  mov     rdi, r15
     +0x24b  call    mldsa_shake256_release
     after_mldsa_shake256_release:
     +0x250  mov     rdi, r15
     +0x253  xor     eax, eax
     +0x255  mov     ecx, 0x1a
     +0x25a  rep stos QWORD PTR es:[rdi], rax
     +0x25d  mov     rsi, r13
     +0x260  mov     rdi, r14
     +0x263  xor     r13d, r13d
     +0x266  call    mldsa65_poly_challenge
     after_mldsa65_poly_challenge:
     +0x26b  mov     rdi, r14
     +0x26e  call    mldsa_poly_ntt
     after_mldsa_poly_ntt:
     +0x273  mov     QWORD PTR [rbp-0x10898], r14
     +0x27a  mov     r14, r13
     loop1:
     +0x27d  mov     rax, QWORD PTR [rbp-0x108a8]
     +0x284  mov     r13, r14
     +0x287  mov     rdi, r15
     +0x28a  mov     ecx, 0x80
     +0x28f  shl     r13, 0xa
     +0x293  mov     DWORD PTR [rbp-0x10880], r14d
     +0x29a  mov     r15, r12
     +0x29d  lea     rsi, [rax+r13*1]
     +0x2a1  rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
     +0x2a4  mov     rsi, QWORD PTR [rbp-0x10898]
     +0x2ab  mov     rdi, r12
     +0x2ae  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_1:
     +0x2b3  mov     rdi, r12
     +0x2b6  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_1:
     +0x2bb  mov     rax, QWORD PTR [rbp-0x10888]
     +0x2c2  mov     ecx, 0x80
     +0x2c7  mov     rdi, QWORD PTR [rbp-0x10878]
     +0x2ce  mov     QWORD PTR [rbp-0x10878], rbx
     +0x2d5  lea     rsi, [rax+r13*1]
     +0x2d9  rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
     +0x2dc  mov     rsi, rbx
     +0x2df  mov     rdi, r12
     +0x2e2  call    mldsa_poly_add
     after_mldsa_poly_add_1:
     +0x2e7  mov     rdi, r12
     +0x2ea  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_1:
     +0x2ef  mov     esi, 0x7ff3c
     +0x2f4  mov     rdi, r12
     +0x2f7  call    mldsa_poly_chknorm
     loop1_test1: after_mldsa_poly_chknorm_1:
     +0x2fc  test    eax, eax
     +0x2fe  jne     join6
     loop1_next1:
     +0x304  mov     edx, DWORD PTR [rbp-0x10880]
     +0x30a  mov     rdi, QWORD PTR [rbp-0x108a0]
     +0x311  mov     rsi, r12
     +0x314  add     r14, 0x1
     +0x318  call    mldsa65_pack_sig_z
     loop1_test2: after_mldsa65_pack_sig_z:
     +0x31d  cmp     r14, 0x5
     loop1_back:
     +0x321  jne     loop1
     loop1_exit1:
     +0x327  mov     QWORD PTR [rbp-0x10878], r12
     +0x32e  mov     r14, QWORD PTR [rbp-0x10898]
     +0x335  xor     r13d, r13d
     +0x338  mov     QWORD PTR [rbp-0x10880], r12
     loop2:
     +0x33f  mov     rax, QWORD PTR [rbp-0x108c0]
     +0x346  mov     ecx, 0x80
     +0x34b  mov     rdi, rbx
     +0x34e  mov     r12, rbx
     +0x351  lea     rsi, [rax+r13*1]
     +0x355  rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
     +0x358  mov     rsi, r14
     +0x35b  mov     rdi, rbx
     +0x35e  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_2:
     +0x363  mov     rdi, rbx
     +0x366  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_2:
     +0x36b  mov     rax, QWORD PTR [rbp-0x10890]
     +0x372  mov     rsi, rbx
     +0x375  lea     r15, [rax+r13*1]
     +0x379  mov     rdi, r15
     +0x37c  call    mldsa_poly_sub
     after_mldsa_poly_sub:
     +0x381  mov     rdi, r15
     +0x384  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_2:
     +0x389  mov     esi, 0x3fe3c
     +0x38e  mov     rdi, r15
     +0x391  call    mldsa_poly_chknorm
     loop2_test1: after_mldsa_poly_chknorm_2:
     +0x396  test    eax, eax
     +0x398  jne     join8
     loop2_next1:
     +0x39e  mov     rax, QWORD PTR [rbp-0x108c8]
     +0x3a5  mov     ecx, 0x80
     +0x3aa  mov     rdi, rbx
     +0x3ad  lea     rsi, [rax+r13*1]
     +0x3b1  rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
     +0x3b4  mov     rsi, r14
     +0x3b7  mov     rdi, rbx
     +0x3ba  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_3:
     +0x3bf  mov     rdi, rbx
     +0x3c2  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_3:
     +0x3c7  mov     rdi, rbx
     +0x3ca  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_3:
     +0x3cf  mov     esi, 0x3ff00
     +0x3d4  mov     rdi, rbx
     +0x3d7  call    mldsa_poly_chknorm
     loop2_test2: after_mldsa_poly_chknorm_3:
     +0x3dc  test    eax, eax
     +0x3de  jne     join8
     loop2_next2:
     +0x3e4  mov     rsi, rbx
     +0x3e7  mov     rdi, r15
     +0x3ea  add     r13, 0x400
     +0x3f1  call    mldsa_poly_add
     loop2_test3: after_mldsa_poly_add_2:
     +0x3f6  cmp     r13, 0x1800
     loop2_back:
     +0x3fd  jne     loop2
     loop2_exit1:
     +0x403  mov     r13, QWORD PTR [rbp-0x108a0]
     +0x40a  mov     rsi, QWORD PTR [rbp-0x108d0]
     +0x411  mov     r15, QWORD PTR [rbp-0x10878]
     +0x418  mov     r12, QWORD PTR [rbp-0x10880]
     +0x41f  mov     QWORD PTR [rbp-0x10878], rbx
     +0x426  mov     rdi, r13
     +0x429  call    mldsa65_pack_sig_c
     after_mldsa65_pack_sig_c:
     +0x42e  mov     rdx, QWORD PTR [rbp-0x108b8]
     +0x435  mov     rdi, r13
     +0x438  mov     rcx, rbx
     +0x43b  mov     rsi, QWORD PTR [rbp-0x10890]
     +0x442  call    mldsa65_pack_sig_h
     after_mldsa65_pack_sig_h:
     +0x447  mov     r13d, eax
     join3:
     +0x44a  mov     rdi, r12
     +0x44d  xor     eax, eax
     +0x44f  mov     ecx, 0x80
     +0x454  rep stos QWORD PTR es:[rdi], rax
     +0x457  mov     ecx, 0x80
     +0x45c  mov     rdi, r14
     +0x45f  rep stos QWORD PTR es:[rdi], rax
     +0x462  mov     rdi, QWORD PTR [rbp-0x10890]
     +0x469  mov     ecx, 0x300
     +0x46e  rep stos QWORD PTR es:[rdi], rax
     +0x471  mov     rdi, QWORD PTR [rbp-0x10890]
     +0x478  mov     rdi, QWORD PTR [rbp-0x108b8]
     +0x47f  mov     ecx, 0x60
     +0x484  rep stos QWORD PTR es:[rdi], rax
     +0x487  mov     rdi, QWORD PTR [rbp-0x108b8]
     +0x48e  mov     ecx, 0x280
     +0x493  mov     rdi, rbx
     +0x496  rep stos QWORD PTR es:[rdi], rax
     +0x499  mov     rdi, QWORD PTR [rbp-0x10888]
     +0x4a0  mov     ecx, 0x280
     +0x4a5  rep stos QWORD PTR es:[rdi], rax
     +0x4a8  mov     rdi, QWORD PTR [rbp-0x10888]
     +0x4af  mov     rax, QWORD PTR [rbp-0x108d0]
     +0x4b6  pxor    xmm0, xmm0
     +0x4ba  movaps  XMMWORD PTR [rax], xmm0
     +0x4bd  movaps  XMMWORD PTR [rax+0x10], xmm0
     +0x4c1  movaps  XMMWORD PTR [rax+0x20], xmm0
     +0x4c5  test    r13d, r13d
     +0x4c8  je      join5
     +0x4ca  cmp     r13d, 0xffffffff
     +0x4ce  jne     join4
     +0x4d0  add     DWORD PTR [rbp-0x108ac], 0x5
     +0x4d7  mov     eax, DWORD PTR [rbp-0x108ac]
     +0x4dd  cmp     eax, 0xfffa
     +0x4e2  jne     join2
     +0x4e8  mov     r13d, 0xfffffffc
     join4:
     +0x4ee  mov     rdx, QWORD PTR [rbp-0x108a0]
     +0x4f5  xor     eax, eax
     +0x4f7  lea     rdi, [rdx+0x8]
     +0x4fb  mov     rcx, rdx
     +0x4fe  mov     QWORD PTR [rdx], 0x0
     +0x505  mov     QWORD PTR [rdx+0xce5], 0x0
     +0x510  and     rdi, 0xfffffffffffffff8
     +0x514  sub     rcx, rdi
     +0x517  add     ecx, 0xced
     +0x51d  shr     ecx, 0x3
     +0x520  rep stos QWORD PTR es:[rdi], rax
     join5:
     +0x523  mov     rdi, QWORD PTR [rbp-0x108c0]
     +0x52a  xor     ebx, ebx
     +0x52c  mov     ecx, 0x300
     +0x531  mov     rax, rbx
     +0x534  rep stos QWORD PTR es:[rdi], rax
     +0x537  mov     rdi, QWORD PTR [rbp-0x108c0]
     +0x53e  mov     rdi, QWORD PTR [rbp-0x108c8]
     +0x545  mov     ecx, 0x300
     +0x54a  rep stos QWORD PTR es:[rdi], rax
     +0x54d  mov     rdi, QWORD PTR [rbp-0x108c8]
     +0x554  mov     rdi, QWORD PTR [rbp-0x108a8]
     +0x55b  mov     ecx, 0x280
     +0x560  rep stos QWORD PTR es:[rdi], rax
     +0x563  mov     rdi, QWORD PTR [rbp-0x108a8]
     +0x56a  mov     r14, QWORD PTR [rbp-0x108d8]
     +0x571  mov     edx, 0x7800
     +0x576  xor     esi, esi
     +0x578  mov     rdi, r14
     +0x57b  call    memset
     after_memset:
     +0x580  mov     rdi, QWORD PTR [rbp-0x108f0]
     +0x587  mov     rax, rbx
     +0x58a  mov     ecx, 0x20
     +0x58f  rep stos QWORD PTR es:[rdi], rax
     +0x592  mov     rdi, QWORD PTR [rbp-0x108f0]
     +0x599  lea     rsp, [rbp-0x30]
     +0x59d  mov     eax, r13d
     +0x5a0  pop     rbx
     +0x5a1  pop     r10
     +0x5a3  pop     r12
     +0x5a5  pop     r13
     +0x5a7  pop     r14
     +0x5a9  pop     r15
     +0x5ab  pop     rbp
     +0x5ac  lea     rsp, [r10-0x8]
     ret:
     +0x5b0  ret
     +0x5b1  nop     DWORD PTR [rax+0x0]
     join6: loop1_exit2:
     +0x5b8  mov     r14, QWORD PTR [rbp-0x10898]
     join7:
     +0x5bf  mov     r13d, 0xffffffff
     +0x5c5  jmp     join3
     +0x5ca  nop     WORD PTR [rax+rax*1+0x0]
     join8: loop2_exit2:
     +0x5d0  mov     r15, QWORD PTR [rbp-0x10878]
     +0x5d7  mov     QWORD PTR [rbp-0x10878], r12
     +0x5de  mov     r12, QWORD PTR [rbp-0x10880]
     +0x5e5  jmp     join7
     +0x5e7  movdqu  xmm1, XMMWORD PTR [r12]
     +0x5ed  movdqu  xmm2, XMMWORD PTR [r12+0x10]
     +0x5f4  lea     rax, [rbp-0x107b0]
     +0x5fb  movdqu  xmm3, XMMWORD PTR [r12+0x20]
     +0x602  movdqu  xmm4, XMMWORD PTR [r12+0x30]
     +0x609  mov     QWORD PTR [rbp-0x108e0], rax
     +0x610  movaps  XMMWORD PTR [rbp-0x107b0], xmm1
     +0x617  movaps  XMMWORD PTR [rbp-0x107a0], xmm2
     +0x61e  movaps  XMMWORD PTR [rbp-0x10790], xmm3
     +0x625  movaps  XMMWORD PTR [rbp-0x10780], xmm4
     +0x62c  jmp     join1

    plt_memset:
       +0x0  jmp     QWORD PTR [rip+0xefc2]
                     // got_memset
       +0x6  push    0x2
       +0xb  jmp     <.plt>
 ***)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_signature_internal"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The secret key skb at sk   *)
(* (4032 bytes), the message M of mlen bytes at m and the prefix PRE of      *)
(* prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu in the *)
(* first 64 bytes at m), and the 32 bytes RND at rnd, with MU the mu that    *)
(* the code uses: the result is 0, with the signature mld_sign_sig at sig    *)
(* (3309 bytes), if one of the 13106 attempts succeeds (mld_sign_ok), and -4 *)
(* with the signature zeroed otherwise. The last two arguments, sk and ext,  *)
(* are on the stack above the return address. The function aligns the stack  *)
(* pointer down to a multiple of 32, which may lower it by up to 31 bytes,   *)
(* copies the return address there, saves seven registers (RBP, the frame    *)
(* pointer, and R10, which holds the original stack pointer, among them) and *)
(* reserves 67784 bytes for its buffers, below which the callees use up to   *)
(* 5182 bytes, with their return addresses and stack arguments: 73061 bytes  *)
(* of stack below the return address in all. The GOT entry of memset, which  *)
(* the stub reads, and the region (ea,el) that memset may read are apart     *)
(* from the signature and the stack.                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !sig m mlen pre prelen rnd sk ext skb M PRE RND MU
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          MU = (if word_zx ext = (word 0:int32)
                then mld_sign_mu (\j. skb(64 + j)) prelen PRE mlen M
                else M MOD 2 EXP 512) /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          mld_sign_terminates_65 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73061),73061)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73061),73061)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)] /\
          nonoverlapping (sig,3309) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa65_signature_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; rnd] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8)))
                         s = sk /\
                    read (memory :> bytes64(word_add stackpointer (word 16)))
                         s = ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
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
                  memory :> bytes(word_sub stackpointer (word 73061),73061)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, ext, rho, what the C *)
(* code declassifies in each attempt (mld_sign_declass), the address of      *)
(* memset and the stack, with all accesses within the arguments, the stack,  *)
(* the return address and the arguments above it, the GOT entry of memset,   *)
(* the region (ea,el) that memset may read and the constants of the callees, *)
(* and the writes within the signature and the stack.                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen rnd sk ext skb M PRE RND MU
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          MU = (if word_zx ext = (word 0:int32)
                then mld_sign_mu (\j. skb(64 + j)) prelen PRE mlen M
                else M MOD 2 EXP 512) /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          mld_sign_terminates_65 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73061),73061)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73061),73061)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)] /\
          nonoverlapping (sig,3309) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa65_signature_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; rnd] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8)))
                         s = sk /\
                    read (memory :> bytes64(word_add stackpointer (word 16)))
                         s = ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
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
                             mf pc (word_sub stackpointer (word 73061))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; rnd,32; sk,4032;
                         word_sub stackpointer (word 73061),73061;
                         stackpointer,8; word_add stackpointer (word 8),16;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa65_polyvec_matrix_expand_eager_consts),
                         4]
                        [sig,3309;
                         word_sub stackpointer (word 73061),73061]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 73061),73061)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen rnd sk ext skb M PRE RND MU
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          MU = (if word_zx ext = (word 0:int32)
                then mld_sign_mu (\j. skb(64 + j)) prelen PRE mlen M
                else M MOD 2 EXP 512) /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          mld_sign_terminates_65 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73061),73061)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73061),73061)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)] /\
          nonoverlapping (sig,3309) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa65_signature_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; rnd] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8)))
                         s = sk /\
                    read (memory :> bytes64(word_add stackpointer (word 16)))
                         s = ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
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
                             mf pc (word_sub stackpointer (word 73061))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; rnd,32; sk,4032;
                         word_sub stackpointer (word 73061),73061;
                         stackpointer,8; word_add stackpointer (word 8),16;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa65_polyvec_matrix_expand_eager_consts),
                         4]
                        [sig,3309;
                         word_sub stackpointer (word 73061),73061]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 73061),73061)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
