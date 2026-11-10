(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing: the statement. This is the code for mldsa87_signature_internal   *)
(* (mld_sign_signature_internal in sign.c, with                              *)
(* mld_attempt_signature_generation and mld_compute_pack_z inlined) from     *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which aligns its stack frame to 32 bytes,        *)
(* unpacks the secret key, computes mu (or takes it from m if ext is         *)
(* nonzero) and rho'', expands the matrix from rho, and makes up to 9361     *)
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
needs "x86/proofs/mldsa_native/gcc12_O2/unpack_sk_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/H_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvec_matrix_expand_eager_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_uniform_gamma1_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvec_matrix_pointwise_montgomery_yvec_eager_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyveck_caddq_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyveck_decompose_pack_w1_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_absorb_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_challenge_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_pointwise_montgomery_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_add_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_sub_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_reduce_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_chknorm_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/pack_sig_z_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/pack_sig_c_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/pack_sig_h_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa87_signature_internal:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  push    QWORD PTR [r10-0x8]
       +0xd  push    rbp
       +0xe  mov     rbp, rsp
      +0x11  push    r15
      +0x13  push    r14
      +0x15  lea     rax, [rbp-0x19430]
      +0x1c  lea     r15, [rbp-0x1a110]
      +0x23  push    r13
      +0x25  lea     r13, [rbp-0x1a0d0]
      +0x2c  push    r12
      +0x2e  mov     r12, rsi
      +0x31  lea     rsi, [rbp-0x14030]
      +0x38  push    r10
      +0x3a  push    rbx
      +0x3b  mov     rbx, r9
      +0x3e  lea     r9, [rbp-0x12030]
      +0x45  sub     rsp, 0x1a1c8
      +0x4c  mov     QWORD PTR [rbp-0x1a1a8], rdi
      +0x53  lea     rdi, [rbp-0x1a130]
      +0x5a  mov     r14d, DWORD PTR [r10+0x8]
      +0x5e  mov     QWORD PTR [rbp-0x1a178], rdx
      +0x65  mov     rdx, r13
      +0x68  mov     QWORD PTR [rbp-0x1a180], rcx
      +0x6f  mov     rcx, rsi
      +0x72  mov     QWORD PTR [rbp-0x1a188], r8
      +0x79  mov     r8, rax
      +0x7c  mov     QWORD PTR [rbp-0x1a1c8], rsi
      +0x83  mov     rsi, r15
      +0x86  mov     QWORD PTR [rbp-0x1a1f0], rdi
      +0x8d  mov     QWORD PTR [rbp-0x1a1b8], r9
      +0x94  mov     QWORD PTR [rbp-0x1a1a0], rax
      +0x9b  push    QWORD PTR [r10]
      +0x9e  call    mldsa87_unpack_sk
     after_mldsa87_unpack_sk:
      +0xa3  pop     rdi
      +0xa4  pop     r8
      +0xa6  test    r14d, r14d
      +0xa9  jne     +0x5ef
      +0xaf  sub     rsp, 0x8
      +0xb3  mov     rsi, r15
      +0xb6  mov     r9, r12
      +0xb9  mov     edx, 0x40
      +0xbe  lea     rax, [rbp-0x1a0b0]
      +0xc5  mov     rcx, QWORD PTR [rbp-0x1a180]
      +0xcc  mov     r8, QWORD PTR [rbp-0x1a188]
      +0xd3  mov     QWORD PTR [rbp-0x1a1d8], rax
      +0xda  mov     rdi, rax
      +0xdd  push    QWORD PTR [rbp-0x1a178]
      +0xe3  call    mld_H87
     after_mld_H87_1:
      +0xe8  pop     rcx
      +0xe9  pop     rsi
     join1:
      +0xea  sub     rsp, 0x8
      +0xee  mov     rcx, rbx
      +0xf1  mov     edx, 0x20
      +0xf6  mov     rsi, r13
      +0xf9  lea     rax, [rbp-0x1a070]
     +0x100  mov     r9, QWORD PTR [rbp-0x1a1d8]
     +0x107  mov     r8d, 0x20
     +0x10d  lea     rbx, [rbp-0x15c30]
     +0x114  mov     QWORD PTR [rbp-0x1a1e8], rax
     +0x11b  mov     rdi, rax
     +0x11e  lea     r15, [rbp-0x19830]
     +0x125  lea     r14, [rbp-0x19c30]
     +0x12c  push    0x40
     +0x12e  mov     r12, r15
     +0x131  call    mld_H87
     after_mld_H87_2:
     +0x136  lea     rax, [rbp-0xe030]
     +0x13d  mov     rsi, QWORD PTR [rbp-0x1a1f0]
     +0x144  mov     rdi, rax
     +0x147  mov     QWORD PTR [rbp-0x1a1e0], rax
     +0x14e  call    mldsa87_polyvec_matrix_expand_eager
     after_mldsa87_polyvec_matrix_expand_eager:
     +0x153  pop     rax
     +0x154  lea     rax, [rbp-0x17830]
     +0x15b  pop     rdx
     +0x15c  mov     QWORD PTR [rbp-0x1a188], rax
     +0x163  lea     rax, [rbp-0x10030]
     +0x16a  mov     QWORD PTR [rbp-0x1a198], rax
     +0x171  lea     rax, [rbp-0x1a030]
     +0x178  mov     QWORD PTR [rbp-0x1a1c0], rax
     +0x17f  lea     rax, [rbp-0x1a170]
     +0x186  mov     DWORD PTR [rbp-0x1a1ac], 0x0
     +0x190  mov     QWORD PTR [rbp-0x1a178], rbx
     +0x197  mov     QWORD PTR [rbp-0x1a1d0], rax
     +0x19e  xchg    ax, ax
     join2:
     +0x1a0  mov     r13, QWORD PTR [rbp-0x1a188]
     +0x1a7  mov     edx, DWORD PTR [rbp-0x1a1ac]
     +0x1ad  mov     rsi, QWORD PTR [rbp-0x1a1e8]
     +0x1b4  mov     rdi, r13
     +0x1b7  call    mldsa87_polyvecl_uniform_gamma1
     after_mldsa87_polyvecl_uniform_gamma1:
     +0x1bc  mov     rdx, r13
     +0x1bf  mov     r13, QWORD PTR [rbp-0x1a198]
     +0x1c6  mov     rcx, QWORD PTR [rbp-0x1a178]
     +0x1cd  mov     rsi, QWORD PTR [rbp-0x1a1e0]
     +0x1d4  mov     rdi, r13
     +0x1d7  call    mldsa87_polyvec_matrix_pointwise_montgomery_yvec_eager
     after_mldsa87_polyvec_matrix_pointwise_montgomery_yvec_eager:
     +0x1dc  mov     rdi, r13
     +0x1df  call    mldsa87_polyveck_caddq
     after_mldsa87_polyveck_caddq:
     +0x1e4  mov     rsi, r13
     +0x1e7  mov     r13, QWORD PTR [rbp-0x1a1c0]
     +0x1ee  mov     rdx, QWORD PTR [rbp-0x1a178]
     +0x1f5  mov     rdi, r13
     +0x1f8  call    mldsa87_polyveck_decompose_pack_w1
     after_mldsa87_polyveck_decompose_pack_w1:
     +0x1fd  mov     rdi, r15
     +0x200  call    mldsa_shake256_init
     after_mldsa_shake256_init:
     +0x205  mov     rsi, QWORD PTR [rbp-0x1a1d8]
     +0x20c  mov     rdi, r15
     +0x20f  mov     edx, 0x40
     +0x214  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_1:
     +0x219  mov     rsi, r13
     +0x21c  mov     edx, 0x400
     +0x221  mov     rdi, r15
     +0x224  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_2:
     +0x229  mov     rdi, r15
     +0x22c  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize:
     +0x231  mov     r13, QWORD PTR [rbp-0x1a1d0]
     +0x238  mov     rdx, r15
     +0x23b  mov     esi, 0x40
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
     +0x266  call    mldsa87_poly_challenge
     after_mldsa87_poly_challenge:
     +0x26b  mov     rdi, r14
     +0x26e  call    mldsa_poly_ntt
     after_mldsa_poly_ntt:
     +0x273  mov     QWORD PTR [rbp-0x1a190], r14
     +0x27a  mov     r14, r13
     +0x27d  nop     DWORD PTR [rax]
     loop1:
     +0x280  mov     rax, QWORD PTR [rbp-0x1a1a0]
     +0x287  mov     r13, r14
     +0x28a  mov     rdi, r15
     +0x28d  mov     ecx, 0x80
     +0x292  shl     r13, 0xa
     +0x296  mov     DWORD PTR [rbp-0x1a180], r14d
     +0x29d  mov     r15, r12
     +0x2a0  lea     rsi, [rax+r13*1]
     +0x2a4  rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
     +0x2a7  mov     rsi, QWORD PTR [rbp-0x1a190]
     +0x2ae  mov     rdi, r12
     +0x2b1  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_1:
     +0x2b6  mov     rdi, r12
     +0x2b9  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_1:
     +0x2be  mov     rax, QWORD PTR [rbp-0x1a188]
     +0x2c5  mov     ecx, 0x80
     +0x2ca  mov     rdi, QWORD PTR [rbp-0x1a178]
     +0x2d1  mov     QWORD PTR [rbp-0x1a178], rbx
     +0x2d8  lea     rsi, [rax+r13*1]
     +0x2dc  rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
     +0x2df  mov     rsi, rbx
     +0x2e2  mov     rdi, r12
     +0x2e5  call    mldsa_poly_add
     after_mldsa_poly_add_1:
     +0x2ea  mov     rdi, r12
     +0x2ed  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_1:
     +0x2f2  mov     esi, 0x7ff88
     +0x2f7  mov     rdi, r12
     +0x2fa  call    mldsa_poly_chknorm
     loop1_test1: after_mldsa_poly_chknorm_1:
     +0x2ff  test    eax, eax
     +0x301  jne     join6
     loop1_next1:
     +0x307  mov     edx, DWORD PTR [rbp-0x1a180]
     +0x30d  mov     rdi, QWORD PTR [rbp-0x1a1a8]
     +0x314  mov     rsi, r12
     +0x317  add     r14, 0x1
     +0x31b  call    mldsa87_pack_sig_z
     loop1_test2: after_mldsa87_pack_sig_z:
     +0x320  cmp     r14, 0x7
     loop1_back:
     +0x324  jne     loop1
     loop1_exit1:
     +0x32a  mov     r14, QWORD PTR [rbp-0x1a190]
     +0x331  mov     QWORD PTR [rbp-0x1a180], r12
     +0x338  xor     r13d, r13d
     +0x33b  mov     QWORD PTR [rbp-0x1a190], r12
     +0x342  nop     WORD PTR [rax+rax*1+0x0]
     loop2:
     +0x348  mov     rax, QWORD PTR [rbp-0x1a1b8]
     +0x34f  mov     ecx, 0x80
     +0x354  mov     rdi, rbx
     +0x357  mov     r12, rbx
     +0x35a  lea     rsi, [rax+r13*1]
     +0x35e  rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
     +0x361  mov     rsi, r14
     +0x364  mov     rdi, rbx
     +0x367  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_2:
     +0x36c  mov     rdi, rbx
     +0x36f  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_2:
     +0x374  mov     rax, QWORD PTR [rbp-0x1a198]
     +0x37b  mov     rsi, rbx
     +0x37e  lea     r15, [rax+r13*1]
     +0x382  mov     rdi, r15
     +0x385  call    mldsa_poly_sub
     after_mldsa_poly_sub:
     +0x38a  mov     rdi, r15
     +0x38d  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_2:
     +0x392  mov     esi, 0x3fe88
     +0x397  mov     rdi, r15
     +0x39a  call    mldsa_poly_chknorm
     loop2_test1: after_mldsa_poly_chknorm_2:
     +0x39f  test    eax, eax
     +0x3a1  jne     join8
     loop2_next1:
     +0x3a7  mov     rax, QWORD PTR [rbp-0x1a1c8]
     +0x3ae  mov     ecx, 0x80
     +0x3b3  mov     rdi, rbx
     +0x3b6  lea     rsi, [rax+r13*1]
     +0x3ba  rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
     +0x3bd  mov     rsi, r14
     +0x3c0  mov     rdi, rbx
     +0x3c3  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_3:
     +0x3c8  mov     rdi, rbx
     +0x3cb  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_3:
     +0x3d0  mov     rdi, rbx
     +0x3d3  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_3:
     +0x3d8  mov     esi, 0x3ff00
     +0x3dd  mov     rdi, rbx
     +0x3e0  call    mldsa_poly_chknorm
     loop2_test2: after_mldsa_poly_chknorm_3:
     +0x3e5  test    eax, eax
     +0x3e7  jne     join8
     loop2_next2:
     +0x3ed  mov     rsi, rbx
     +0x3f0  mov     rdi, r15
     +0x3f3  add     r13, 0x400
     +0x3fa  call    mldsa_poly_add
     loop2_test3: after_mldsa_poly_add_2:
     +0x3ff  cmp     r13, 0x2000
     loop2_back:
     +0x406  jne     loop2
     loop2_exit1:
     +0x40c  mov     r13, QWORD PTR [rbp-0x1a1a8]
     +0x413  mov     rsi, QWORD PTR [rbp-0x1a1d0]
     +0x41a  mov     QWORD PTR [rbp-0x1a178], rbx
     +0x421  mov     r15, QWORD PTR [rbp-0x1a180]
     +0x428  mov     r12, QWORD PTR [rbp-0x1a190]
     +0x42f  mov     rdi, r13
     +0x432  call    mldsa87_pack_sig_c
     after_mldsa87_pack_sig_c:
     +0x437  mov     rdx, QWORD PTR [rbp-0x1a1c0]
     +0x43e  mov     rdi, r13
     +0x441  mov     rcx, rbx
     +0x444  mov     rsi, QWORD PTR [rbp-0x1a198]
     +0x44b  call    mldsa87_pack_sig_h
     after_mldsa87_pack_sig_h:
     +0x450  mov     r13d, eax
     join3:
     +0x453  mov     rdi, r12
     +0x456  xor     eax, eax
     +0x458  mov     ecx, 0x80
     +0x45d  rep stos QWORD PTR es:[rdi], rax
     +0x460  mov     ecx, 0x80
     +0x465  mov     rdi, r14
     +0x468  rep stos QWORD PTR es:[rdi], rax
     +0x46b  mov     rdi, QWORD PTR [rbp-0x1a198]
     +0x472  mov     ecx, 0x400
     +0x477  rep stos QWORD PTR es:[rdi], rax
     +0x47a  mov     rdi, QWORD PTR [rbp-0x1a198]
     +0x481  mov     rdi, QWORD PTR [rbp-0x1a1c0]
     +0x488  mov     ecx, 0x80
     +0x48d  rep stos QWORD PTR es:[rdi], rax
     +0x490  mov     rdi, QWORD PTR [rbp-0x1a1c0]
     +0x497  mov     ecx, 0x380
     +0x49c  mov     rdi, rbx
     +0x49f  rep stos QWORD PTR es:[rdi], rax
     +0x4a2  mov     rdi, QWORD PTR [rbp-0x1a188]
     +0x4a9  mov     ecx, 0x380
     +0x4ae  rep stos QWORD PTR es:[rdi], rax
     +0x4b1  mov     rdi, QWORD PTR [rbp-0x1a188]
     +0x4b8  mov     rax, QWORD PTR [rbp-0x1a1d0]
     +0x4bf  pxor    xmm0, xmm0
     +0x4c3  movaps  XMMWORD PTR [rax], xmm0
     +0x4c6  movaps  XMMWORD PTR [rax+0x10], xmm0
     +0x4ca  movaps  XMMWORD PTR [rax+0x20], xmm0
     +0x4ce  movaps  XMMWORD PTR [rax+0x30], xmm0
     +0x4d2  test    r13d, r13d
     +0x4d5  je      join5
     +0x4d7  cmp     r13d, 0xffffffff
     +0x4db  jne     join4
     +0x4dd  add     DWORD PTR [rbp-0x1a1ac], 0x7
     +0x4e4  mov     eax, DWORD PTR [rbp-0x1a1ac]
     +0x4ea  cmp     eax, 0xfff7
     +0x4ef  jne     join2
     +0x4f5  mov     r13d, 0xfffffffc
     join4:
     +0x4fb  mov     rdx, QWORD PTR [rbp-0x1a1a8]
     +0x502  xor     eax, eax
     +0x504  lea     rdi, [rdx+0x8]
     +0x508  mov     rcx, rdx
     +0x50b  mov     QWORD PTR [rdx], 0x0
     +0x512  mov     QWORD PTR [rdx+0x120b], 0x0
     +0x51d  and     rdi, 0xfffffffffffffff8
     +0x521  sub     rcx, rdi
     +0x524  add     ecx, 0x1213
     +0x52a  shr     ecx, 0x3
     +0x52d  rep stos QWORD PTR es:[rdi], rax
     join5:
     +0x530  mov     rdi, QWORD PTR [rbp-0x1a1b8]
     +0x537  xor     ebx, ebx
     +0x539  mov     ecx, 0x400
     +0x53e  mov     rax, rbx
     +0x541  rep stos QWORD PTR es:[rdi], rax
     +0x544  mov     rdi, QWORD PTR [rbp-0x1a1b8]
     +0x54b  mov     rdi, QWORD PTR [rbp-0x1a1c8]
     +0x552  mov     ecx, 0x400
     +0x557  rep stos QWORD PTR es:[rdi], rax
     +0x55a  mov     rdi, QWORD PTR [rbp-0x1a1c8]
     +0x561  mov     rdi, QWORD PTR [rbp-0x1a1a0]
     +0x568  mov     ecx, 0x380
     +0x56d  rep stos QWORD PTR es:[rdi], rax
     +0x570  mov     rdi, QWORD PTR [rbp-0x1a1a0]
     +0x577  mov     r14, QWORD PTR [rbp-0x1a1e0]
     +0x57e  mov     edx, 0xe000
     +0x583  xor     esi, esi
     +0x585  mov     rdi, r14
     +0x588  call    memset
     after_memset:
     +0x58d  mov     rdi, QWORD PTR [rbp-0x1a1f0]
     +0x594  mov     rax, rbx
     +0x597  mov     ecx, 0x20
     +0x59c  rep stos QWORD PTR es:[rdi], rax
     +0x59f  mov     rdi, QWORD PTR [rbp-0x1a1f0]
     +0x5a6  lea     rsp, [rbp-0x30]
     +0x5aa  mov     eax, r13d
     +0x5ad  pop     rbx
     +0x5ae  pop     r10
     +0x5b0  pop     r12
     +0x5b2  pop     r13
     +0x5b4  pop     r14
     +0x5b6  pop     r15
     +0x5b8  pop     rbp
     +0x5b9  lea     rsp, [r10-0x8]
     ret:
     +0x5bd  ret
     +0x5be  xchg    ax, ax
     join6: loop1_exit2:
     +0x5c0  mov     r14, QWORD PTR [rbp-0x1a190]
     join7:
     +0x5c7  mov     r13d, 0xffffffff
     +0x5cd  jmp     join3
     +0x5d2  nop     WORD PTR [rax+rax*1+0x0]
     join8: loop2_exit2:
     +0x5d8  mov     QWORD PTR [rbp-0x1a178], r12
     +0x5df  mov     r15, QWORD PTR [rbp-0x1a180]
     +0x5e6  mov     r12, QWORD PTR [rbp-0x1a190]
     +0x5ed  jmp     join7
     +0x5ef  movdqu  xmm1, XMMWORD PTR [r12]
     +0x5f5  movdqu  xmm2, XMMWORD PTR [r12+0x10]
     +0x5fc  lea     rax, [rbp-0x1a0b0]
     +0x603  movdqu  xmm3, XMMWORD PTR [r12+0x20]
     +0x60a  movdqu  xmm4, XMMWORD PTR [r12+0x30]
     +0x611  mov     QWORD PTR [rbp-0x1a1d8], rax
     +0x618  movaps  XMMWORD PTR [rbp-0x1a0b0], xmm1
     +0x61f  movaps  XMMWORD PTR [rbp-0x1a0a0], xmm2
     +0x626  movaps  XMMWORD PTR [rbp-0x1a090], xmm3
     +0x62d  movaps  XMMWORD PTR [rbp-0x1a080], xmm4
     +0x634  jmp     join1

    plt_memset:
       +0x0  jmp     QWORD PTR [rip+0xefc2]
                     // got_memset
       +0x6  push    0x2
       +0xb  jmp     <.plt>
 ***)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_signature_internal"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The secret key skb at sk   *)
(* (4896 bytes), the message M of mlen bytes at m and the prefix PRE of      *)
(* prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu in the *)
(* first 64 bytes at m), and the 32 bytes RND at rnd, with MU the mu that    *)
(* the code uses: the result is 0, with the signature mld_sign_sig at sig    *)
(* (4627 bytes), if one of the 9361 attempts succeeds (mld_sign_ok), and -4  *)
(* with the signature zeroed otherwise. The last two arguments, sk and ext,  *)
(* are on the stack above the return address. The function aligns the stack  *)
(* pointer down to a multiple of 32, which may lower it by up to 31 bytes,   *)
(* copies the return address there, saves seven registers (RBP, the frame    *)
(* pointer, and R10, which holds the original stack pointer, among them) and *)
(* reserves 106952 bytes for its buffers, below which the callees use up to  *)
(* 5174 bytes, with their return addresses and stack arguments: 112221 bytes *)
(* of stack below the return address in all. The GOT entry of memset, which  *)
(* the stub reads, and the region (ea,el) that memset may read are apart     *)
(* from the signature and the stack.                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
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
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          mld_sign_terminates_87 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112221),112221)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112221),112221)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_signature_internal) /\
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
                  memory :> bytes(word_sub stackpointer (word 112221),
                                  112221)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, ext, rho, what the C *)
(* code declassifies in each attempt (mld_sign_declass), the address of      *)
(* memset and the stack, with all accesses within the arguments, the stack,  *)
(* the return address and the arguments above it, the GOT entry of memset,   *)
(* the region (ea,el) that memset may read and the constants of the callees, *)
(* and the writes within the signature and the stack.                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
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
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          mld_sign_terminates_87 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112221),112221)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112221),112221)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_signature_internal) /\
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
                             mf pc (word_sub stackpointer (word 112221))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; rnd,32; sk,4896;
                         word_sub stackpointer (word 112221),112221;
                         stackpointer,8; word_add stackpointer (word 8),16;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16]
                        [sig,4627;
                         word_sub stackpointer (word 112221),112221]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112221),
                                  112221)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
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
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          mld_sign_terminates_87 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112221),112221)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112221),112221)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_signature_internal) /\
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
                             mf pc (word_sub stackpointer (word 112221))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; rnd,32; sk,4896;
                         word_sub stackpointer (word 112221),112221;
                         stackpointer,8; word_add stackpointer (word 8),16;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16]
                        [sig,4627;
                         word_sub stackpointer (word 112221),112221]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112221),
                                  112221)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
