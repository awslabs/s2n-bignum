(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing: the statement. This is the code for mldsa44_signature_internal   *)
(* (mld_sign_signature_internal in sign.c, with                              *)
(* mld_attempt_signature_generation and mld_compute_pack_z inlined) from     *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which aligns its stack frame to 32 bytes,        *)
(* unpacks the secret key, computes mu (or takes it from m if ext is         *)
(* nonzero) and rho'', expands the matrix from rho, and makes up to 16382    *)
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
needs "x86/proofs/mldsa_native/gcc12_O2/unpack_sk_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/H_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvec_matrix_expand_eager_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_uniform_gamma1_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvec_matrix_pointwise_montgomery_yvec_eager_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyveck_caddq_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyveck_decompose_pack_w1_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_absorb_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_challenge_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_pointwise_montgomery_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_add_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_sub_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_reduce_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_chknorm_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/pack_sig_z_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/pack_sig_c_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/pack_sig_h_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa44_signature_internal:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  push    QWORD PTR [r10-0x8]
       +0xd  push    rbp
       +0xe  mov     rbp, rsp
      +0x11  push    r15
      +0x13  push    r14
      +0x15  lea     rax, [rbp-0xa030]
      +0x1c  lea     r15, [rbp-0xabd0]
      +0x23  push    r13
      +0x25  lea     r13, [rbp-0xac10]
      +0x2c  push    r12
      +0x2e  mov     r12, rsi
      +0x31  lea     rsi, [rbp-0xac30]
      +0x38  push    r10
      +0x3a  push    rbx
      +0x3b  mov     rbx, r9
      +0x3e  lea     r9, [rbp-0x8030]
      +0x45  sub     rsp, 0xacc8
      +0x4c  mov     QWORD PTR [rbp-0xac60], rcx
      +0x53  lea     rcx, [rbp-0x9030]
      +0x5a  mov     r14d, DWORD PTR [r10+0x8]
      +0x5e  mov     QWORD PTR [rbp-0xac88], rdi
      +0x65  mov     rdi, rsi
      +0x68  mov     QWORD PTR [rbp-0xac58], rdx
      +0x6f  mov     rdx, r15
      +0x72  mov     QWORD PTR [rbp-0xac68], r8
      +0x79  mov     r8, rax
      +0x7c  mov     QWORD PTR [rbp-0xacd8], rsi
      +0x83  mov     rsi, r13
      +0x86  mov     QWORD PTR [rbp-0xaca8], r9
      +0x8d  mov     QWORD PTR [rbp-0xac98], rax
      +0x94  mov     QWORD PTR [rbp-0xacb0], rcx
      +0x9b  push    QWORD PTR [r10]
      +0x9e  call    mldsa44_unpack_sk
     after_mldsa44_unpack_sk:
      +0xa3  pop     rdi
      +0xa4  pop     r8
      +0xa6  test    r14d, r14d
      +0xa9  jne     +0x5e0
      +0xaf  lea     rax, [rbp-0xabb0]
      +0xb6  mov     r9, QWORD PTR [rbp-0xac68]
      +0xbd  mov     ecx, 0x40
      +0xc2  mov     rdx, r13
      +0xc5  mov     QWORD PTR [rbp-0xacc0], rax
      +0xcc  mov     r8, QWORD PTR [rbp-0xac60]
      +0xd3  mov     esi, 0x40
      +0xd8  mov     rdi, rax
      +0xdb  push    QWORD PTR [rbp-0xac58]
      +0xe1  push    r12
      +0xe3  call    mld_H44
     after_mld_H44_1:
      +0xe8  pop     rcx
      +0xe9  pop     rsi
     join1:
      +0xea  mov     rdx, r15
      +0xed  mov     r8, rbx
      +0xf0  mov     ecx, 0x20
      +0xf5  mov     esi, 0x40
      +0xfa  lea     rax, [rbp-0xab70]
     +0x101  mov     r9d, 0x20
     +0x107  lea     rbx, [rbp-0x6030]
     +0x10e  mov     QWORD PTR [rbp-0xacd0], rax
     +0x115  mov     rdi, rax
     +0x118  lea     r14, [rbp-0xa830]
     +0x11f  lea     r15, [rbp-0xa430]
     +0x126  push    0x40
     +0x128  mov     r12, r15
     +0x12b  push    QWORD PTR [rbp-0xacc0]
     +0x131  call    mld_H44
     after_mld_H44_2:
     +0x136  lea     rax, [rbp-0x4030]
     +0x13d  mov     rsi, QWORD PTR [rbp-0xacd8]
     +0x144  mov     rdi, rax
     +0x147  mov     QWORD PTR [rbp-0xacc8], rax
     +0x14e  call    mldsa44_polyvec_matrix_expand_eager
     after_mldsa44_polyvec_matrix_expand_eager:
     +0x153  pop     rax
     +0x154  lea     rax, [rbp-0x7030]
     +0x15b  pop     rdx
     +0x15c  mov     QWORD PTR [rbp-0xac70], rax
     +0x163  lea     rax, [rbp-0x5030]
     +0x16a  mov     QWORD PTR [rbp-0xac78], rax
     +0x171  lea     rax, [rbp-0xab30]
     +0x178  mov     QWORD PTR [rbp-0xac90], rax
     +0x17f  lea     rax, [rbp-0xac50]
     +0x186  mov     DWORD PTR [rbp-0xac7c], 0x0
     +0x190  mov     QWORD PTR [rbp-0xac58], rbx
     +0x197  mov     QWORD PTR [rbp-0xaca0], rax
     +0x19e  mov     QWORD PTR [rbp-0xac60], r14
     +0x1a5  nop     DWORD PTR [rax]
     join2:
     +0x1a8  mov     r14, QWORD PTR [rbp-0xac70]
     +0x1af  mov     edx, DWORD PTR [rbp-0xac7c]
     +0x1b5  mov     rsi, QWORD PTR [rbp-0xacd0]
     +0x1bc  mov     rdi, r14
     +0x1bf  call    mldsa44_polyvecl_uniform_gamma1
     after_mldsa44_polyvecl_uniform_gamma1:
     +0x1c4  mov     r13, QWORD PTR [rbp-0xac58]
     +0x1cb  mov     rdx, r14
     +0x1ce  mov     r14, QWORD PTR [rbp-0xac78]
     +0x1d5  mov     rsi, QWORD PTR [rbp-0xacc8]
     +0x1dc  mov     rcx, r13
     +0x1df  mov     rdi, r14
     +0x1e2  call    mldsa44_polyvec_matrix_pointwise_montgomery_yvec_eager
     after_mldsa44_polyvec_matrix_pointwise_montgomery_yvec_eager:
     +0x1e7  mov     rdi, r14
     +0x1ea  call    mldsa44_polyveck_caddq
     after_mldsa44_polyveck_caddq:
     +0x1ef  mov     rsi, r14
     +0x1f2  mov     r14, QWORD PTR [rbp-0xac90]
     +0x1f9  mov     rdx, r13
     +0x1fc  mov     rdi, r14
     +0x1ff  call    mldsa44_polyveck_decompose_pack_w1
     after_mldsa44_polyveck_decompose_pack_w1:
     +0x204  mov     rdi, r15
     +0x207  call    mldsa_shake256_init
     after_mldsa_shake256_init:
     +0x20c  mov     rsi, QWORD PTR [rbp-0xacc0]
     +0x213  mov     rdi, r15
     +0x216  mov     edx, 0x40
     +0x21b  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_1:
     +0x220  mov     rsi, r14
     +0x223  mov     edx, 0x300
     +0x228  mov     rdi, r15
     +0x22b  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_2:
     +0x230  mov     rdi, r15
     +0x233  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize:
     +0x238  mov     r14, QWORD PTR [rbp-0xaca0]
     +0x23f  mov     rdx, r15
     +0x242  mov     esi, 0x20
     +0x247  mov     rdi, r14
     +0x24a  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze:
     +0x24f  mov     rdi, r15
     +0x252  call    mldsa_shake256_release
     after_mldsa_shake256_release:
     +0x257  mov     rdi, r15
     +0x25a  xor     eax, eax
     +0x25c  mov     ecx, 0x1a
     +0x261  rep stos QWORD PTR es:[rdi], rax
     +0x264  mov     rsi, r14
     +0x267  mov     r14, QWORD PTR [rbp-0xac60]
     +0x26e  xor     r13d, r13d
     +0x271  mov     rdi, r14
     +0x274  call    mldsa44_poly_challenge
     after_mldsa44_poly_challenge:
     +0x279  mov     rdi, r14
     +0x27c  call    mldsa_poly_ntt
     loop1: after_mldsa_poly_ntt:
     +0x281  mov     rax, QWORD PTR [rbp-0xac98]
     +0x288  mov     r14, r13
     +0x28b  mov     rdi, r15
     +0x28e  mov     ecx, 0x80
     +0x293  shl     r14, 0xa
     +0x297  mov     DWORD PTR [rbp-0xac68], r13d
     +0x29e  mov     r15, r12
     +0x2a1  lea     rsi, [rax+r14*1]
     +0x2a5  rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
     +0x2a8  mov     rsi, QWORD PTR [rbp-0xac60]
     +0x2af  mov     rdi, r12
     +0x2b2  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_1:
     +0x2b7  mov     rdi, r12
     +0x2ba  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_1:
     +0x2bf  mov     rax, QWORD PTR [rbp-0xac70]
     +0x2c6  mov     ecx, 0x80
     +0x2cb  mov     rdi, QWORD PTR [rbp-0xac58]
     +0x2d2  mov     QWORD PTR [rbp-0xac58], rbx
     +0x2d9  lea     rsi, [rax+r14*1]
     +0x2dd  rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
     +0x2e0  mov     rsi, rbx
     +0x2e3  mov     rdi, r12
     +0x2e6  call    mldsa_poly_add
     after_mldsa_poly_add_1:
     +0x2eb  mov     rdi, r12
     +0x2ee  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_1:
     +0x2f3  mov     esi, 0x1ffb2
     +0x2f8  mov     rdi, r12
     +0x2fb  call    mldsa_poly_chknorm
     loop1_test1: after_mldsa_poly_chknorm_1:
     +0x300  test    eax, eax
     +0x302  jne     join7
     loop1_next1:
     +0x308  mov     edx, DWORD PTR [rbp-0xac68]
     +0x30e  mov     rdi, QWORD PTR [rbp-0xac88]
     +0x315  mov     rsi, r12
     +0x318  add     r13, 0x1
     +0x31c  call    mldsa44_pack_sig_z
     loop1_test2: after_mldsa44_pack_sig_z:
     +0x321  cmp     r13, 0x4
     loop1_back:
     +0x325  jne     loop1
     loop1_exit1:
     +0x32b  mov     QWORD PTR [rbp-0xac68], r12
     +0x332  xor     r13d, r13d
     +0x335  mov     QWORD PTR [rbp-0xacb8], r12
     +0x33c  mov     r12, QWORD PTR [rbp-0xac60]
     loop2:
     +0x343  mov     rax, QWORD PTR [rbp-0xaca8]
     +0x34a  mov     ecx, 0x80
     +0x34f  mov     rdi, rbx
     +0x352  mov     r15, rbx
     +0x355  lea     rsi, [rax+r13*1]
     +0x359  rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
     +0x35c  mov     rsi, r12
     +0x35f  mov     rdi, rbx
     +0x362  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_2:
     +0x367  mov     rdi, rbx
     +0x36a  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_2:
     +0x36f  mov     rax, QWORD PTR [rbp-0xac78]
     +0x376  mov     rsi, rbx
     +0x379  lea     r14, [rax+r13*1]
     +0x37d  mov     rdi, r14
     +0x380  call    mldsa_poly_sub
     after_mldsa_poly_sub:
     +0x385  mov     rdi, r14
     +0x388  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_2:
     +0x38d  mov     esi, 0x173b2
     +0x392  mov     rdi, r14
     +0x395  call    mldsa_poly_chknorm
     loop2_test1: after_mldsa_poly_chknorm_2:
     +0x39a  test    eax, eax
     +0x39c  jne     join6
     loop2_next1:
     +0x3a2  mov     rax, QWORD PTR [rbp-0xacb0]
     +0x3a9  mov     ecx, 0x80
     +0x3ae  mov     rdi, rbx
     +0x3b1  lea     rsi, [rax+r13*1]
     +0x3b5  rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
     +0x3b8  mov     rsi, r12
     +0x3bb  mov     rdi, rbx
     +0x3be  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_3:
     +0x3c3  mov     rdi, rbx
     +0x3c6  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_3:
     +0x3cb  mov     rdi, rbx
     +0x3ce  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_3:
     +0x3d3  mov     esi, 0x17400
     +0x3d8  mov     rdi, rbx
     +0x3db  call    mldsa_poly_chknorm
     loop2_test2: after_mldsa_poly_chknorm_3:
     +0x3e0  test    eax, eax
     +0x3e2  jne     join6
     loop2_next2:
     +0x3e8  mov     rsi, rbx
     +0x3eb  mov     rdi, r14
     +0x3ee  add     r13, 0x400
     +0x3f5  call    mldsa_poly_add
     loop2_test3: after_mldsa_poly_add_2:
     +0x3fa  cmp     r13, 0x1000
     loop2_back:
     +0x401  jne     loop2
     loop2_exit1:
     +0x407  mov     r14, QWORD PTR [rbp-0xac88]
     +0x40e  mov     rsi, QWORD PTR [rbp-0xaca0]
     +0x415  mov     QWORD PTR [rbp-0xac58], rbx
     +0x41c  mov     r15, QWORD PTR [rbp-0xac68]
     +0x423  mov     r12, QWORD PTR [rbp-0xacb8]
     +0x42a  mov     rdi, r14
     +0x42d  call    mldsa44_pack_sig_c
     after_mldsa44_pack_sig_c:
     +0x432  mov     rdx, QWORD PTR [rbp-0xac90]
     +0x439  mov     rcx, rbx
     +0x43c  mov     rdi, r14
     +0x43f  mov     rsi, QWORD PTR [rbp-0xac78]
     +0x446  call    mldsa44_pack_sig_h
     after_mldsa44_pack_sig_h:
     +0x44b  mov     r13d, eax
     join3:
     +0x44e  mov     rdi, r12
     +0x451  xor     eax, eax
     +0x453  mov     ecx, 0x80
     +0x458  rep stos QWORD PTR es:[rdi], rax
     +0x45b  mov     rdi, QWORD PTR [rbp-0xac60]
     +0x462  mov     ecx, 0x80
     +0x467  rep stos QWORD PTR es:[rdi], rax
     +0x46a  mov     rdi, QWORD PTR [rbp-0xac60]
     +0x471  mov     rdi, QWORD PTR [rbp-0xac78]
     +0x478  mov     ecx, 0x200
     +0x47d  rep stos QWORD PTR es:[rdi], rax
     +0x480  mov     rdi, QWORD PTR [rbp-0xac78]
     +0x487  mov     rdi, QWORD PTR [rbp-0xac90]
     +0x48e  mov     ecx, 0x60
     +0x493  rep stos QWORD PTR es:[rdi], rax
     +0x496  mov     rdi, QWORD PTR [rbp-0xac90]
     +0x49d  mov     ecx, 0x200
     +0x4a2  mov     rdi, rbx
     +0x4a5  rep stos QWORD PTR es:[rdi], rax
     +0x4a8  mov     rdi, QWORD PTR [rbp-0xac70]
     +0x4af  mov     ecx, 0x200
     +0x4b4  rep stos QWORD PTR es:[rdi], rax
     +0x4b7  mov     rdi, QWORD PTR [rbp-0xac70]
     +0x4be  mov     rax, QWORD PTR [rbp-0xaca0]
     +0x4c5  pxor    xmm0, xmm0
     +0x4c9  movaps  XMMWORD PTR [rax], xmm0
     +0x4cc  movaps  XMMWORD PTR [rax+0x10], xmm0
     +0x4d0  test    r13d, r13d
     +0x4d3  je      join5
     +0x4d5  cmp     r13d, 0xffffffff
     +0x4d9  jne     join4
     +0x4db  add     DWORD PTR [rbp-0xac7c], 0x4
     +0x4e2  mov     eax, DWORD PTR [rbp-0xac7c]
     +0x4e8  cmp     eax, 0xfff8
     +0x4ed  jne     join2
     +0x4f3  mov     r13d, 0xfffffffc
     join4:
     +0x4f9  mov     rdx, QWORD PTR [rbp-0xac88]
     +0x500  xor     eax, eax
     +0x502  lea     rdi, [rdx+0x8]
     +0x506  mov     rcx, rdx
     +0x509  mov     QWORD PTR [rdx], 0x0
     +0x510  mov     QWORD PTR [rdx+0x96c], 0x0
     +0x51b  and     rdi, 0xfffffffffffffff8
     +0x51f  sub     rcx, rdi
     +0x522  add     ecx, 0x974
     +0x528  shr     ecx, 0x3
     +0x52b  rep stos QWORD PTR es:[rdi], rax
     join5:
     +0x52e  mov     rdi, QWORD PTR [rbp-0xaca8]
     +0x535  xor     ebx, ebx
     +0x537  mov     ecx, 0x200
     +0x53c  mov     rax, rbx
     +0x53f  rep stos QWORD PTR es:[rdi], rax
     +0x542  mov     rdi, QWORD PTR [rbp-0xaca8]
     +0x549  mov     rdi, QWORD PTR [rbp-0xacb0]
     +0x550  mov     ecx, 0x200
     +0x555  rep stos QWORD PTR es:[rdi], rax
     +0x558  mov     rdi, QWORD PTR [rbp-0xacb0]
     +0x55f  mov     rdi, QWORD PTR [rbp-0xac98]
     +0x566  mov     ecx, 0x200
     +0x56b  rep stos QWORD PTR es:[rdi], rax
     +0x56e  mov     rdi, QWORD PTR [rbp-0xac98]
     +0x575  mov     r15, QWORD PTR [rbp-0xacc8]
     +0x57c  mov     edx, 0x4000
     +0x581  xor     esi, esi
     +0x583  mov     rdi, r15
     +0x586  call    memset
     after_memset:
     +0x58b  mov     rdi, QWORD PTR [rbp-0xacd8]
     +0x592  mov     rax, rbx
     +0x595  mov     ecx, 0x20
     +0x59a  rep stos QWORD PTR es:[rdi], rax
     +0x59d  mov     rdi, QWORD PTR [rbp-0xacd8]
     +0x5a4  lea     rsp, [rbp-0x30]
     +0x5a8  mov     eax, r13d
     +0x5ab  pop     rbx
     +0x5ac  pop     r10
     +0x5ae  pop     r12
     +0x5b0  pop     r13
     +0x5b2  pop     r14
     +0x5b4  pop     r15
     +0x5b6  pop     rbp
     +0x5b7  lea     rsp, [r10-0x8]
     ret:
     +0x5bb  ret
     +0x5bc  nop     DWORD PTR [rax+0x0]
     join6: loop2_exit2:
     +0x5c0  mov     QWORD PTR [rbp-0xac58], r15
     +0x5c7  mov     r12, QWORD PTR [rbp-0xacb8]
     +0x5ce  mov     r15, QWORD PTR [rbp-0xac68]
     join7: loop1_exit2:
     +0x5d5  mov     r13d, 0xffffffff
     +0x5db  jmp     join3
     +0x5e0  movdqu  xmm1, XMMWORD PTR [r12]
     +0x5e6  movdqu  xmm2, XMMWORD PTR [r12+0x10]
     +0x5ed  lea     rax, [rbp-0xabb0]
     +0x5f4  movdqu  xmm3, XMMWORD PTR [r12+0x20]
     +0x5fb  movdqu  xmm4, XMMWORD PTR [r12+0x30]
     +0x602  mov     QWORD PTR [rbp-0xacc0], rax
     +0x609  movaps  XMMWORD PTR [rbp-0xabb0], xmm1
     +0x610  movaps  XMMWORD PTR [rbp-0xaba0], xmm2
     +0x617  movaps  XMMWORD PTR [rbp-0xab90], xmm3
     +0x61e  movaps  XMMWORD PTR [rbp-0xab80], xmm4
     +0x625  jmp     join1

    plt_memset:
       +0x0  jmp     QWORD PTR [rip+0xefc2]
                     // got_memset
       +0x6  push    0x2
       +0xb  jmp     <.plt>
 ***)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_signature_internal"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The secret key skb at sk   *)
(* (2560 bytes), the message M of mlen bytes at m and the prefix PRE of      *)
(* prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu in the *)
(* first 64 bytes at m), and the 32 bytes RND at rnd, with MU the mu that    *)
(* the code uses: the result is 0, with the signature mld_sign_sig at sig    *)
(* (2420 bytes), if one of the 16382 attempts succeeds (mld_sign_ok), and -4 *)
(* with the signature zeroed otherwise. The last two arguments, sk and ext,  *)
(* are on the stack above the return address. The function aligns the stack  *)
(* pointer down to a multiple of 32, which may lower it by up to 31 bytes,   *)
(* copies the return address there, saves seven registers (RBP, the frame    *)
(* pointer, and R10, which holds the original stack pointer, among them) and *)
(* reserves 44232 bytes for its buffers, below which the callees use up to   *)
(* 5174 bytes, with their return addresses and stack arguments: 49501 bytes  *)
(* of stack below the return address in all. The GOT entry of memset, which  *)
(* the stub reads, and the region (ea,el) that memset may read are apart     *)
(* from the signature and the stack.                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
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
          mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
          mld_sign_terminates_44 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49501),49501)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49501),49501)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)] /\
          nonoverlapping (sig,2420) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_signature_internal) /\
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
                  memory :> bytes(word_sub stackpointer (word 49501),49501)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, ext, rho, what the C *)
(* code declassifies in each attempt (mld_sign_declass), the address of      *)
(* memset and the stack, with all accesses within the arguments, the stack,  *)
(* the return address and the arguments above it, the GOT entry of memset,   *)
(* the region (ea,el) that memset may read and the constants of the callees, *)
(* and the writes within the signature and the stack.                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
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
          mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
          mld_sign_terminates_44 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49501),49501)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49501),49501)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)] /\
          nonoverlapping (sig,2420) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_signature_internal) /\
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
                             mf pc (word_sub stackpointer (word 49501))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; pre,prelen; rnd,32; sk,2560;
                         word_sub stackpointer (word 49501),49501;
                         stackpointer,8; word_add stackpointer (word 8),16;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16]
                        [sig,2420;
                         word_sub stackpointer (word 49501),49501]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 49501),49501)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
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
          mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
          mld_sign_terminates_44 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49501),49501)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49501),49501)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)] /\
          nonoverlapping (sig,2420) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_signature_internal) /\
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
                             mf pc (word_sub stackpointer (word 49501))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; pre,prelen; rnd,32; sk,2560;
                         word_sub stackpointer (word 49501),49501;
                         stackpointer,8; word_add stackpointer (word 8),16;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16]
                        [sig,2420;
                         word_sub stackpointer (word 49501),49501]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 49501),49501)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
