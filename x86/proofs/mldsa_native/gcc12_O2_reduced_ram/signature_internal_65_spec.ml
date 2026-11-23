(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing: the statement. This is the code for mldsa65_signature_internal   *)
(* (mld_sign_signature_internal in sign.c, with                              *)
(* mld_attempt_signature_generation and mld_compute_pack_z inlined) from     *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 and  *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which aligns its      *)
(* stack frame to 32 bytes, unpacks the secret key (keeping only pointers    *)
(* into it for s1, s2 and t0), computes mu (or takes it from m if ext is     *)
(* nonzero) and rho'', copies rho into the structure of the matrix, which it *)
(* never stores, and makes up to 13106 attempts: each computes w = A y with  *)
(* the lazy product, which samples the polynomials of y and the entries of A *)
(* as it needs them, w1 packed, c~ and the challenge, then z, sampling y_i   *)
(* again and unpacking and transforming s1_i, checking and packing each      *)
(* polynomial, and for each row checks w0 - c s2 and c t0, unpacking and     *)
(* transforming s2 and t0 in turn, and finally packs c~ and the hints,       *)
(* rejecting at the first check that fails. It returns 0 with the signature  *)
(* of the first attempt that succeeds, or -4                                 *)
(* (MLD_ERR_SIGN_ATTEMPTS_EXHAUSTED) with the signature zeroed, and zeroes   *)
(* its buffers (the zeroization of the C code, which gcc inlines as REP      *)
(* STOSQ and SSE stores), so the direction flag must be clear, as the ABI    *)
(* requires on entry. It is verified in the whole image (see libmldsa.ml)    *)
(* against mld_sign_ok and mld_sign_sig of common/mldsa_native_sign.ml, the  *)
(* model of the default configuration, using the theorems for the callees,   *)
(* assuming that the expansion of the matrix and the sampling of the         *)
(* challenge in each attempt terminate, and shown to be constant time and    *)
(* memory safe, with the events depending only on public values and those    *)
(* that the C code declassifies (mld_sign_declass).                          *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_lazy.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/unpack_sk_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/H_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_expand_lazy_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_uniform_gamma1_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_yvec_lazy_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyveck_caddq_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyveck_decompose_pack_w1_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_absorb_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_finalize_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_squeeze_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_challenge_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_pointwise_montgomery_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_add_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_sub_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_reduce_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_chknorm_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyeta_unpack_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyt0_unpack_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/pack_sig_z_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/pack_sig_c_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/pack_sig_h_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa65_signature_internal:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  push    QWORD PTR [r10-0x8]
       +0xd  push    rbp
       +0xe  mov     rbp, rsp
      +0x11  push    r15
      +0x13  mov     r15, rsi
      +0x16  push    r14
      +0x18  lea     rax, [rbp-0x2d10]
      +0x1f  lea     r14, [rbp-0x2bf0]
      +0x26  push    r13
      +0x28  push    r12
      +0x2a  lea     r12, [rbp-0x2c30]
      +0x31  push    r10
      +0x33  mov     rsi, r12
      +0x36  push    rbx
      +0x37  mov     rbx, r9
      +0x3a  lea     r9, [rbp-0x2cd0]
      +0x41  sub     rsp, 0x2d68
      +0x48  mov     QWORD PTR [rbp-0x2d28], rdi
      +0x4f  lea     rdi, [rbp-0x2c50]
      +0x56  mov     r13d, DWORD PTR [r10+0x8]
      +0x5a  mov     QWORD PTR [rbp-0x2d20], rcx
      +0x61  lea     rcx, [rbp-0x2cf0]
      +0x68  mov     QWORD PTR [rbp-0x2d18], rdx
      +0x6f  mov     rdx, r14
      +0x72  mov     QWORD PTR [rbp-0x2d30], r8
      +0x79  mov     r8, rax
      +0x7c  mov     QWORD PTR [rbp-0x2d88], r9
      +0x83  mov     QWORD PTR [rbp-0x2d78], rax
      +0x8a  mov     QWORD PTR [rbp-0x2d80], rcx
      +0x91  mov     QWORD PTR [rbp-0x2d70], rdi
      +0x98  push    QWORD PTR [r10]
      +0x9b  call    mldsa65_unpack_sk
     after_mldsa65_unpack_sk:
      +0xa0  pop     r8
      +0xa2  pop     r9
      +0xa4  test    r13d, r13d
      +0xa7  jne     +0x588
      +0xad  lea     rax, [rbp-0x2bd0]
      +0xb4  mov     r9, QWORD PTR [rbp-0x2d30]
      +0xbb  mov     esi, 0x40
      +0xc0  mov     rdx, r12
      +0xc3  mov     QWORD PTR [rbp-0x2d60], rax
      +0xca  mov     r8, QWORD PTR [rbp-0x2d20]
      +0xd1  mov     rdi, rax
      +0xd4  mov     ecx, 0x40
      +0xd9  push    QWORD PTR [rbp-0x2d18]
      +0xdf  push    r15
      +0xe1  call    mld_H65
     after_mld_H65_1:
      +0xe6  pop     rsi
      +0xe7  pop     rdi
     join1:
      +0xe8  mov     rdx, r14
      +0xeb  mov     r8, rbx
      +0xee  mov     ecx, 0x20
      +0xf3  mov     esi, 0x40
      +0xf8  lea     rax, [rbp-0x2b90]
      +0xff  mov     r9d, 0x20
     +0x105  lea     r15, [rbp-0x2450]
     +0x10c  mov     QWORD PTR [rbp-0x2d68], rax
     +0x113  mov     rdi, rax
     +0x116  lea     rbx, [rbp-0x2850]
     +0x11d  lea     r12, [rbp-0x2050]
     +0x124  push    0x40
     +0x126  lea     r14, [rbp-0x2c90]
     +0x12d  push    QWORD PTR [rbp-0x2d60]
     +0x133  call    mld_H65
     after_mld_H65_2:
     +0x138  lea     rax, [rbp-0x1c50]
     +0x13f  mov     rsi, QWORD PTR [rbp-0x2d70]
     +0x146  mov     rdi, rax
     +0x149  mov     QWORD PTR [rbp-0x2d58], rax
     +0x150  call    mldsa65_polyvec_matrix_expand_lazy
     after_mldsa65_polyvec_matrix_expand_lazy:
     +0x155  pop     rax
     +0x156  lea     rax, [rbp-0x2cb0]
     +0x15d  pop     rdx
     +0x15e  mov     QWORD PTR [rbp-0x2d40], rax
     +0x165  lea     rax, [rbp-0x1830]
     +0x16c  xor     ecx, ecx
     +0x16e  mov     QWORD PTR [rbp-0x2d20], rax
     +0x175  lea     rax, [rbp-0x2b50]
     +0x17c  mov     WORD PTR [rbp-0x2d30], cx
     +0x183  mov     QWORD PTR [rbp-0x2d38], rax
     +0x18a  mov     QWORD PTR [rbp-0x2d18], r15
     +0x191  nop     DWORD PTR [rax+0x0]
     loop1:
     +0x198  mov     rax, QWORD PTR [rbp-0x2d68]
     +0x19f  mov     r15, QWORD PTR [rbp-0x2d20]
     +0x1a6  mov     rcx, rbx
     +0x1a9  mov     rdx, QWORD PTR [rbp-0x2d40]
     +0x1b0  mov     rsi, QWORD PTR [rbp-0x2d58]
     +0x1b7  mov     QWORD PTR [rbp-0x2cb0], rax
     +0x1be  movzx   eax, WORD PTR [rbp-0x2d30]
     +0x1c5  mov     rdi, r15
     +0x1c8  mov     WORD PTR [rbp-0x2ca8], ax
     +0x1cf  call    mldsa65_polyvec_matrix_pointwise_montgomery_yvec_lazy
     after_mldsa65_polyvec_matrix_pointwise_montgomery_yvec_lazy:
     +0x1d4  mov     rdi, r15
     +0x1d7  call    mldsa65_polyveck_caddq
     after_mldsa65_polyveck_caddq:
     +0x1dc  mov     rsi, r15
     +0x1df  mov     r15, QWORD PTR [rbp-0x2d38]
     +0x1e6  mov     rdx, rbx
     +0x1e9  mov     rdi, r15
     +0x1ec  call    mldsa65_polyveck_decompose_pack_w1
     after_mldsa65_polyveck_decompose_pack_w1:
     +0x1f1  mov     rdi, r12
     +0x1f4  call    mldsa_shake256_init
     after_mldsa_shake256_init:
     +0x1f9  mov     rsi, QWORD PTR [rbp-0x2d60]
     +0x200  mov     rdi, r12
     +0x203  mov     edx, 0x40
     +0x208  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_1:
     +0x20d  mov     rsi, r15
     +0x210  mov     edx, 0x300
     +0x215  mov     rdi, r12
     +0x218  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_2:
     +0x21d  mov     rdi, r12
     +0x220  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize:
     +0x225  mov     rdx, r12
     +0x228  mov     esi, 0x30
     +0x22d  mov     rdi, r14
     +0x230  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze:
     +0x235  mov     rdi, r12
     +0x238  call    mldsa_shake256_release
     after_mldsa_shake256_release:
     +0x23d  mov     rdi, r12
     +0x240  xor     eax, eax
     +0x242  mov     ecx, 0x1a
     +0x247  rep stos QWORD PTR es:[rdi], rax
     +0x24a  mov     r15, QWORD PTR [rbp-0x2d18]
     +0x251  mov     rsi, r14
     +0x254  mov     rdi, r15
     +0x257  call    mldsa65_poly_challenge
     after_mldsa65_poly_challenge:
     +0x25c  mov     rdi, r15
     +0x25f  xor     r15d, r15d
     +0x262  call    mldsa_poly_ntt
     loop2: after_mldsa_poly_ntt_1:
     +0x267  mov     rsi, r15
     +0x26a  mov     rdi, r12
     +0x26d  shl     rsi, 0x7
     +0x271  add     rsi, QWORD PTR [rbp-0x2d10]
     +0x278  call    mldsa65_polyeta_unpack
     after_mldsa65_polyeta_unpack_1:
     +0x27d  mov     rdi, r12
     +0x280  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_2:
     +0x285  mov     rsi, QWORD PTR [rbp-0x2d18]
     +0x28c  mov     rdi, r12
     +0x28f  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_1:
     +0x294  mov     rdi, r12
     +0x297  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_1:
     +0x29c  movzx   edx, WORD PTR [rbp-0x2ca8]
     +0x2a3  mov     rsi, QWORD PTR [rbp-0x2cb0]
     +0x2aa  mov     rdi, rbx
     +0x2ad  add     edx, r15d
     +0x2b0  movzx   edx, dx
     +0x2b3  call    mldsa65_poly_uniform_gamma1
     after_mldsa65_poly_uniform_gamma1:
     +0x2b8  mov     rsi, rbx
     +0x2bb  mov     rdi, r12
     +0x2be  call    mldsa_poly_add
     after_mldsa_poly_add_1:
     +0x2c3  mov     rdi, r12
     +0x2c6  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_1:
     +0x2cb  mov     esi, 0x7ff3c
     +0x2d0  mov     rdi, r12
     +0x2d3  call    mldsa_poly_chknorm
     loop2_test1: after_mldsa_poly_chknorm_1:
     +0x2d8  test    eax, eax
     +0x2da  jne     join6
     loop2_next1:
     +0x2e0  mov     rdi, QWORD PTR [rbp-0x2d28]
     +0x2e7  mov     edx, r15d
     +0x2ea  mov     rsi, r12
     +0x2ed  add     r15, 0x1
     +0x2f1  call    mldsa65_pack_sig_z
     loop2_test2: after_mldsa65_pack_sig_z:
     +0x2f6  cmp     r15, 0x5
     loop2_back:
     +0x2fa  jne     loop2
     loop2_exit1:
     +0x300  mov     QWORD PTR [rbp-0x2d48], r14
     +0x307  xor     r15d, r15d
     +0x30a  xor     r13d, r13d
     +0x30d  mov     QWORD PTR [rbp-0x2d50], r12
     +0x314  mov     r12, QWORD PTR [rbp-0x2d18]
     loop3:
     +0x31b  mov     rsi, QWORD PTR [rbp-0x2cd0]
     +0x322  mov     rdi, rbx
     +0x325  add     rsi, r13
     +0x328  call    mldsa65_polyeta_unpack
     after_mldsa65_polyeta_unpack_2:
     +0x32d  mov     rdi, rbx
     +0x330  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_3:
     +0x335  mov     rsi, r12
     +0x338  mov     rdi, rbx
     +0x33b  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_2:
     +0x340  mov     rdi, rbx
     +0x343  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_2:
     +0x348  mov     rax, QWORD PTR [rbp-0x2d20]
     +0x34f  mov     rsi, rbx
     +0x352  lea     r14, [rax+r13*8]
     +0x356  mov     rdi, r14
     +0x359  call    mldsa_poly_sub
     after_mldsa_poly_sub:
     +0x35e  mov     rdi, r14
     +0x361  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_2:
     +0x366  mov     esi, 0x3fe3c
     +0x36b  mov     rdi, r14
     +0x36e  call    mldsa_poly_chknorm
     loop3_test1: after_mldsa_poly_chknorm_2:
     +0x373  test    eax, eax
     +0x375  jne     join5
     loop3_next1:
     +0x37b  mov     rsi, QWORD PTR [rbp-0x2cf0]
     +0x382  mov     rdi, rbx
     +0x385  add     rsi, r15
     +0x388  call    mldsa_polyt0_unpack
     after_mldsa_polyt0_unpack:
     +0x38d  mov     rdi, rbx
     +0x390  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_4:
     +0x395  mov     rsi, r12
     +0x398  mov     rdi, rbx
     +0x39b  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_3:
     +0x3a0  mov     rdi, rbx
     +0x3a3  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_3:
     +0x3a8  mov     rdi, rbx
     +0x3ab  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_3:
     +0x3b0  mov     esi, 0x3ff00
     +0x3b5  mov     rdi, rbx
     +0x3b8  call    mldsa_poly_chknorm
     loop3_test2: after_mldsa_poly_chknorm_3:
     +0x3bd  test    eax, eax
     +0x3bf  jne     join5
     loop3_next2:
     +0x3c5  mov     rsi, rbx
     +0x3c8  mov     rdi, r14
     +0x3cb  sub     r13, 0xffffffffffffff80
     +0x3cf  add     r15, 0x1a0
     +0x3d6  call    mldsa_poly_add
     loop3_test3: after_mldsa_poly_add_2:
     +0x3db  cmp     r13, 0x300
     loop3_back:
     +0x3e2  jne     loop3
     loop3_exit1:
     +0x3e8  mov     r15, QWORD PTR [rbp-0x2d28]
     +0x3ef  mov     r14, QWORD PTR [rbp-0x2d48]
     +0x3f6  mov     r12, QWORD PTR [rbp-0x2d50]
     +0x3fd  mov     rsi, r14
     +0x400  mov     rdi, r15
     +0x403  call    mldsa65_pack_sig_c
     after_mldsa65_pack_sig_c:
     +0x408  mov     rdx, QWORD PTR [rbp-0x2d38]
     +0x40f  mov     rcx, rbx
     +0x412  mov     rdi, r15
     +0x415  mov     rsi, QWORD PTR [rbp-0x2d20]
     +0x41c  call    mldsa65_pack_sig_h
     after_mldsa65_pack_sig_h:
     +0x421  mov     edx, eax
     join2:
     +0x423  mov     rdi, r12
     +0x426  xor     eax, eax
     +0x428  mov     ecx, 0x80
     +0x42d  rep stos QWORD PTR es:[rdi], rax
     +0x430  mov     rdi, QWORD PTR [rbp-0x2d18]
     +0x437  mov     ecx, 0x80
     +0x43c  rep stos QWORD PTR es:[rdi], rax
     +0x43f  mov     rdi, QWORD PTR [rbp-0x2d18]
     +0x446  mov     rdi, QWORD PTR [rbp-0x2d20]
     +0x44d  mov     ecx, 0x300
     +0x452  rep stos QWORD PTR es:[rdi], rax
     +0x455  mov     rdi, QWORD PTR [rbp-0x2d20]
     +0x45c  mov     rdi, QWORD PTR [rbp-0x2d38]
     +0x463  mov     ecx, 0x60
     +0x468  rep stos QWORD PTR es:[rdi], rax
     +0x46b  mov     rdi, QWORD PTR [rbp-0x2d38]
     +0x472  mov     ecx, 0x80
     +0x477  mov     rdi, rbx
     +0x47a  rep stos QWORD PTR es:[rdi], rax
     +0x47d  mov     rax, QWORD PTR [rbp-0x2d40]
     +0x484  pxor    xmm0, xmm0
     +0x488  movaps  XMMWORD PTR [rax], xmm0
     +0x48b  movaps  XMMWORD PTR [r14], xmm0
     +0x48f  movaps  XMMWORD PTR [r14+0x10], xmm0
     +0x494  movaps  XMMWORD PTR [r14+0x20], xmm0
     loop1_test1:
     +0x499  test    edx, edx
     +0x49b  je      join4
     loop1_test2: loop1_next1:
     +0x49d  cmp     edx, 0xffffffff
     +0x4a0  jne     join3
     loop1_next2:
     +0x4a2  add     WORD PTR [rbp-0x2d30], 0x5
     +0x4aa  movzx   eax, WORD PTR [rbp-0x2d30]
     loop1_test3:
     +0x4b1  cmp     ax, 0xfffa
     loop1_back:
     +0x4b5  jne     loop1
     loop1_exit1:
     +0x4bb  mov     edx, 0xfffffffc
     join3: loop1_exit2:
     +0x4c0  mov     rbx, QWORD PTR [rbp-0x2d28]
     +0x4c7  xor     eax, eax
     +0x4c9  lea     rdi, [rbx+0x8]
     +0x4cd  mov     rcx, rbx
     +0x4d0  mov     QWORD PTR [rbx], 0x0
     +0x4d7  mov     QWORD PTR [rbx+0xce5], 0x0
     +0x4e2  and     rdi, 0xfffffffffffffff8
     +0x4e6  sub     rcx, rdi
     +0x4e9  add     ecx, 0xced
     +0x4ef  shr     ecx, 0x3
     +0x4f2  rep stos QWORD PTR es:[rdi], rax
     join4: loop1_exit3:
     +0x4f5  mov     QWORD PTR [rbp-0x2cd0], 0x0
     +0x500  mov     rax, QWORD PTR [rbp-0x2d88]
     +0x507  mov     QWORD PTR [rbp-0x2cf0], 0x0
     +0x512  mov     rax, QWORD PTR [rbp-0x2d80]
     +0x519  mov     QWORD PTR [rbp-0x2d10], 0x0
     +0x524  mov     rax, QWORD PTR [rbp-0x2d78]
     +0x52b  mov     rdi, QWORD PTR [rbp-0x2d58]
     +0x532  xor     eax, eax
     +0x534  mov     ecx, 0x84
     +0x539  rep stos QWORD PTR es:[rdi], rax
     +0x53c  mov     rdi, QWORD PTR [rbp-0x2d58]
     +0x543  mov     rdi, QWORD PTR [rbp-0x2d70]
     +0x54a  mov     ecx, 0x20
     +0x54f  rep stos QWORD PTR es:[rdi], rax
     +0x552  mov     rdi, QWORD PTR [rbp-0x2d70]
     +0x559  lea     rsp, [rbp-0x30]
     +0x55d  mov     eax, edx
     +0x55f  pop     rbx
     +0x560  pop     r10
     +0x562  pop     r12
     +0x564  pop     r13
     +0x566  pop     r14
     +0x568  pop     r15
     +0x56a  pop     rbp
     +0x56b  lea     rsp, [r10-0x8]
     ret:
     +0x56f  ret
     join5: loop3_exit2:
     +0x570  mov     r14, QWORD PTR [rbp-0x2d48]
     +0x577  mov     r12, QWORD PTR [rbp-0x2d50]
     join6: loop2_exit2:
     +0x57e  mov     edx, 0xffffffff
     +0x583  jmp     join2
     +0x588  movdqu  xmm1, XMMWORD PTR [r15]
     +0x58d  movdqu  xmm2, XMMWORD PTR [r15+0x10]
     +0x593  lea     rax, [rbp-0x2bd0]
     +0x59a  movdqu  xmm3, XMMWORD PTR [r15+0x20]
     +0x5a0  movdqu  xmm4, XMMWORD PTR [r15+0x30]
     +0x5a6  mov     QWORD PTR [rbp-0x2d60], rax
     +0x5ad  movaps  XMMWORD PTR [rbp-0x2bd0], xmm1
     +0x5b4  movaps  XMMWORD PTR [rbp-0x2bc0], xmm2
     +0x5bb  movaps  XMMWORD PTR [rbp-0x2bb0], xmm3
     +0x5c2  movaps  XMMWORD PTR [rbp-0x2ba0], xmm4
     +0x5c9  jmp     join1
 ***)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa65_signature_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The secret key skb at sk (4032 bytes), the message M of mlen *)
(* bytes at m and the prefix PRE of prelen bytes at pre (or, if ext is       *)
(* nonzero as a 32-bit integer, mu in the first 64 bytes at m), and the 32   *)
(* bytes RND at rnd, with MU the mu that the code uses: the result is 0,     *)
(* with the signature mld_sign_sig at sig (3309 bytes), if one of the 13106  *)
(* attempts succeeds (mld_sign_ok), and -4 with the signature zeroed         *)
(* otherwise. The last two arguments, sk and ext, are on the stack above the *)
(* return address. The function aligns the stack pointer down to a multiple  *)
(* of 32, which may lower it by up to 31 bytes, copies the return address    *)
(* there, saves seven registers (RBP, the frame pointer, and R10, which      *)
(* holds the original stack pointer, among them) and reserves 11624 bytes    *)
(* for its buffers, below which the callees use up to 1670 bytes, with their *)
(* return addresses and stack arguments: 13389 bytes of stack below the      *)
(* return address in all.                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!sig m mlen pre prelen rnd sk ext skb M PRE RND MU
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
         [(sig,3309); (word_sub stackpointer (word 13389),13389)] /\
        ALLPAIRS nonoverlapping
         [(sig,3309); (word_sub stackpointer (word 13389),13389)]
         [(m,mlen); (pre,prelen); (rnd,32); (sk,4032);
          (word pc,libmldsa_size)] /\
        nonoverlapping (sig,3309) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_signature_internal) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; m; word mlen; pre; word prelen; rnd] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8)))
                       s = sk /\
                  read (memory :> bytes64(word_add stackpointer (word 16)))
                       s = ext /\
                  (read DF s <=> false) /\
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
                memory :> bytes(word_sub stackpointer (word 13389),13389)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, ext, rho, what the C *)
(* code declassifies in each attempt (mld_sign_declass) and the stack, with  *)
(* all accesses within the arguments, the stack, the return address and the  *)
(* arguments above it and the constants of the callees, and the writes       *)
(* within the signature and the stack.                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
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
         [(sig,3309); (word_sub stackpointer (word 13389),13389)] /\
        ALLPAIRS nonoverlapping
         [(sig,3309); (word_sub stackpointer (word 13389),13389)]
         [(m,mlen); (pre,prelen); (rnd,32); (sk,4032);
          (word pc,libmldsa_size)] /\
        nonoverlapping (sig,3309) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_signature_internal) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; m; word mlen; pre; word prelen; rnd] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8)))
                       s = sk /\
                  read (memory :> bytes64(word_add stackpointer (word 16)))
                       s = ext /\
                  (read DF s <=> false) /\
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
                           pc (word_sub stackpointer (word 13389))
                           returnaddress /\
                     memaccess_inbounds e2
                      [sig,3309; m,mlen; pre,prelen; rnd,32; sk,4032;
                       word_sub stackpointer (word 13389),13389;
                       stackpointer,8; word_add stackpointer (word 8),16;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [sig,3309;
                       word_sub stackpointer (word 13389),13389]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(sig,3309);
                memory :> bytes(word_sub stackpointer (word 13389),13389)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
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
         [(sig,3309); (word_sub stackpointer (word 13389),13389)] /\
        ALLPAIRS nonoverlapping
         [(sig,3309); (word_sub stackpointer (word 13389),13389)]
         [(m,mlen); (pre,prelen); (rnd,32); (sk,4032);
          (word pc,libmldsa_size)] /\
        nonoverlapping (sig,3309) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_signature_internal) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; m; word mlen; pre; word prelen; rnd] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8)))
                       s = sk /\
                  read (memory :> bytes64(word_add stackpointer (word 16)))
                       s = ext /\
                  (read DF s <=> false) /\
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
                           pc (word_sub stackpointer (word 13389))
                           returnaddress /\
                     memaccess_inbounds e2
                      [sig,3309; m,mlen; pre,prelen; rnd,32; sk,4032;
                       word_sub stackpointer (word 13389),13389;
                       stackpointer,8; word_add stackpointer (word 8),16;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [sig,3309;
                       word_sub stackpointer (word 13389),13389]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(sig,3309);
                memory :> bytes(word_sub stackpointer (word 13389),13389)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
