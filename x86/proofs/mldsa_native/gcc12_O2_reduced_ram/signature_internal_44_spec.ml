(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing: the statement. This is the code for mldsa44_signature_internal   *)
(* (mld_sign_signature_internal in sign.c, with                              *)
(* mld_attempt_signature_generation and mld_compute_pack_z inlined) from     *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 and  *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which aligns its      *)
(* stack frame to 32 bytes, unpacks the secret key (keeping only pointers    *)
(* into it for s1, s2 and t0), computes mu (or takes it from m if ext is     *)
(* nonzero) and rho'', copies rho into the structure of the matrix, which it *)
(* never stores, and makes up to 16382 attempts: each computes w = A y with  *)
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
(* model of the default configuration, using the theorems for the callees    *)
(* and MLD_SIGN_W_LAZY_44 of lazy_spec.ml (w of the lazy product, made       *)
(* nonnegative, is that of the model), assuming that the expansion of the    *)
(* matrix and the sampling of the challenge in each attempt terminate, and   *)
(* shown to be constant time and memory safe, with the events depending only *)
(* on public values and those that the C code declassifies                   *)
(* (mld_sign_declass).                                                       *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec_lazy.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/unpack_sk_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/H_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_expand_lazy_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_uniform_gamma1_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_yvec_lazy_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyveck_caddq_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyveck_decompose_pack_w1_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_absorb_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_finalize_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_squeeze_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_challenge_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_pointwise_montgomery_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_add_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_sub_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_reduce_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_chknorm_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyeta_unpack_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyt0_unpack_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/pack_sig_z_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/pack_sig_c_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/pack_sig_h_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/lazy_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_signature_internal:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  push    QWORD PTR [r10-0x8]
       +0xd  push    rbp
       +0xe  mov     rbp, rsp
      +0x11  push    r15
      +0x13  mov     r15, rsi
      +0x16  push    r14
      +0x18  lea     rax, [rbp-0x24f0]
      +0x1f  lea     rsi, [rbp-0x2450]
      +0x26  push    r13
      +0x28  lea     r13, [rbp-0x23f0]
      +0x2f  push    r12
      +0x31  lea     r12, [rbp-0x2430]
      +0x38  push    r10
      +0x3a  push    rbx
      +0x3b  mov     rbx, r9
      +0x3e  lea     r9, [rbp-0x24b0]
      +0x45  sub     rsp, 0x2548
      +0x4c  mov     QWORD PTR [rbp-0x2500], rcx
      +0x53  lea     rcx, [rbp-0x24d0]
      +0x5a  mov     r14d, DWORD PTR [r10+0x8]
      +0x5e  mov     QWORD PTR [rbp-0x2508], rdi
      +0x65  mov     rdi, rsi
      +0x68  mov     QWORD PTR [rbp-0x24f8], rdx
      +0x6f  mov     rdx, r13
      +0x72  mov     QWORD PTR [rbp-0x2510], r8
      +0x79  mov     r8, rax
      +0x7c  mov     QWORD PTR [rbp-0x2550], r9
      +0x83  mov     QWORD PTR [rbp-0x2548], rsi
      +0x8a  mov     rsi, r12
      +0x8d  mov     QWORD PTR [rbp-0x2558], rax
      +0x94  mov     QWORD PTR [rbp-0x2560], rcx
      +0x9b  push    QWORD PTR [r10]
      +0x9e  call    mldsa44_unpack_sk
     after_mldsa44_unpack_sk:
      +0xa3  pop     r8
      +0xa5  pop     r9
      +0xa7  test    r14d, r14d
      +0xaa  jne     +0x571
      +0xb0  lea     rax, [rbp-0x23d0]
      +0xb7  mov     r9, QWORD PTR [rbp-0x2510]
      +0xbe  mov     esi, 0x40
      +0xc3  mov     rdx, r12
      +0xc6  mov     QWORD PTR [rbp-0x2538], rax
      +0xcd  mov     r8, QWORD PTR [rbp-0x2500]
      +0xd4  mov     rdi, rax
      +0xd7  mov     ecx, 0x40
      +0xdc  push    QWORD PTR [rbp-0x24f8]
      +0xe2  push    r15
      +0xe4  call    mld_H44
     after_mld_H44_1:
      +0xe9  pop     rsi
      +0xea  pop     rdi
     join1:
      +0xeb  mov     r8, rbx
      +0xee  mov     ecx, 0x20
      +0xf3  mov     rdx, r13
      +0xf6  mov     esi, 0x40
      +0xfb  lea     rax, [rbp-0x2390]
     +0x102  mov     r9d, 0x20
     +0x108  lea     r12, [rbp-0x2050]
     +0x10f  mov     QWORD PTR [rbp-0x2540], rax
     +0x116  mov     rdi, rax
     +0x119  lea     rbx, [rbp-0x1850]
     +0x120  lea     r15, [rbp-0x1c50]
     +0x127  push    0x40
     +0x129  push    QWORD PTR [rbp-0x2538]
     +0x12f  call    mld_H44
     after_mld_H44_2:
     +0x134  lea     rax, [rbp-0x1450]
     +0x13b  mov     rsi, QWORD PTR [rbp-0x2548]
     +0x142  mov     rdi, rax
     +0x145  mov     QWORD PTR [rbp-0x2530], rax
     +0x14c  call    mldsa44_polyvec_matrix_expand_lazy
     after_mldsa44_polyvec_matrix_expand_lazy:
     +0x151  pop     rax
     +0x152  lea     rax, [rbp-0x2490]
     +0x159  pop     rdx
     +0x15a  mov     QWORD PTR [rbp-0x2520], rax
     +0x161  lea     rax, [rbp-0x1030]
     +0x168  xor     ecx, ecx
     +0x16a  mov     QWORD PTR [rbp-0x24f8], rax
     +0x171  lea     rax, [rbp-0x2350]
     +0x178  mov     QWORD PTR [rbp-0x2510], rax
     +0x17f  lea     rax, [rbp-0x2470]
     +0x186  mov     WORD PTR [rbp-0x2500], cx
     +0x18d  mov     QWORD PTR [rbp-0x2518], rax
     +0x194  nop     DWORD PTR [rax+0x0]
     join2:
     +0x198  mov     rax, QWORD PTR [rbp-0x2540]
     +0x19f  mov     r14, QWORD PTR [rbp-0x24f8]
     +0x1a6  mov     rcx, r12
     +0x1a9  mov     rdx, QWORD PTR [rbp-0x2520]
     +0x1b0  mov     rsi, QWORD PTR [rbp-0x2530]
     +0x1b7  mov     QWORD PTR [rbp-0x2490], rax
     +0x1be  movzx   eax, WORD PTR [rbp-0x2500]
     +0x1c5  mov     rdi, r14
     +0x1c8  mov     WORD PTR [rbp-0x2488], ax
     +0x1cf  call    mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy
     after_mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy:
     +0x1d4  mov     rdi, r14
     +0x1d7  call    mldsa44_polyveck_caddq
     after_mldsa44_polyveck_caddq:
     +0x1dc  mov     rsi, r14
     +0x1df  mov     r14, QWORD PTR [rbp-0x2510]
     +0x1e6  mov     rdx, r12
     +0x1e9  mov     rdi, r14
     +0x1ec  call    mldsa44_polyveck_decompose_pack_w1
     after_mldsa44_polyveck_decompose_pack_w1:
     +0x1f1  mov     rdi, rbx
     +0x1f4  call    mldsa_shake256_init
     after_mldsa_shake256_init:
     +0x1f9  mov     rsi, QWORD PTR [rbp-0x2538]
     +0x200  mov     rdi, rbx
     +0x203  mov     edx, 0x40
     +0x208  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_1:
     +0x20d  mov     rsi, r14
     +0x210  mov     edx, 0x300
     +0x215  mov     rdi, rbx
     +0x218  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_2:
     +0x21d  mov     rdi, rbx
     +0x220  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize:
     +0x225  mov     r14, QWORD PTR [rbp-0x2518]
     +0x22c  mov     rdx, rbx
     +0x22f  mov     esi, 0x20
     +0x234  mov     rdi, r14
     +0x237  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze:
     +0x23c  mov     rdi, rbx
     +0x23f  call    mldsa_shake256_release
     after_mldsa_shake256_release:
     +0x244  mov     rdi, rbx
     +0x247  xor     eax, eax
     +0x249  mov     ecx, 0x1a
     +0x24e  rep stos QWORD PTR es:[rdi], rax
     +0x251  mov     rsi, r14
     +0x254  mov     rdi, r15
     +0x257  xor     r14d, r14d
     +0x25a  call    mldsa44_poly_challenge
     after_mldsa44_poly_challenge:
     +0x25f  mov     rdi, r15
     +0x262  call    mldsa_poly_ntt
     loop1: after_mldsa_poly_ntt_1:
     +0x267  lea     rsi, [r14+r14*2]
     +0x26b  mov     rdi, rbx
     +0x26e  shl     rsi, 0x5
     +0x272  add     rsi, QWORD PTR [rbp-0x24f0]
     +0x279  call    mldsa44_polyeta_unpack
     after_mldsa44_polyeta_unpack_1:
     +0x27e  mov     rdi, rbx
     +0x281  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_2:
     +0x286  mov     rsi, r15
     +0x289  mov     rdi, rbx
     +0x28c  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_1:
     +0x291  mov     rdi, rbx
     +0x294  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_1:
     +0x299  movzx   edx, WORD PTR [rbp-0x2488]
     +0x2a0  mov     rsi, QWORD PTR [rbp-0x2490]
     +0x2a7  mov     rdi, r12
     +0x2aa  add     edx, r14d
     +0x2ad  movzx   edx, dx
     +0x2b0  call    mldsa44_poly_uniform_gamma1
     after_mldsa44_poly_uniform_gamma1:
     +0x2b5  mov     rsi, r12
     +0x2b8  mov     rdi, rbx
     +0x2bb  call    mldsa_poly_add
     after_mldsa_poly_add_1:
     +0x2c0  mov     rdi, rbx
     +0x2c3  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_1:
     +0x2c8  mov     esi, 0x1ffb2
     +0x2cd  mov     rdi, rbx
     +0x2d0  call    mldsa_poly_chknorm
     loop1_test1: after_mldsa_poly_chknorm_1:
     +0x2d5  test    eax, eax
     +0x2d7  jne     join7
     loop1_next1:
     +0x2dd  mov     rdi, QWORD PTR [rbp-0x2508]
     +0x2e4  mov     edx, r14d
     +0x2e7  mov     rsi, rbx
     +0x2ea  add     r14, 0x1
     +0x2ee  call    mldsa44_pack_sig_z
     loop1_test2: after_mldsa44_pack_sig_z:
     +0x2f3  cmp     r14, 0x4
     loop1_back:
     +0x2f7  jne     loop1
     loop1_exit1:
     +0x2fd  xor     eax, eax
     +0x2ff  mov     r13, QWORD PTR [rbp-0x24f8]
     +0x306  mov     QWORD PTR [rbp-0x2528], rbx
     +0x30d  xor     r14d, r14d
     +0x310  mov     rbx, rax
     loop2:
     +0x313  mov     rsi, QWORD PTR [rbp-0x24b0]
     +0x31a  mov     rdi, r12
     +0x31d  add     rsi, r14
     +0x320  call    mldsa44_polyeta_unpack
     after_mldsa44_polyeta_unpack_2:
     +0x325  mov     rdi, r12
     +0x328  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_3:
     +0x32d  mov     rsi, r15
     +0x330  mov     rdi, r12
     +0x333  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_2:
     +0x338  mov     rdi, r12
     +0x33b  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_2:
     +0x340  mov     rsi, r12
     +0x343  mov     rdi, r13
     +0x346  call    mldsa_poly_sub
     after_mldsa_poly_sub:
     +0x34b  mov     rdi, r13
     +0x34e  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_2:
     +0x353  mov     esi, 0x173b2
     +0x358  mov     rdi, r13
     +0x35b  call    mldsa_poly_chknorm
     loop2_test1: after_mldsa_poly_chknorm_2:
     +0x360  test    eax, eax
     +0x362  jne     join6
     loop2_next1:
     +0x368  mov     rsi, QWORD PTR [rbp-0x24d0]
     +0x36f  mov     rdi, r12
     +0x372  add     rsi, rbx
     +0x375  call    mldsa_polyt0_unpack
     after_mldsa_polyt0_unpack:
     +0x37a  mov     rdi, r12
     +0x37d  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_4:
     +0x382  mov     rsi, r15
     +0x385  mov     rdi, r12
     +0x388  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_3:
     +0x38d  mov     rdi, r12
     +0x390  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_3:
     +0x395  mov     rdi, r12
     +0x398  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_3:
     +0x39d  mov     esi, 0x17400
     +0x3a2  mov     rdi, r12
     +0x3a5  call    mldsa_poly_chknorm
     loop2_test2: after_mldsa_poly_chknorm_3:
     +0x3aa  test    eax, eax
     +0x3ac  jne     join6
     loop2_next2:
     +0x3b2  mov     rdi, r13
     +0x3b5  mov     rsi, r12
     +0x3b8  add     r14, 0x60
     +0x3bc  add     r13, 0x400
     +0x3c3  call    mldsa_poly_add
     after_mldsa_poly_add_2:
     +0x3c8  add     rbx, 0x1a0
     loop2_test3:
     +0x3cf  cmp     r14, 0x180
     loop2_back:
     +0x3d6  jne     loop2
     loop2_exit1:
     +0x3dc  mov     r14, QWORD PTR [rbp-0x2508]
     +0x3e3  mov     rsi, QWORD PTR [rbp-0x2518]
     +0x3ea  mov     rbx, QWORD PTR [rbp-0x2528]
     +0x3f1  mov     rdi, r14
     +0x3f4  call    mldsa44_pack_sig_c
     after_mldsa44_pack_sig_c:
     +0x3f9  mov     rdx, QWORD PTR [rbp-0x2510]
     +0x400  mov     rcx, r12
     +0x403  mov     rdi, r14
     +0x406  mov     rsi, QWORD PTR [rbp-0x24f8]
     +0x40d  call    mldsa44_pack_sig_h
     after_mldsa44_pack_sig_h:
     +0x412  mov     edx, eax
     join3:
     +0x414  mov     rdi, rbx
     +0x417  xor     eax, eax
     +0x419  mov     ecx, 0x80
     +0x41e  rep stos QWORD PTR es:[rdi], rax
     +0x421  mov     ecx, 0x80
     +0x426  mov     rdi, r15
     +0x429  rep stos QWORD PTR es:[rdi], rax
     +0x42c  mov     rdi, QWORD PTR [rbp-0x24f8]
     +0x433  mov     ecx, 0x200
     +0x438  rep stos QWORD PTR es:[rdi], rax
     +0x43b  mov     rdi, QWORD PTR [rbp-0x24f8]
     +0x442  mov     rdi, QWORD PTR [rbp-0x2510]
     +0x449  mov     ecx, 0x60
     +0x44e  rep stos QWORD PTR es:[rdi], rax
     +0x451  mov     rdi, QWORD PTR [rbp-0x2510]
     +0x458  mov     ecx, 0x80
     +0x45d  mov     rdi, r12
     +0x460  rep stos QWORD PTR es:[rdi], rax
     +0x463  mov     rax, QWORD PTR [rbp-0x2520]
     +0x46a  pxor    xmm0, xmm0
     +0x46e  movaps  XMMWORD PTR [rax], xmm0
     +0x471  mov     rax, QWORD PTR [rbp-0x2518]
     +0x478  movaps  XMMWORD PTR [rax], xmm0
     +0x47b  movaps  XMMWORD PTR [rax+0x10], xmm0
     +0x47f  test    edx, edx
     +0x481  je      join5
     +0x483  cmp     edx, 0xffffffff
     +0x486  jne     join4
     +0x488  add     WORD PTR [rbp-0x2500], 0x4
     +0x490  movzx   eax, WORD PTR [rbp-0x2500]
     +0x497  cmp     ax, 0xfff8
     +0x49b  jne     join2
     +0x4a1  mov     edx, 0xfffffffc
     join4:
     +0x4a6  mov     rbx, QWORD PTR [rbp-0x2508]
     +0x4ad  xor     eax, eax
     +0x4af  lea     rdi, [rbx+0x8]
     +0x4b3  mov     rcx, rbx
     +0x4b6  mov     QWORD PTR [rbx], 0x0
     +0x4bd  mov     QWORD PTR [rbx+0x96c], 0x0
     +0x4c8  and     rdi, 0xfffffffffffffff8
     +0x4cc  sub     rcx, rdi
     +0x4cf  add     ecx, 0x974
     +0x4d5  shr     ecx, 0x3
     +0x4d8  rep stos QWORD PTR es:[rdi], rax
     join5:
     +0x4db  mov     QWORD PTR [rbp-0x24b0], 0x0
     +0x4e6  mov     rax, QWORD PTR [rbp-0x2550]
     +0x4ed  mov     QWORD PTR [rbp-0x24d0], 0x0
     +0x4f8  mov     rax, QWORD PTR [rbp-0x2560]
     +0x4ff  mov     QWORD PTR [rbp-0x24f0], 0x0
     +0x50a  mov     rax, QWORD PTR [rbp-0x2558]
     +0x511  mov     rdi, QWORD PTR [rbp-0x2530]
     +0x518  xor     eax, eax
     +0x51a  mov     ecx, 0x84
     +0x51f  rep stos QWORD PTR es:[rdi], rax
     +0x522  mov     rdi, QWORD PTR [rbp-0x2530]
     +0x529  mov     rdi, QWORD PTR [rbp-0x2548]
     +0x530  mov     ecx, 0x20
     +0x535  rep stos QWORD PTR es:[rdi], rax
     +0x538  mov     rdi, QWORD PTR [rbp-0x2548]
     +0x53f  lea     rsp, [rbp-0x30]
     +0x543  mov     eax, edx
     +0x545  pop     rbx
     +0x546  pop     r10
     +0x548  pop     r12
     +0x54a  pop     r13
     +0x54c  pop     r14
     +0x54e  pop     r15
     +0x550  pop     rbp
     +0x551  lea     rsp, [r10-0x8]
     ret:
     +0x555  ret
     +0x556  cs nop  WORD PTR [rax+rax*1+0x0]
     join6: loop2_exit2:
     +0x560  mov     rbx, QWORD PTR [rbp-0x2528]
     join7: loop1_exit2:
     +0x567  mov     edx, 0xffffffff
     +0x56c  jmp     join3
     +0x571  movdqu  xmm1, XMMWORD PTR [r15]
     +0x576  movdqu  xmm2, XMMWORD PTR [r15+0x10]
     +0x57c  lea     rax, [rbp-0x23d0]
     +0x583  movdqu  xmm3, XMMWORD PTR [r15+0x20]
     +0x589  movdqu  xmm4, XMMWORD PTR [r15+0x30]
     +0x58f  mov     QWORD PTR [rbp-0x2538], rax
     +0x596  movaps  XMMWORD PTR [rbp-0x23d0], xmm1
     +0x59d  movaps  XMMWORD PTR [rbp-0x23c0], xmm2
     +0x5a4  movaps  XMMWORD PTR [rbp-0x23b0], xmm3
     +0x5ab  movaps  XMMWORD PTR [rbp-0x23a0], xmm4
     +0x5b2  jmp     join1
 ***)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa44_signature_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The secret key skb at sk (2560 bytes), the message M of mlen *)
(* bytes at m and the prefix PRE of prelen bytes at pre (or, if ext is       *)
(* nonzero as a 32-bit integer, mu in the first 64 bytes at m), and the 32   *)
(* bytes RND at rnd, with MU the mu that the code uses: the result is 0,     *)
(* with the signature mld_sign_sig at sig (2420 bytes), if one of the 16382  *)
(* attempts succeeds (mld_sign_ok), and -4 with the signature zeroed         *)
(* otherwise. The last two arguments, sk and ext, are on the stack above the *)
(* return address. The function aligns the stack pointer down to a multiple  *)
(* of 32, which may lower it by up to 31 bytes, copies the return address    *)
(* there, saves seven registers (RBP, the frame pointer, and R10, which      *)
(* holds the original stack pointer, among them) and reserves 9544 bytes for *)
(* its buffers, below which the callees use up to 1670 bytes, with their     *)
(* return addresses and stack arguments: 11309 bytes of stack below the      *)
(* return address in all.                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!sig m mlen pre prelen rnd sk ext skb M PRE RND MU
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
         [(sig,2420); (word_sub stackpointer (word 11309),11309)] /\
        ALLPAIRS nonoverlapping
         [(sig,2420); (word_sub stackpointer (word 11309),11309)]
         [(m,mlen); (pre,prelen); (rnd,32); (sk,2560);
          (word pc,libmldsa_size)] /\
        nonoverlapping (sig,2420) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa44_signature_internal) /\
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
                memory :> bytes(word_sub stackpointer (word 11309),11309)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, ext, rho, what the C *)
(* code declassifies in each attempt (mld_sign_declass) and the stack, with  *)
(* all accesses within the arguments, the stack, the return address and the  *)
(* arguments above it and the constants of the callees, and the writes       *)
(* within the signature and the stack.                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
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
         [(sig,2420); (word_sub stackpointer (word 11309),11309)] /\
        ALLPAIRS nonoverlapping
         [(sig,2420); (word_sub stackpointer (word 11309),11309)]
         [(m,mlen); (pre,prelen); (rnd,32); (sk,2560);
          (word pc,libmldsa_size)] /\
        nonoverlapping (sig,2420) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa44_signature_internal) /\
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
                           pc (word_sub stackpointer (word 11309))
                           returnaddress /\
                     memaccess_inbounds e2
                      [sig,2420; m,mlen; pre,prelen; rnd,32; sk,2560;
                       word_sub stackpointer (word 11309),11309;
                       stackpointer,8; word_add stackpointer (word 8),16;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [sig,2420;
                       word_sub stackpointer (word 11309),11309]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(sig,2420);
                memory :> bytes(word_sub stackpointer (word 11309),11309)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
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
         [(sig,2420); (word_sub stackpointer (word 11309),11309)] /\
        ALLPAIRS nonoverlapping
         [(sig,2420); (word_sub stackpointer (word 11309),11309)]
         [(m,mlen); (pre,prelen); (rnd,32); (sk,2560);
          (word pc,libmldsa_size)] /\
        nonoverlapping (sig,2420) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa44_signature_internal) /\
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
                           pc (word_sub stackpointer (word 11309))
                           returnaddress /\
                     memaccess_inbounds e2
                      [sig,2420; m,mlen; pre,prelen; rnd,32; sk,2560;
                       word_sub stackpointer (word 11309),11309;
                       stackpointer,8; word_add stackpointer (word 8),16;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [sig,2420;
                       word_sub stackpointer (word 11309),11309]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(sig,2420);
                memory :> bytes(word_sub stackpointer (word 11309),11309)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
