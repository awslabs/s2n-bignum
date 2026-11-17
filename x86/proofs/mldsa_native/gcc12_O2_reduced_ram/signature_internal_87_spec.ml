(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing: the statement. This is the code for mldsa87_signature_internal   *)
(* (mld_sign_signature_internal in sign.c, with                              *)
(* mld_attempt_signature_generation and mld_compute_pack_z inlined) from     *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 and  *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which aligns its      *)
(* stack frame to 32 bytes, unpacks the secret key (keeping only pointers    *)
(* into it for s1, s2 and t0), computes mu (or takes it from m if ext is     *)
(* nonzero) and rho'', copies rho into the structure of the matrix, which it *)
(* never stores, and makes up to 9361 attempts: each computes w = A y with   *)
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
(* and MLD_SIGN_W_LAZY_87 of lazy_spec.ml (w of the lazy product, made       *)
(* nonnegative, is that of the model), assuming that the expansion of the    *)
(* matrix and the sampling of the challenge in each attempt terminate, and   *)
(* shown to be constant time and memory safe, with the events depending only *)
(* on public values and those that the C code declassifies                   *)
(* (mld_sign_declass).                                                       *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec_lazy.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/unpack_sk_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/H_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_expand_lazy_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_uniform_gamma1_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_yvec_lazy_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyveck_caddq_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyveck_decompose_pack_w1_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_absorb_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_finalize_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_squeeze_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_challenge_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_pointwise_montgomery_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_add_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_sub_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_reduce_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_chknorm_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyeta_unpack_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyt0_unpack_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/pack_sig_z_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/pack_sig_c_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/pack_sig_h_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/lazy_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa87_signature_internal:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  push    QWORD PTR [r10-0x8]
       +0xd  push    rbp
       +0xe  mov     rbp, rsp
      +0x11  push    r15
      +0x13  push    r14
      +0x15  lea     rax, [rbp-0x3610]
      +0x1c  lea     r14, [rbp-0x34f0]
      +0x23  push    r13
      +0x25  mov     r13, rsi
      +0x28  lea     rsi, [rbp-0x35f0]
      +0x2f  lea     r15, [rbp-0x3530]
      +0x36  push    r12
      +0x38  push    r10
      +0x3a  push    rbx
      +0x3b  mov     rbx, r9
      +0x3e  lea     r9, [rbp-0x35d0]
      +0x45  sub     rsp, 0x3668
      +0x4c  mov     QWORD PTR [rbp-0x3618], rdi
      +0x53  lea     rdi, [rbp-0x3550]
      +0x5a  mov     r12d, DWORD PTR [r10+0x8]
      +0x5e  mov     QWORD PTR [rbp-0x3620], rdx
      +0x65  mov     rdx, r14
      +0x68  mov     QWORD PTR [rbp-0x3628], rcx
      +0x6f  mov     rcx, rsi
      +0x72  mov     QWORD PTR [rbp-0x3630], r8
      +0x79  mov     r8, rax
      +0x7c  mov     QWORD PTR [rbp-0x3680], r9
      +0x83  mov     QWORD PTR [rbp-0x3678], rsi
      +0x8a  mov     rsi, r15
      +0x8d  mov     QWORD PTR [rbp-0x3670], rax
      +0x94  mov     QWORD PTR [rbp-0x3668], rdi
      +0x9b  push    QWORD PTR [r10]
      +0x9e  call    mldsa87_unpack_sk
     after_mldsa87_unpack_sk:
      +0xa3  pop     r8
      +0xa5  pop     r9
      +0xa7  test    r12d, r12d
      +0xaa  jne     +0x581
      +0xb0  sub     rsp, 0x8
      +0xb4  mov     rsi, r15
      +0xb7  mov     r9, r13
      +0xba  mov     edx, 0x40
      +0xbf  lea     rax, [rbp-0x34d0]
      +0xc6  mov     r8, QWORD PTR [rbp-0x3630]
      +0xcd  mov     rcx, QWORD PTR [rbp-0x3628]
      +0xd4  mov     QWORD PTR [rbp-0x3658], rax
      +0xdb  mov     rdi, rax
      +0xde  push    QWORD PTR [rbp-0x3620]
      +0xe4  call    mld_H87
     after_mld_H87_1:
      +0xe9  pop     rsi
      +0xea  pop     rdi
     join1:
      +0xeb  sub     rsp, 0x8
      +0xef  mov     rcx, rbx
      +0xf2  mov     edx, 0x20
      +0xf7  mov     rsi, r14
      +0xfa  lea     rax, [rbp-0x3490]
     +0x101  mov     r9, QWORD PTR [rbp-0x3658]
     +0x108  mov     r8d, 0x20
     +0x10e  lea     rbx, [rbp-0x3450]
     +0x115  mov     QWORD PTR [rbp-0x3660], rax
     +0x11c  mov     rdi, rax
     +0x11f  lea     r12, [rbp-0x2850]
     +0x126  lea     r15, [rbp-0x2c50]
     +0x12d  push    0x40
     +0x12f  call    mld_H87
     after_mld_H87_2:
     +0x134  lea     rax, [rbp-0x2450]
     +0x13b  mov     rsi, QWORD PTR [rbp-0x3668]
     +0x142  mov     rdi, rax
     +0x145  mov     QWORD PTR [rbp-0x3650], rax
     +0x14c  call    mldsa87_polyvec_matrix_expand_lazy
     after_mldsa87_polyvec_matrix_expand_lazy:
     +0x151  pop     rax
     +0x152  lea     rax, [rbp-0x35b0]
     +0x159  pop     rdx
     +0x15a  mov     QWORD PTR [rbp-0x3640], rax
     +0x161  lea     rax, [rbp-0x2030]
     +0x168  xor     ecx, ecx
     +0x16a  mov     QWORD PTR [rbp-0x3620], rax
     +0x171  lea     rax, [rbp-0x3050]
     +0x178  mov     QWORD PTR [rbp-0x3630], rax
     +0x17f  lea     rax, [rbp-0x3590]
     +0x186  mov     WORD PTR [rbp-0x3628], cx
     +0x18d  mov     QWORD PTR [rbp-0x3638], rax
     +0x194  nop     DWORD PTR [rax+0x0]
     join2:
     +0x198  mov     rax, QWORD PTR [rbp-0x3660]
     +0x19f  mov     r14, QWORD PTR [rbp-0x3620]
     +0x1a6  mov     rcx, rbx
     +0x1a9  mov     rdx, QWORD PTR [rbp-0x3640]
     +0x1b0  mov     rsi, QWORD PTR [rbp-0x3650]
     +0x1b7  mov     QWORD PTR [rbp-0x35b0], rax
     +0x1be  movzx   eax, WORD PTR [rbp-0x3628]
     +0x1c5  mov     rdi, r14
     +0x1c8  mov     WORD PTR [rbp-0x35a8], ax
     +0x1cf  call    mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy
     after_mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy:
     +0x1d4  mov     rdi, r14
     +0x1d7  call    mldsa87_polyveck_caddq
     after_mldsa87_polyveck_caddq:
     +0x1dc  mov     rsi, r14
     +0x1df  mov     r14, QWORD PTR [rbp-0x3630]
     +0x1e6  mov     rdx, rbx
     +0x1e9  mov     rdi, r14
     +0x1ec  call    mldsa87_polyveck_decompose_pack_w1
     after_mldsa87_polyveck_decompose_pack_w1:
     +0x1f1  mov     rdi, r12
     +0x1f4  call    mldsa_shake256_init
     after_mldsa_shake256_init:
     +0x1f9  mov     rsi, QWORD PTR [rbp-0x3658]
     +0x200  mov     rdi, r12
     +0x203  mov     edx, 0x40
     +0x208  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_1:
     +0x20d  mov     rsi, r14
     +0x210  mov     edx, 0x400
     +0x215  mov     rdi, r12
     +0x218  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_2:
     +0x21d  mov     rdi, r12
     +0x220  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize:
     +0x225  mov     r14, QWORD PTR [rbp-0x3638]
     +0x22c  mov     rdx, r12
     +0x22f  mov     esi, 0x40
     +0x234  mov     rdi, r14
     +0x237  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze:
     +0x23c  mov     rdi, r12
     +0x23f  call    mldsa_shake256_release
     after_mldsa_shake256_release:
     +0x244  mov     rdi, r12
     +0x247  xor     eax, eax
     +0x249  mov     ecx, 0x1a
     +0x24e  rep stos QWORD PTR es:[rdi], rax
     +0x251  mov     rsi, r14
     +0x254  mov     rdi, r15
     +0x257  xor     r14d, r14d
     +0x25a  call    mldsa87_poly_challenge
     after_mldsa87_poly_challenge:
     +0x25f  mov     rdi, r15
     +0x262  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_1:
     +0x267  nop     WORD PTR [rax+rax*1+0x0]
     loop1:
     +0x270  lea     rsi, [r14+r14*2]
     +0x274  mov     rdi, r12
     +0x277  shl     rsi, 0x5
     +0x27b  add     rsi, QWORD PTR [rbp-0x3610]
     +0x282  call    mldsa87_polyeta_unpack
     after_mldsa87_polyeta_unpack_1:
     +0x287  mov     rdi, r12
     +0x28a  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_2:
     +0x28f  mov     rsi, r15
     +0x292  mov     rdi, r12
     +0x295  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_1:
     +0x29a  mov     rdi, r12
     +0x29d  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_1:
     +0x2a2  movzx   edx, WORD PTR [rbp-0x35a8]
     +0x2a9  mov     rsi, QWORD PTR [rbp-0x35b0]
     +0x2b0  mov     rdi, rbx
     +0x2b3  add     edx, r14d
     +0x2b6  movzx   edx, dx
     +0x2b9  call    mldsa87_poly_uniform_gamma1
     after_mldsa87_poly_uniform_gamma1:
     +0x2be  mov     rsi, rbx
     +0x2c1  mov     rdi, r12
     +0x2c4  call    mldsa_poly_add
     after_mldsa_poly_add_1:
     +0x2c9  mov     rdi, r12
     +0x2cc  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_1:
     +0x2d1  mov     esi, 0x7ff88
     +0x2d6  mov     rdi, r12
     +0x2d9  call    mldsa_poly_chknorm
     loop1_test1: after_mldsa_poly_chknorm_1:
     +0x2de  test    eax, eax
     +0x2e0  jne     join7
     loop1_next1:
     +0x2e6  mov     rdi, QWORD PTR [rbp-0x3618]
     +0x2ed  mov     edx, r14d
     +0x2f0  mov     rsi, r12
     +0x2f3  add     r14, 0x1
     +0x2f7  call    mldsa87_pack_sig_z
     loop1_test2: after_mldsa87_pack_sig_z:
     +0x2fc  cmp     r14, 0x7
     loop1_back:
     +0x300  jne     loop1
     loop1_exit1:
     +0x306  xor     eax, eax
     +0x308  mov     r13, QWORD PTR [rbp-0x3620]
     +0x30f  mov     QWORD PTR [rbp-0x3648], r12
     +0x316  xor     r14d, r14d
     +0x319  mov     r12, rax
     +0x31c  nop     DWORD PTR [rax+0x0]
     loop2:
     +0x320  mov     rsi, QWORD PTR [rbp-0x35d0]
     +0x327  mov     rdi, rbx
     +0x32a  add     rsi, r14
     +0x32d  call    mldsa87_polyeta_unpack
     after_mldsa87_polyeta_unpack_2:
     +0x332  mov     rdi, rbx
     +0x335  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_3:
     +0x33a  mov     rsi, r15
     +0x33d  mov     rdi, rbx
     +0x340  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_2:
     +0x345  mov     rdi, rbx
     +0x348  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_2:
     +0x34d  mov     rsi, rbx
     +0x350  mov     rdi, r13
     +0x353  call    mldsa_poly_sub
     after_mldsa_poly_sub:
     +0x358  mov     rdi, r13
     +0x35b  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_2:
     +0x360  mov     esi, 0x3fe88
     +0x365  mov     rdi, r13
     +0x368  call    mldsa_poly_chknorm
     loop2_test1: after_mldsa_poly_chknorm_2:
     +0x36d  test    eax, eax
     +0x36f  jne     join6
     loop2_next1:
     +0x375  mov     rsi, QWORD PTR [rbp-0x35f0]
     +0x37c  mov     rdi, rbx
     +0x37f  add     rsi, r12
     +0x382  call    mldsa_polyt0_unpack
     after_mldsa_polyt0_unpack:
     +0x387  mov     rdi, rbx
     +0x38a  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_4:
     +0x38f  mov     rsi, r15
     +0x392  mov     rdi, rbx
     +0x395  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_3:
     +0x39a  mov     rdi, rbx
     +0x39d  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont_3:
     +0x3a2  mov     rdi, rbx
     +0x3a5  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_3:
     +0x3aa  mov     esi, 0x3ff00
     +0x3af  mov     rdi, rbx
     +0x3b2  call    mldsa_poly_chknorm
     loop2_test2: after_mldsa_poly_chknorm_3:
     +0x3b7  test    eax, eax
     +0x3b9  jne     join6
     loop2_next2:
     +0x3bf  mov     rdi, r13
     +0x3c2  mov     rsi, rbx
     +0x3c5  add     r14, 0x60
     +0x3c9  add     r13, 0x400
     +0x3d0  call    mldsa_poly_add
     after_mldsa_poly_add_2:
     +0x3d5  add     r12, 0x1a0
     loop2_test3:
     +0x3dc  cmp     r14, 0x300
     loop2_back:
     +0x3e3  jne     loop2
     loop2_exit1:
     +0x3e9  mov     r14, QWORD PTR [rbp-0x3618]
     +0x3f0  mov     rsi, QWORD PTR [rbp-0x3638]
     +0x3f7  mov     r12, QWORD PTR [rbp-0x3648]
     +0x3fe  mov     rdi, r14
     +0x401  call    mldsa87_pack_sig_c
     after_mldsa87_pack_sig_c:
     +0x406  mov     rdx, QWORD PTR [rbp-0x3630]
     +0x40d  mov     rcx, rbx
     +0x410  mov     rdi, r14
     +0x413  mov     rsi, QWORD PTR [rbp-0x3620]
     +0x41a  call    mldsa87_pack_sig_h
     after_mldsa87_pack_sig_h:
     +0x41f  mov     edx, eax
     join3:
     +0x421  mov     rdi, r12
     +0x424  xor     eax, eax
     +0x426  mov     ecx, 0x80
     +0x42b  rep stos QWORD PTR es:[rdi], rax
     +0x42e  mov     ecx, 0x80
     +0x433  mov     rdi, r15
     +0x436  rep stos QWORD PTR es:[rdi], rax
     +0x439  mov     rdi, QWORD PTR [rbp-0x3620]
     +0x440  mov     ecx, 0x400
     +0x445  rep stos QWORD PTR es:[rdi], rax
     +0x448  mov     rdi, QWORD PTR [rbp-0x3620]
     +0x44f  mov     rdi, QWORD PTR [rbp-0x3630]
     +0x456  mov     ecx, 0x80
     +0x45b  rep stos QWORD PTR es:[rdi], rax
     +0x45e  mov     rdi, QWORD PTR [rbp-0x3630]
     +0x465  mov     ecx, 0x80
     +0x46a  mov     rdi, rbx
     +0x46d  rep stos QWORD PTR es:[rdi], rax
     +0x470  mov     rax, QWORD PTR [rbp-0x3640]
     +0x477  pxor    xmm0, xmm0
     +0x47b  movaps  XMMWORD PTR [rax], xmm0
     +0x47e  mov     rax, QWORD PTR [rbp-0x3638]
     +0x485  movaps  XMMWORD PTR [rax], xmm0
     +0x488  movaps  XMMWORD PTR [rax+0x10], xmm0
     +0x48c  movaps  XMMWORD PTR [rax+0x20], xmm0
     +0x490  movaps  XMMWORD PTR [rax+0x30], xmm0
     +0x494  test    edx, edx
     +0x496  je      join5
     +0x498  cmp     edx, 0xffffffff
     +0x49b  jne     join4
     +0x49d  add     WORD PTR [rbp-0x3628], 0x7
     +0x4a5  movzx   eax, WORD PTR [rbp-0x3628]
     +0x4ac  cmp     ax, 0xfff7
     +0x4b0  jne     join2
     +0x4b6  mov     edx, 0xfffffffc
     join4:
     +0x4bb  mov     rbx, QWORD PTR [rbp-0x3618]
     +0x4c2  xor     eax, eax
     +0x4c4  lea     rdi, [rbx+0x8]
     +0x4c8  mov     rcx, rbx
     +0x4cb  mov     QWORD PTR [rbx], 0x0
     +0x4d2  mov     QWORD PTR [rbx+0x120b], 0x0
     +0x4dd  and     rdi, 0xfffffffffffffff8
     +0x4e1  sub     rcx, rdi
     +0x4e4  add     ecx, 0x1213
     +0x4ea  shr     ecx, 0x3
     +0x4ed  rep stos QWORD PTR es:[rdi], rax
     join5:
     +0x4f0  mov     QWORD PTR [rbp-0x35d0], 0x0
     +0x4fb  mov     rax, QWORD PTR [rbp-0x3680]
     +0x502  mov     QWORD PTR [rbp-0x35f0], 0x0
     +0x50d  mov     rax, QWORD PTR [rbp-0x3678]
     +0x514  mov     QWORD PTR [rbp-0x3610], 0x0
     +0x51f  mov     rax, QWORD PTR [rbp-0x3670]
     +0x526  mov     rdi, QWORD PTR [rbp-0x3650]
     +0x52d  xor     eax, eax
     +0x52f  mov     ecx, 0x84
     +0x534  rep stos QWORD PTR es:[rdi], rax
     +0x537  mov     rdi, QWORD PTR [rbp-0x3650]
     +0x53e  mov     rdi, QWORD PTR [rbp-0x3668]
     +0x545  mov     ecx, 0x20
     +0x54a  rep stos QWORD PTR es:[rdi], rax
     +0x54d  mov     rdi, QWORD PTR [rbp-0x3668]
     +0x554  lea     rsp, [rbp-0x30]
     +0x558  mov     eax, edx
     +0x55a  pop     rbx
     +0x55b  pop     r10
     +0x55d  pop     r12
     +0x55f  pop     r13
     +0x561  pop     r14
     +0x563  pop     r15
     +0x565  pop     rbp
     +0x566  lea     rsp, [r10-0x8]
     ret:
     +0x56a  ret
     +0x56b  nop     DWORD PTR [rax+rax*1+0x0]
     join6: loop2_exit2:
     +0x570  mov     r12, QWORD PTR [rbp-0x3648]
     join7: loop1_exit2:
     +0x577  mov     edx, 0xffffffff
     +0x57c  jmp     join3
     +0x581  movdqu  xmm1, XMMWORD PTR [r13+0x0]
     +0x587  movdqu  xmm2, XMMWORD PTR [r13+0x10]
     +0x58d  lea     rax, [rbp-0x34d0]
     +0x594  movdqu  xmm3, XMMWORD PTR [r13+0x20]
     +0x59a  movdqu  xmm4, XMMWORD PTR [r13+0x30]
     +0x5a0  mov     QWORD PTR [rbp-0x3658], rax
     +0x5a7  movaps  XMMWORD PTR [rbp-0x34d0], xmm1
     +0x5ae  movaps  XMMWORD PTR [rbp-0x34c0], xmm2
     +0x5b5  movaps  XMMWORD PTR [rbp-0x34b0], xmm3
     +0x5bc  movaps  XMMWORD PTR [rbp-0x34a0], xmm4
     +0x5c3  jmp     join1
 ***)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa87_signature_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The secret key skb at sk (4896 bytes), the message M of mlen *)
(* bytes at m and the prefix PRE of prelen bytes at pre (or, if ext is       *)
(* nonzero as a 32-bit integer, mu in the first 64 bytes at m), and the 32   *)
(* bytes RND at rnd, with MU the mu that the code uses: the result is 0,     *)
(* with the signature mld_sign_sig at sig (4627 bytes), if one of the 9361   *)
(* attempts succeeds (mld_sign_ok), and -4 with the signature zeroed         *)
(* otherwise. The last two arguments, sk and ext, are on the stack above the *)
(* return address. The function aligns the stack pointer down to a multiple  *)
(* of 32, which may lower it by up to 31 bytes, copies the return address    *)
(* there, saves seven registers (RBP, the frame pointer, and R10, which      *)
(* holds the original stack pointer, among them) and reserves 13928 bytes    *)
(* for its buffers, below which the callees use up to 1670 bytes, with their *)
(* return addresses and stack arguments: 15693 bytes of stack below the      *)
(* return address in all.                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!sig m mlen pre prelen rnd sk ext skb M PRE RND MU
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
         [(sig,4627); (word_sub stackpointer (word 15693),15693)] /\
        ALLPAIRS nonoverlapping
         [(sig,4627); (word_sub stackpointer (word 15693),15693)]
         [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
          (word pc,libmldsa_size)] /\
        nonoverlapping (sig,4627) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_signature_internal) /\
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
                memory :> bytes(word_sub stackpointer (word 15693),15693)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, ext, rho, what the C *)
(* code declassifies in each attempt (mld_sign_declass) and the stack, with  *)
(* all accesses within the arguments, the stack, the return address and the  *)
(* arguments above it and the constants of the callees, and the writes       *)
(* within the signature and the stack.                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
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
         [(sig,4627); (word_sub stackpointer (word 15693),15693)] /\
        ALLPAIRS nonoverlapping
         [(sig,4627); (word_sub stackpointer (word 15693),15693)]
         [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
          (word pc,libmldsa_size)] /\
        nonoverlapping (sig,4627) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_signature_internal) /\
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
                           pc (word_sub stackpointer (word 15693))
                           returnaddress /\
                     memaccess_inbounds e2
                      [sig,4627; m,mlen; pre,prelen; rnd,32; sk,4896;
                       word_sub stackpointer (word 15693),15693;
                       stackpointer,8; word_add stackpointer (word 8),16;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [sig,4627;
                       word_sub stackpointer (word 15693),15693]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(sig,4627);
                memory :> bytes(word_sub stackpointer (word 15693),15693)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
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
         [(sig,4627); (word_sub stackpointer (word 15693),15693)] /\
        ALLPAIRS nonoverlapping
         [(sig,4627); (word_sub stackpointer (word 15693),15693)]
         [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
          (word pc,libmldsa_size)] /\
        nonoverlapping (sig,4627) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_signature_internal) /\
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
                           pc (word_sub stackpointer (word 15693))
                           returnaddress /\
                     memaccess_inbounds e2
                      [sig,4627; m,mlen; pre,prelen; rnd,32; sk,4896;
                       word_sub stackpointer (word 15693),15693;
                       stackpointer,8; word_add stackpointer (word 8),16;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [sig,4627;
                       word_sub stackpointer (word 15693),15693]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(sig,4627);
                memory :> bytes(word_sub stackpointer (word 15693),15693)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
