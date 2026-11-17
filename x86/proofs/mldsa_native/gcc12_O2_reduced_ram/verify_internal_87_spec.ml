(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the statement. This is the code for          *)
(* mldsa87_verify_internal (mld_sign_verify_internal in sign.c) from         *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 and  *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which unpacks z and   *)
(* checks its norm, computes mu (or takes it from m if ext is nonzero),      *)
(* copies rho into the structure of the matrix, whose entries are sampled    *)
(* when they are needed, the challenge from c~, and for each row computes    *)
(* w1' = UseHint(h, A z - c t1 2^d), with the row of A z computed by         *)
(* mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy, unpacking the hints *)
(* of the row, and packs it, and then compares c~ with the hash of mu and    *)
(* w1'. It zeroes its buffers at the end with REP STOSQ and 128-bit stores,  *)
(* so the direction flag must be clear, as the ABI requires on entry. It is  *)
(* verified in the whole image (see libmldsa.ml) against                     *)
(* mld_verify_internal_ok of common/mldsa_native_sign.ml, the model of the   *)
(* default configuration, using the theorems for the callees and             *)
(* MLD_VERIFY_W1_LAZY_87 of lazy_spec.ml (the rows of w1' are those of the   *)
(* default configuration once the norm of z is checked), assuming that the   *)
(* sampling of the matrix and of the challenge terminate, and shown to be    *)
(* constant time and memory safe, with events depending on the signature,    *)
(* the message, the prefix and the public key, which are all public.         *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec_lazy.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_unpack_z_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_chknorm_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_ntt_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_expand_lazy_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_challenge_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/unpack_pk_t1_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_shiftl_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_pointwise_montgomery_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_sub_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_reduce_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_caddq_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/sig_unpack_hints_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_use_hint_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyw1_pack_32_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_absorb_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_finalize_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_squeeze_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/H_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/lazy_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa87_verify_internal:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  push    QWORD PTR [r10-0x8]
       +0xd  push    rbp
       +0xe  mov     rbp, rsp
      +0x11  push    r15
      +0x13  mov     r15, rsi
      +0x16  lea     rsi, [rdi+0x40]
      +0x1a  push    r14
      +0x1c  lea     rax, [rbp-0x1c30]
      +0x23  mov     r14, r8
      +0x26  push    r13
      +0x28  mov     r13, rax
      +0x2b  push    r12
      +0x2d  mov     r12, rdx
      +0x30  push    r10
      +0x32  push    rbx
      +0x33  sub     rsp, 0x3200
      +0x3a  movdqu  xmm3, XMMWORD PTR [rdi]
      +0x3e  mov     ebx, DWORD PTR [r10]
      +0x41  mov     QWORD PTR [rbp-0x31f8], rdi
      +0x48  movdqu  xmm4, XMMWORD PTR [rdi+0x10]
      +0x4d  movdqu  xmm5, XMMWORD PTR [rdi+0x20]
      +0x52  mov     QWORD PTR [rbp-0x3208], rcx
      +0x59  movdqu  xmm6, XMMWORD PTR [rdi+0x30]
      +0x5e  mov     rdi, rax
      +0x61  mov     QWORD PTR [rbp-0x3210], r9
      +0x68  mov     QWORD PTR [rbp-0x3200], rax
      +0x6f  movaps  XMMWORD PTR [rbp-0x31b0], xmm3
      +0x76  movaps  XMMWORD PTR [rbp-0x31a0], xmm4
      +0x7d  movaps  XMMWORD PTR [rbp-0x3190], xmm5
      +0x84  movaps  XMMWORD PTR [rbp-0x3180], xmm6
      +0x8b  call    mldsa87_polyvecl_unpack_z
     after_mldsa87_polyvecl_unpack_z:
      +0x90  mov     esi, 0x7ff88
      +0x95  mov     rdi, r13
      +0x98  call    mldsa87_polyvecl_chknorm
     after_mldsa87_polyvecl_chknorm:
      +0x9d  mov     r11, QWORD PTR [rbp-0x31f8]
      +0xa4  test    eax, eax
      +0xa6  jne     +0x541
      +0xac  mov     r13d, eax
      +0xaf  test    ebx, ebx
      +0xb1  je      join3
      +0xb7  movdqu  xmm7, XMMWORD PTR [r15]
      +0xbc  lea     rax, [rbp-0x2050]
      +0xc3  movdqu  xmm3, XMMWORD PTR [r15+0x20]
      +0xc9  lea     rbx, [rbp-0x2450]
      +0xd0  mov     QWORD PTR [rbp-0x31f8], rax
      +0xd7  lea     rax, [rbp-0x31f0]
      +0xde  movdqu  xmm4, XMMWORD PTR [r15+0x30]
      +0xe4  movaps  XMMWORD PTR [rbp-0x31f0], xmm7
      +0xeb  movdqu  xmm7, XMMWORD PTR [r15+0x10]
      +0xf1  mov     QWORD PTR [rbp-0x3228], rax
      +0xf8  movaps  XMMWORD PTR [rbp-0x31e0], xmm7
      +0xff  movaps  XMMWORD PTR [rbp-0x31d0], xmm3
     +0x106  movaps  XMMWORD PTR [rbp-0x31c0], xmm4
     join1:
     +0x10d  mov     rdi, QWORD PTR [rbp-0x3200]
     +0x114  mov     QWORD PTR [rbp-0x3218], r11
     +0x11b  lea     r12, [rbp-0x2850]
     +0x122  call    mldsa87_polyvecl_ntt
     after_mldsa87_polyvecl_ntt:
     +0x127  mov     rsi, QWORD PTR [rbp-0x3210]
     +0x12e  mov     rdi, QWORD PTR [rbp-0x31f8]
     +0x135  call    mldsa87_polyvec_matrix_expand_lazy
     after_mldsa87_polyvec_matrix_expand_lazy:
     +0x13a  lea     rax, [rbp-0x2c50]
     +0x141  lea     r9, [rbp-0x31b0]
     +0x148  mov     r15, rax
     +0x14b  mov     rdi, rax
     +0x14e  mov     rsi, r9
     +0x151  mov     QWORD PTR [rbp-0x3208], rax
     +0x158  mov     QWORD PTR [rbp-0x3230], r9
     +0x15f  call    mldsa87_poly_challenge
     after_mldsa87_poly_challenge:
     +0x164  mov     rdi, r15
     +0x167  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_1:
     +0x16c  lea     rax, [rbp-0x3050]
     +0x173  mov     QWORD PTR [rbp-0x3220], rax
     +0x17a  mov     r14, rax
     +0x17d  nop     DWORD PTR [rax]
     loop1:
     +0x180  mov     rdx, QWORD PTR [rbp-0x3200]
     +0x187  mov     rsi, QWORD PTR [rbp-0x31f8]
     +0x18e  mov     ecx, r13d
     +0x191  mov     rdi, r12
     +0x194  call    mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy
     after_mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy:
     +0x199  mov     rsi, QWORD PTR [rbp-0x3210]
     +0x1a0  mov     edx, r13d
     +0x1a3  mov     rdi, rbx
     +0x1a6  call    mldsa87_unpack_pk_t1
     after_mldsa87_unpack_pk_t1:
     +0x1ab  mov     rdi, rbx
     +0x1ae  call    mldsa_poly_shiftl
     after_mldsa_poly_shiftl:
     +0x1b3  mov     rdi, rbx
     +0x1b6  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_2:
     +0x1bb  mov     rsi, QWORD PTR [rbp-0x3208]
     +0x1c2  mov     rdi, rbx
     +0x1c5  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery:
     +0x1ca  mov     rsi, rbx
     +0x1cd  mov     rdi, r12
     +0x1d0  call    mldsa_poly_sub
     after_mldsa_poly_sub:
     +0x1d5  mov     rdi, r12
     +0x1d8  call    mldsa_poly_reduce
     after_mldsa_poly_reduce:
     +0x1dd  mov     rdi, r12
     +0x1e0  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont:
     +0x1e5  mov     rdi, r12
     +0x1e8  call    mldsa_poly_caddq
     after_mldsa_poly_caddq:
     +0x1ed  mov     rsi, QWORD PTR [rbp-0x3218]
     +0x1f4  mov     edx, r13d
     +0x1f7  mov     rdi, rbx
     +0x1fa  call    mldsa87_sig_unpack_hints
     after_mldsa87_sig_unpack_hints:
     +0x1ff  mov     r15d, eax
     loop1_test1:
     +0x202  test    eax, eax
     +0x204  jne     join4
     loop1_next1:
     +0x20a  mov     rsi, rbx
     +0x20d  mov     rdi, r12
     +0x210  add     r13d, 0x1
     +0x214  call    mldsa87_poly_use_hint
     after_mldsa87_poly_use_hint:
     +0x219  mov     rdi, r14
     +0x21c  mov     rsi, r12
     +0x21f  sub     r14, 0xffffffffffffff80
     +0x223  call    mldsa_polyw1_pack_32
     loop1_test2: after_mldsa_polyw1_pack_32:
     +0x228  cmp     r13d, 0x8
     loop1_back:
     +0x22c  jne     loop1
     loop1_exit1:
     +0x232  mov     r9, QWORD PTR [rbp-0x3230]
     +0x239  lea     r13, [rbp-0x3120]
     +0x240  lea     r14, [rbp-0x3170]
     +0x247  mov     rdi, r13
     +0x24a  mov     QWORD PTR [rbp-0x3210], r9
     +0x251  call    mldsa_shake256_init
     after_mldsa_shake256_init_1:
     +0x256  mov     rsi, QWORD PTR [rbp-0x3228]
     +0x25d  mov     rdi, r13
     +0x260  mov     edx, 0x40
     +0x265  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_1:
     +0x26a  mov     rsi, QWORD PTR [rbp-0x3220]
     +0x271  mov     edx, 0x400
     +0x276  mov     rdi, r13
     +0x279  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_2:
     +0x27e  mov     rdi, r13
     +0x281  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize_1:
     +0x286  mov     rdx, r13
     +0x289  mov     esi, 0x40
     +0x28e  mov     rdi, r14
     +0x291  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze_1:
     +0x296  mov     rdi, r13
     +0x299  call    mldsa_shake256_release
     after_mldsa_shake256_release_1:
     +0x29e  xor     eax, eax
     +0x2a0  mov     rdi, r13
     +0x2a3  mov     ecx, 0x1a
     +0x2a8  rep stos QWORD PTR es:[rdi], rax
     +0x2ab  pxor    xmm1, xmm1
     +0x2af  mov     r9, QWORD PTR [rbp-0x3210]
     +0x2b6  movdqa  xmm0, xmm1
     loop2:
     +0x2ba  movdqa  xmm2, XMMWORD PTR [r9+rax*1]
     +0x2c0  pxor    xmm2, XMMWORD PTR [r14+rax*1]
     +0x2c6  add     rax, 0x10
     +0x2ca  por     xmm0, xmm2
     +0x2ce  pxor    xmm1, xmm2
     loop2_test:
     +0x2d2  cmp     rax, 0x40
     loop2_back:
     +0x2d6  jne     loop2
     loop2_exit:
     +0x2d8  movdqa  xmm2, xmm1
     +0x2dc  psrldq  xmm2, 0x8
     +0x2e1  pxor    xmm1, xmm2
     +0x2e5  movdqa  xmm2, xmm1
     +0x2e9  psrldq  xmm2, 0x4
     +0x2ee  pxor    xmm1, xmm2
     +0x2f2  movdqa  xmm2, xmm1
     +0x2f6  psrldq  xmm2, 0x2
     +0x2fb  pxor    xmm1, xmm2
     +0x2ff  movdqa  xmm2, xmm1
     +0x303  psrldq  xmm2, 0x1
     +0x308  pxor    xmm1, xmm2
     +0x30c  movd    edx, xmm1
     +0x310  movdqa  xmm1, xmm0
     +0x314  psrldq  xmm1, 0x8
     +0x319  por     xmm0, xmm1
     +0x31d  movdqa  xmm1, xmm0
     +0x321  psrldq  xmm1, 0x4
     +0x326  por     xmm0, xmm1
     +0x32a  movdqa  xmm1, xmm0
     +0x32e  psrldq  xmm1, 0x2
     +0x333  por     xmm0, xmm1
     +0x337  movdqa  xmm1, xmm0
     +0x33b  psrldq  xmm1, 0x1
     +0x340  por     xmm0, xmm1
     +0x344  movd    eax, xmm0
     +0x348  movzx   eax, al
     +0x34b  neg     rax
     +0x34e  sar     rax, 0x20
     +0x352  xor     eax, edx
     +0x354  cmp     al, dl
     +0x356  jne     join5
     join2:
     +0x35c  xor     eax, eax
     +0x35e  mov     rdi, rbx
     +0x361  mov     ecx, 0x80
     +0x366  rep stos QWORD PTR es:[rdi], rax
     +0x369  mov     ecx, 0x80
     +0x36e  mov     rdi, r12
     +0x371  rep stos QWORD PTR es:[rdi], rax
     +0x374  mov     rdi, QWORD PTR [rbp-0x31f8]
     +0x37b  mov     ecx, 0x84
     +0x380  rep stos QWORD PTR es:[rdi], rax
     +0x383  mov     rdi, QWORD PTR [rbp-0x31f8]
     +0x38a  mov     rdi, QWORD PTR [rbp-0x3208]
     +0x391  mov     ecx, 0x80
     +0x396  rep stos QWORD PTR es:[rdi], rax
     +0x399  mov     rdi, QWORD PTR [rbp-0x3208]
     +0x3a0  mov     rdi, QWORD PTR [rbp-0x3200]
     +0x3a7  mov     ecx, 0x380
     +0x3ac  rep stos QWORD PTR es:[rdi], rax
     +0x3af  mov     rdi, QWORD PTR [rbp-0x3200]
     +0x3b6  pxor    xmm0, xmm0
     +0x3ba  movaps  XMMWORD PTR [rbp-0x3170], xmm0
     +0x3c1  movaps  XMMWORD PTR [rbp-0x3160], xmm0
     +0x3c8  movaps  XMMWORD PTR [rbp-0x3150], xmm0
     +0x3cf  movaps  XMMWORD PTR [rbp-0x3140], xmm0
     +0x3d6  movaps  XMMWORD PTR [rbp-0x31b0], xmm0
     +0x3dd  movaps  XMMWORD PTR [rbp-0x31a0], xmm0
     +0x3e4  movaps  XMMWORD PTR [rbp-0x3190], xmm0
     +0x3eb  movaps  XMMWORD PTR [rbp-0x3180], xmm0
     +0x3f2  mov     rcx, QWORD PTR [rbp-0x3228]
     +0x3f9  movaps  XMMWORD PTR [rbp-0x31f0], xmm0
     +0x400  movaps  XMMWORD PTR [rbp-0x31e0], xmm0
     +0x407  movaps  XMMWORD PTR [rbp-0x31d0], xmm0
     +0x40e  movaps  XMMWORD PTR [rbp-0x31c0], xmm0
     +0x415  mov     rdi, QWORD PTR [rbp-0x3220]
     +0x41c  mov     ecx, 0x80
     +0x421  rep stos QWORD PTR es:[rdi], rax
     +0x424  mov     rdi, QWORD PTR [rbp-0x3220]
     +0x42b  lea     rsp, [rbp-0x30]
     +0x42f  mov     eax, r15d
     +0x432  pop     rbx
     +0x433  pop     r10
     +0x435  pop     r12
     +0x437  pop     r13
     +0x439  pop     r14
     +0x43b  pop     r15
     +0x43d  pop     rbp
     +0x43e  lea     rsp, [r10-0x8]
     ret:
     +0x442  ret
     +0x443  nop     DWORD PTR [rax+rax*1+0x0]
     join3:
     +0x448  lea     rax, [rbp-0x2050]
     +0x44f  mov     QWORD PTR [rbp-0x3218], r11
     +0x456  mov     rdi, rax
     +0x459  mov     rbx, rax
     +0x45c  call    mldsa_shake256_init
     after_mldsa_shake256_init_2:
     +0x461  mov     rsi, QWORD PTR [rbp-0x3210]
     +0x468  mov     edx, 0xa20
     +0x46d  mov     rdi, rbx
     +0x470  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_3:
     +0x475  mov     rdi, rbx
     +0x478  mov     QWORD PTR [rbp-0x31f8], rbx
     +0x47f  lea     rbx, [rbp-0x2450]
     +0x486  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize_2:
     +0x48b  mov     rdx, QWORD PTR [rbp-0x31f8]
     +0x492  mov     esi, 0x40
     +0x497  mov     rdi, rbx
     +0x49a  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze_2:
     +0x49f  mov     rdi, QWORD PTR [rbp-0x31f8]
     +0x4a6  call    mldsa_shake256_release
     after_mldsa_shake256_release_2:
     +0x4ab  mov     rdi, QWORD PTR [rbp-0x31f8]
     +0x4b2  xor     eax, eax
     +0x4b4  mov     ecx, 0x1a
     +0x4b9  rep stos QWORD PTR es:[rdi], rax
     +0x4bc  mov     rdi, QWORD PTR [rbp-0x31f8]
     +0x4c3  lea     rax, [rbp-0x31f0]
     +0x4ca  mov     r9, r15
     +0x4cd  mov     r8, r14
     +0x4d0  mov     rsi, rbx
     +0x4d3  sub     rsp, 0x8
     +0x4d7  mov     QWORD PTR [rbp-0x3228], rax
     +0x4de  mov     edx, 0x40
     +0x4e3  mov     rdi, rax
     +0x4e6  push    r12
     +0x4e8  mov     rcx, QWORD PTR [rbp-0x3208]
     +0x4ef  call    mld_H87
     after_mld_H87:
     +0x4f4  pxor    xmm0, xmm0
     +0x4f8  movaps  XMMWORD PTR [rbp-0x2450], xmm0
     +0x4ff  movaps  XMMWORD PTR [rbp-0x2440], xmm0
     +0x506  movaps  XMMWORD PTR [rbp-0x2430], xmm0
     +0x50d  movaps  XMMWORD PTR [rbp-0x2420], xmm0
     +0x514  pop     rax
     +0x515  mov     r11, QWORD PTR [rbp-0x3218]
     +0x51c  pop     rdx
     +0x51d  jmp     join1
     +0x522  nop     WORD PTR [rax+rax*1+0x0]
     join4: loop1_exit2:
     +0x528  mov     r9, QWORD PTR [rbp-0x3230]
     +0x52f  lea     r14, [rbp-0x3170]
     join5:
     +0x536  mov     r15d, 0xfffffffa
     +0x53c  jmp     join2
     +0x541  lea     rax, [rbp-0x2050]
     +0x548  lea     rbx, [rbp-0x2450]
     +0x54f  mov     QWORD PTR [rbp-0x31f8], rax
     +0x556  lea     rax, [rbp-0x31f0]
     +0x55d  lea     r9, [rbp-0x31b0]
     +0x564  mov     QWORD PTR [rbp-0x3228], rax
     +0x56b  lea     rax, [rbp-0x2c50]
     +0x572  lea     r12, [rbp-0x2850]
     +0x579  mov     QWORD PTR [rbp-0x3208], rax
     +0x580  lea     rax, [rbp-0x3050]
     +0x587  lea     r14, [rbp-0x3170]
     +0x58e  mov     QWORD PTR [rbp-0x3220], rax
     +0x595  jmp     join5
 ***)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa87_verify_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The signature sigb at sig (4627 bytes), the message M of     *)
(* mlen bytes at m and the prefix PRE of prelen bytes at pre (or, if ext is  *)
(* nonzero as a 32-bit integer, mu in the first 64 bytes at m), the public   *)
(* key pkb at pk (2592 bytes): the result is 0 if the signature is accepted, *)
(* and -6 otherwise. ext, the seventh argument, is on the stack above the    *)
(* return address, as a 64-bit word whose low 32 bits the code reads. The    *)
(* function keeps the stack pointer of the entry in R10, lowers RSP by up to *)
(* 31 bytes to align it to 32 bytes, copies the return address there and     *)
(* saves RBP, the frame pointer, and six more registers, reserves the stack  *)
(* for its buffers, below which the callees use theirs: 14573 bytes of stack *)
(* below the return address in all.                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!sig m mlen pre prelen pk ext sigb pkb M PRE pc stackpointer
   returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
        (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
        mld_matrix_terminates 8 7 (num_of_bytelist(list_of_seq pkb 32)) /\
        mld_poly_challenge_terminates 60 64
         (num_of_bytelist(list_of_seq sigb 64)) /\
        ALL (nonoverlapping (word_sub stackpointer (word 14573),14573))
            [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
             (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_verify_internal) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  ext /\
                  (read DF s <=> false) /\
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
                         (if word_zx ext = (word 0:int32)
                          then mld_verify_mu 2592 pkb prelen PRE mlen M
                          else M MOD 2 EXP 512)
                   then word 0 else word 4294967290))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 14573),14573)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the flag ext, the    *)
(* signature, the message, the prefix and the public key, all public, and    *)
(* the stack, with all accesses within the arguments, the stack, the return  *)
(* address and ext above it and the constants of the callees, and the writes *)
(* within the stack.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e sig m mlen pre prelen pk ext sigb pkb M PRE pc
            stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
        (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
        mld_matrix_terminates 8 7 (num_of_bytelist(list_of_seq pkb 32)) /\
        mld_poly_challenge_terminates 60 64
         (num_of_bytelist(list_of_seq sigb 64)) /\
        ALL (nonoverlapping (word_sub stackpointer (word 14573),14573))
            [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
             (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_verify_internal) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  ext /\
                  (read DF s <=> false) /\
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
                         (if word_zx ext = (word 0:int32)
                          then mld_verify_mu 2592 pkb prelen PRE mlen M
                          else M MOD 2 EXP 512)
                   then word 0 else word 4294967290) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events sig m mlen pre prelen pk ext sigb pkb M PRE
                            pc (word_sub stackpointer (word 14573))
                            returnaddress /\
                     memaccess_inbounds e2
                      [sig,4627; m,mlen; pre,prelen; pk,2592;
                       word_sub stackpointer (word 14573),14573;
                       stackpointer,8; word_add stackpointer (word 8),8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [word_sub stackpointer (word 14573),14573]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 14573),14573)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e sig m mlen pre prelen pk ext sigb pkb M PRE pc
            stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
        (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
        mld_matrix_terminates 8 7 (num_of_bytelist(list_of_seq pkb 32)) /\
        mld_poly_challenge_terminates 60 64
         (num_of_bytelist(list_of_seq sigb 64)) /\
        ALL (nonoverlapping (word_sub stackpointer (word 14573),14573))
            [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
             (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_verify_internal) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  ext /\
                  (read DF s <=> false) /\
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
                     e2 = f_events sig m mlen pre prelen pk ext sigb pkb M PRE
                            pc (word_sub stackpointer (word 14573))
                            returnaddress /\
                     memaccess_inbounds e2
                      [sig,4627; m,mlen; pre,prelen; pk,2592;
                       word_sub stackpointer (word 14573),14573;
                       stackpointer,8; word_add stackpointer (word 8),8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [word_sub stackpointer (word 14573),14573]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 14573),14573)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
