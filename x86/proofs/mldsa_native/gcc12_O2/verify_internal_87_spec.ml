(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the statement. This is the code for          *)
(* mldsa87_verify_internal (mld_sign_verify_internal in sign.c) from         *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which unpacks z and checks its norm, computes mu *)
(* (or takes it from m if ext is nonzero), expands the matrix from rho, the  *)
(* challenge from c~, and for each row computes w1' = UseHint(h, A z - c t1  *)
(* 2^d), unpacking the hints of the row, and packs it, and then compares c~  *)
(* with the hash of mu and w1'. It zeroes its buffers at the end with        *)
(* memsets that gcc inlines with REP STOSQ, so the direction flag must be    *)
(* clear, as the ABI requires on entry, and the matrix with memset, which it *)
(* calls through the PLT. It is verified in the whole image (see             *)
(* libmldsa.ml) against mld_verify_internal_ok of                            *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and the   *)
(* contract memset_full_contract of utils/mldsa_native_libc.ml, assuming     *)
(* that the expansion of the matrix and the sampling of the challenge        *)
(* terminate, and shown to be constant time and memory safe, with events     *)
(* depending on the signature, the message, the prefix and the public key,   *)
(* which are all public.                                                     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_unpack_z_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_chknorm_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_ntt_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvec_matrix_expand_eager_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_challenge_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvec_matrix_pointwise_montgomery_row_eager_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/unpack_pk_t1_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_shiftl_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_pointwise_montgomery_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_sub_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_reduce_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_caddq_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/sig_unpack_hints_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_use_hint_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyw1_pack_32_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_absorb_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/H_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa87_verify_internal:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  push    QWORD PTR [r10-0x8]
       +0xd  push    rbp
       +0xe  mov     rbp, rsp
      +0x11  push    r15
      +0x13  mov     r15, rcx
      +0x16  push    r14
      +0x18  lea     rax, [rbp-0xfc30]
      +0x1f  mov     r14, rsi
      +0x22  lea     rsi, [rdi+0x40]
      +0x26  push    r13
      +0x28  mov     r13, rax
      +0x2b  push    r12
      +0x2d  mov     r12, rdx
      +0x30  push    r10
      +0x32  push    rbx
      +0x33  sub     rsp, 0x10de0
      +0x3a  movdqu  xmm3, XMMWORD PTR [rdi]
      +0x3e  mov     ebx, DWORD PTR [r10]
      +0x41  mov     QWORD PTR [rbp-0x10dd8], rdi
      +0x48  movdqu  xmm4, XMMWORD PTR [rdi+0x10]
      +0x4d  movdqu  xmm5, XMMWORD PTR [rdi+0x20]
      +0x52  mov     QWORD PTR [rbp-0x10de8], r8
      +0x59  movdqu  xmm6, XMMWORD PTR [rdi+0x30]
      +0x5e  mov     rdi, rax
      +0x61  mov     QWORD PTR [rbp-0x10df0], r9
      +0x68  mov     QWORD PTR [rbp-0x10de0], rax
      +0x6f  movaps  XMMWORD PTR [rbp-0x10d90], xmm3
      +0x76  movaps  XMMWORD PTR [rbp-0x10d80], xmm4
      +0x7d  movaps  XMMWORD PTR [rbp-0x10d70], xmm5
      +0x84  movaps  XMMWORD PTR [rbp-0x10d60], xmm6
      +0x8b  call    mldsa87_polyvecl_unpack_z
     after_mldsa87_polyvecl_unpack_z:
      +0x90  mov     esi, 0x7ff88
      +0x95  mov     rdi, r13
      +0x98  call    mldsa87_polyvecl_chknorm
     after_mldsa87_polyvecl_chknorm:
      +0x9d  mov     r11, QWORD PTR [rbp-0x10dd8]
      +0xa4  test    eax, eax
      +0xa6  jne     +0x559
      +0xac  mov     r13d, eax
      +0xaf  test    ebx, ebx
      +0xb1  je      join3
      +0xb7  movdqu  xmm7, XMMWORD PTR [r14]
      +0xbc  lea     rax, [rbp-0xe030]
      +0xc3  movdqu  xmm3, XMMWORD PTR [r14+0x20]
      +0xc9  lea     rbx, [rbp-0x10030]
      +0xd0  mov     QWORD PTR [rbp-0x10dd8], rax
      +0xd7  lea     rax, [rbp-0x10dd0]
      +0xde  movdqu  xmm4, XMMWORD PTR [r14+0x30]
      +0xe4  movaps  XMMWORD PTR [rbp-0x10dd0], xmm7
      +0xeb  movdqu  xmm7, XMMWORD PTR [r14+0x10]
      +0xf1  mov     QWORD PTR [rbp-0x10e08], rax
      +0xf8  movaps  XMMWORD PTR [rbp-0x10dc0], xmm7
      +0xff  movaps  XMMWORD PTR [rbp-0x10db0], xmm3
     +0x106  movaps  XMMWORD PTR [rbp-0x10da0], xmm4
     join1:
     +0x10d  mov     rdi, QWORD PTR [rbp-0x10de0]
     +0x114  mov     QWORD PTR [rbp-0x10df8], r11
     +0x11b  lea     r12, [rbp-0x10430]
     +0x122  call    mldsa87_polyvecl_ntt
     after_mldsa87_polyvecl_ntt:
     +0x127  mov     rsi, QWORD PTR [rbp-0x10df0]
     +0x12e  mov     rdi, QWORD PTR [rbp-0x10dd8]
     +0x135  call    mldsa87_polyvec_matrix_expand_eager
     after_mldsa87_polyvec_matrix_expand_eager:
     +0x13a  lea     rax, [rbp-0x10830]
     +0x141  lea     r8, [rbp-0x10d90]
     +0x148  mov     r14, rax
     +0x14b  mov     rdi, rax
     +0x14e  mov     rsi, r8
     +0x151  mov     QWORD PTR [rbp-0x10de8], rax
     +0x158  mov     QWORD PTR [rbp-0x10e10], r8
     +0x15f  call    mldsa87_poly_challenge
     after_mldsa87_poly_challenge:
     +0x164  mov     rdi, r14
     +0x167  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_1:
     +0x16c  lea     rax, [rbp-0x10c30]
     +0x173  mov     QWORD PTR [rbp-0x10e00], rax
     +0x17a  mov     r15, rax
     +0x17d  nop     DWORD PTR [rax]
     loop1:
     +0x180  mov     rdx, QWORD PTR [rbp-0x10de0]
     +0x187  mov     rsi, QWORD PTR [rbp-0x10dd8]
     +0x18e  mov     ecx, r13d
     +0x191  mov     rdi, r12
     +0x194  call    mldsa87_polyvec_matrix_pointwise_montgomery_row_eager
     after_mldsa87_polyvec_matrix_pointwise_montgomery_row_eager:
     +0x199  mov     rsi, QWORD PTR [rbp-0x10df0]
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
     +0x1bb  mov     rsi, QWORD PTR [rbp-0x10de8]
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
     +0x1ed  mov     rsi, QWORD PTR [rbp-0x10df8]
     +0x1f4  mov     edx, r13d
     +0x1f7  mov     rdi, rbx
     +0x1fa  call    mldsa87_sig_unpack_hints
     after_mldsa87_sig_unpack_hints:
     +0x1ff  mov     r14d, eax
     loop1_test1:
     +0x202  test    eax, eax
     +0x204  jne     join4
     loop1_next1:
     +0x20a  mov     rsi, rbx
     +0x20d  mov     rdi, r12
     +0x210  add     r13d, 0x1
     +0x214  call    mldsa87_poly_use_hint
     after_mldsa87_poly_use_hint:
     +0x219  mov     rdi, r15
     +0x21c  mov     rsi, r12
     +0x21f  sub     r15, 0xffffffffffffff80
     +0x223  call    mldsa_polyw1_pack_32
     loop1_test2: after_mldsa_polyw1_pack_32:
     +0x228  cmp     r13d, 0x8
     loop1_back:
     +0x22c  jne     loop1
     loop1_exit1:
     +0x232  mov     r8, QWORD PTR [rbp-0x10e10]
     +0x239  lea     r13, [rbp-0x10d00]
     +0x240  lea     r15, [rbp-0x10d50]
     +0x247  mov     rdi, r13
     +0x24a  mov     QWORD PTR [rbp-0x10df0], r8
     +0x251  call    mldsa_shake256_init
     after_mldsa_shake256_init_1:
     +0x256  mov     rsi, QWORD PTR [rbp-0x10e08]
     +0x25d  mov     rdi, r13
     +0x260  mov     edx, 0x40
     +0x265  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_1:
     +0x26a  mov     rsi, QWORD PTR [rbp-0x10e00]
     +0x271  mov     edx, 0x400
     +0x276  mov     rdi, r13
     +0x279  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_2:
     +0x27e  mov     rdi, r13
     +0x281  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize_1:
     +0x286  mov     rdx, r13
     +0x289  mov     esi, 0x40
     +0x28e  mov     rdi, r15
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
     +0x2af  mov     r8, QWORD PTR [rbp-0x10df0]
     +0x2b6  movdqa  xmm0, xmm1
     loop2:
     +0x2ba  movdqa  xmm2, XMMWORD PTR [r8+rax*1]
     +0x2c0  pxor    xmm2, XMMWORD PTR [r15+rax*1]
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
     +0x35c  xor     r13d, r13d
     +0x35f  mov     rdi, rbx
     +0x362  mov     ecx, 0x80
     +0x367  mov     QWORD PTR [rbp-0x10df0], r8
     +0x36e  mov     rax, r13
     +0x371  rep stos QWORD PTR es:[rdi], rax
     +0x374  mov     ecx, 0x80
     +0x379  mov     rdi, r12
     +0x37c  rep stos QWORD PTR es:[rdi], rax
     +0x37f  mov     rbx, QWORD PTR [rbp-0x10dd8]
     +0x386  mov     edx, 0xe000
     +0x38b  xor     esi, esi
     +0x38d  mov     rdi, rbx
     +0x390  call    memset
     after_memset:
     +0x395  mov     rdi, QWORD PTR [rbp-0x10de8]
     +0x39c  mov     rax, r13
     +0x39f  mov     ecx, 0x80
     +0x3a4  rep stos QWORD PTR es:[rdi], rax
     +0x3a7  mov     rdi, QWORD PTR [rbp-0x10de8]
     +0x3ae  mov     rdi, QWORD PTR [rbp-0x10de0]
     +0x3b5  mov     ecx, 0x380
     +0x3ba  rep stos QWORD PTR es:[rdi], rax
     +0x3bd  mov     rdi, QWORD PTR [rbp-0x10de0]
     +0x3c4  pxor    xmm0, xmm0
     +0x3c8  movaps  XMMWORD PTR [rbp-0x10d50], xmm0
     +0x3cf  movaps  XMMWORD PTR [rbp-0x10d40], xmm0
     +0x3d6  movaps  XMMWORD PTR [rbp-0x10d30], xmm0
     +0x3dd  movaps  XMMWORD PTR [rbp-0x10d20], xmm0
     +0x3e4  mov     r8, QWORD PTR [rbp-0x10df0]
     +0x3eb  movaps  XMMWORD PTR [rbp-0x10d90], xmm0
     +0x3f2  movaps  XMMWORD PTR [rbp-0x10d80], xmm0
     +0x3f9  movaps  XMMWORD PTR [rbp-0x10d70], xmm0
     +0x400  movaps  XMMWORD PTR [rbp-0x10d60], xmm0
     +0x407  mov     rax, QWORD PTR [rbp-0x10e08]
     +0x40e  movaps  XMMWORD PTR [rbp-0x10dd0], xmm0
     +0x415  movaps  XMMWORD PTR [rbp-0x10dc0], xmm0
     +0x41c  movaps  XMMWORD PTR [rbp-0x10db0], xmm0
     +0x423  movaps  XMMWORD PTR [rbp-0x10da0], xmm0
     +0x42a  mov     rdi, QWORD PTR [rbp-0x10e00]
     +0x431  mov     rax, r13
     +0x434  mov     ecx, 0x80
     +0x439  rep stos QWORD PTR es:[rdi], rax
     +0x43c  mov     rdi, QWORD PTR [rbp-0x10e00]
     +0x443  lea     rsp, [rbp-0x30]
     +0x447  mov     eax, r14d
     +0x44a  pop     rbx
     +0x44b  pop     r10
     +0x44d  pop     r12
     +0x44f  pop     r13
     +0x451  pop     r14
     +0x453  pop     r15
     +0x455  pop     rbp
     +0x456  lea     rsp, [r10-0x8]
     ret:
     +0x45a  ret
     +0x45b  nop     DWORD PTR [rax+rax*1+0x0]
     join3:
     +0x460  lea     rax, [rbp-0xe030]
     +0x467  mov     QWORD PTR [rbp-0x10df8], r11
     +0x46e  mov     rdi, rax
     +0x471  mov     rbx, rax
     +0x474  call    mldsa_shake256_init
     after_mldsa_shake256_init_2:
     +0x479  mov     rsi, QWORD PTR [rbp-0x10df0]
     +0x480  mov     edx, 0xa20
     +0x485  mov     rdi, rbx
     +0x488  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_3:
     +0x48d  mov     rdi, rbx
     +0x490  mov     QWORD PTR [rbp-0x10dd8], rbx
     +0x497  lea     rbx, [rbp-0x10030]
     +0x49e  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize_2:
     +0x4a3  mov     rdx, QWORD PTR [rbp-0x10dd8]
     +0x4aa  mov     esi, 0x40
     +0x4af  mov     rdi, rbx
     +0x4b2  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze_2:
     +0x4b7  mov     rdi, QWORD PTR [rbp-0x10dd8]
     +0x4be  call    mldsa_shake256_release
     after_mldsa_shake256_release_2:
     +0x4c3  mov     rdi, QWORD PTR [rbp-0x10dd8]
     +0x4ca  xor     eax, eax
     +0x4cc  mov     ecx, 0x1a
     +0x4d1  rep stos QWORD PTR es:[rdi], rax
     +0x4d4  mov     rdi, QWORD PTR [rbp-0x10dd8]
     +0x4db  lea     rax, [rbp-0x10dd0]
     +0x4e2  mov     r9, r14
     +0x4e5  mov     rcx, r15
     +0x4e8  mov     rsi, rbx
     +0x4eb  sub     rsp, 0x8
     +0x4ef  mov     QWORD PTR [rbp-0x10e08], rax
     +0x4f6  mov     edx, 0x40
     +0x4fb  mov     rdi, rax
     +0x4fe  push    r12
     +0x500  mov     r8, QWORD PTR [rbp-0x10de8]
     +0x507  call    mld_H87
     after_mld_H87:
     +0x50c  pxor    xmm0, xmm0
     +0x510  movaps  XMMWORD PTR [rbp-0x10030], xmm0
     +0x517  movaps  XMMWORD PTR [rbp-0x10020], xmm0
     +0x51e  movaps  XMMWORD PTR [rbp-0x10010], xmm0
     +0x525  movaps  XMMWORD PTR [rbp-0x10000], xmm0
     +0x52c  pop     rax
     +0x52d  mov     r11, QWORD PTR [rbp-0x10df8]
     +0x534  pop     rdx
     +0x535  jmp     join1
     +0x53a  nop     WORD PTR [rax+rax*1+0x0]
     join4: loop1_exit2:
     +0x540  mov     r8, QWORD PTR [rbp-0x10e10]
     +0x547  lea     r15, [rbp-0x10d50]
     join5:
     +0x54e  mov     r14d, 0xfffffffa
     +0x554  jmp     join2
     +0x559  lea     rax, [rbp-0xe030]
     +0x560  lea     rbx, [rbp-0x10030]
     +0x567  mov     QWORD PTR [rbp-0x10dd8], rax
     +0x56e  lea     rax, [rbp-0x10dd0]
     +0x575  lea     r8, [rbp-0x10d90]
     +0x57c  mov     QWORD PTR [rbp-0x10e08], rax
     +0x583  lea     rax, [rbp-0x10830]
     +0x58a  lea     r12, [rbp-0x10430]
     +0x591  mov     QWORD PTR [rbp-0x10de8], rax
     +0x598  lea     rax, [rbp-0x10c30]
     +0x59f  lea     r15, [rbp-0x10d50]
     +0x5a6  mov     QWORD PTR [rbp-0x10e00], rax
     +0x5ad  jmp     join5

    plt_memset:
       +0x0  jmp     QWORD PTR [rip+0xefc2]
                     // got_memset
       +0x6  push    0x2
       +0xb  jmp     <.plt>
 ***)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_verify_internal"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The signature sigb at sig  *)
(* (4627 bytes), the message M of mlen bytes at m and the prefix PRE of      *)
(* prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu in the *)
(* first 64 bytes at m), the public key pkb at pk (2592 bytes): the result   *)
(* is 0 if the signature is accepted, and -6 otherwise. ext, the seventh     *)
(* argument, is on the stack above the return address, as a 64-bit word      *)
(* whose low 32 bits the code reads. The function keeps the stack pointer of *)
(* the entry in R10, lowers RSP by up to 31 bytes to align it to 32 bytes,   *)
(* copies the return address there and saves RBP, the frame pointer, and six *)
(* more registers, reserves the stack for its buffers, below which the       *)
(* callees use theirs: 74349 bytes of stack below the return address in all. *)
(* The GOT entry of memset, which the stub reads, and the region (ea,el)     *)
(* that memset may read are apart from the stack.                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !sig m mlen pre prelen pk ext sigb pkb M PRE pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 8 7 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 60 64
           (num_of_bytelist(list_of_seq sigb 64)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74349),74349))
              [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
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
                           (if word_zx ext = (word 0:int32)
                            then mld_verify_mu 2592 pkb prelen PRE mlen M
                            else M MOD 2 EXP 512)
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74349),74349)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the flag ext, the    *)
(* signature, the message, the prefix and the public key, all public, the    *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the return address and ext above it, the GOT entry of memset,  *)
(* the region (ea,el) that memset may read and the constants of the callees, *)
(* and the writes within the stack.                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk ext sigb pkb M PRE pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 8 7 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 60 64
           (num_of_bytelist(list_of_seq sigb 64)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74349),74349))
              [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
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
                           (if word_zx ext = (word 0:int32)
                            then mld_verify_mu 2592 pkb prelen PRE mlen M
                            else M MOD 2 EXP 512)
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen pk ext sigb pkb M PRE
                              mf pc (word_sub stackpointer (word 74349))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; pk,2592;
                         word_sub stackpointer (word 74349),74349;
                         stackpointer,8; word_add stackpointer (word 8),8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16]
                        [word_sub stackpointer (word 74349),74349]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74349),74349)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk ext sigb pkb M PRE pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 8 7 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 60 64
           (num_of_bytelist(list_of_seq sigb 64)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74349),74349))
              [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
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
                       e2 = f_events sig m mlen pre prelen pk ext sigb pkb M PRE
                              mf pc (word_sub stackpointer (word 74349))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; pk,2592;
                         word_sub stackpointer (word 74349),74349;
                         stackpointer,8; word_add stackpointer (word 8),8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16]
                        [word_sub stackpointer (word 74349),74349]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74349),74349)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
