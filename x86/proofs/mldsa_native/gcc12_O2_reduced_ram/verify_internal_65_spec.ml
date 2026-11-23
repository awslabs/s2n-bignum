(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the statement. This is the code for          *)
(* mldsa65_verify_internal (mld_sign_verify_internal in sign.c) from         *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 and  *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which unpacks z and   *)
(* checks its norm, computes mu (or takes it from m if ext is nonzero),      *)
(* copies rho into the structure of the matrix, whose entries are sampled    *)
(* when they are needed, the challenge from c~, and for each row computes    *)
(* w1' = UseHint(h, A z - c t1 2^d), with the row of A z computed by         *)
(* mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy, unpacking the hints *)
(* of the row, and packs it, and then compares c~ with the hash of mu and    *)
(* w1'. It zeroes its buffers at the end with REP STOSQ and 128-bit stores,  *)
(* so the direction flag must be clear, as the ABI requires on entry. It is  *)
(* verified in the whole image (see libmldsa.ml) against                     *)
(* mld_verify_internal_ok of common/mldsa_native_sign.ml, the model of the   *)
(* default configuration, using the theorems for the callees, assuming that  *)
(* the sampling of the matrix and of the challenge terminate, and shown to   *)
(* be constant time and memory safe, with events depending on the signature, *)
(* the message, the prefix and the public key, which are all public.         *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_lazy.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_unpack_z_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_chknorm_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_ntt_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_expand_lazy_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_challenge_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/unpack_pk_t1_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_shiftl_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_pointwise_montgomery_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_sub_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_reduce_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_caddq_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/sig_unpack_hints_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_use_hint_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyw1_pack_32_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_absorb_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_finalize_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_squeeze_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/H_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa65_verify_internal:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  push    QWORD PTR [r10-0x8]
       +0xd  push    rbp
       +0xe  mov     rbp, rsp
      +0x11  push    r15
      +0x13  mov     r15, rdx
      +0x16  push    r14
      +0x18  lea     rax, [rbp-0x1430]
      +0x1f  mov     r14, rcx
      +0x22  push    r13
      +0x24  mov     r13, rax
      +0x27  push    r12
      +0x29  mov     r12, rsi
      +0x2c  lea     rsi, [rdi+0x30]
      +0x30  push    r10
      +0x32  push    rbx
      +0x33  sub     rsp, 0x2900
      +0x3a  movdqu  xmm3, XMMWORD PTR [rdi]
      +0x3e  movdqu  xmm4, XMMWORD PTR [rdi+0x10]
      +0x43  mov     QWORD PTR [rbp-0x28f8], rdi
      +0x4a  movdqu  xmm5, XMMWORD PTR [rdi+0x20]
      +0x4f  mov     rdi, rax
      +0x52  mov     QWORD PTR [rbp-0x2908], r8
      +0x59  mov     QWORD PTR [rbp-0x2910], r9
      +0x60  mov     ebx, DWORD PTR [r10]
      +0x63  mov     QWORD PTR [rbp-0x2900], rax
      +0x6a  movaps  XMMWORD PTR [rbp-0x28f0], xmm3
      +0x71  movaps  XMMWORD PTR [rbp-0x28e0], xmm4
      +0x78  movaps  XMMWORD PTR [rbp-0x28d0], xmm5
      +0x7f  call    mldsa65_polyvecl_unpack_z
     after_mldsa65_polyvecl_unpack_z:
      +0x84  mov     esi, 0x7ff3c
      +0x89  mov     rdi, r13
      +0x8c  call    mldsa65_polyvecl_chknorm
     after_mldsa65_polyvecl_chknorm:
      +0x91  mov     r11, QWORD PTR [rbp-0x28f8]
      +0x98  test    eax, eax
      +0x9a  jne     +0x529
      +0xa0  mov     r13d, eax
      +0xa3  test    ebx, ebx
      +0xa5  je      join3
      +0xab  movdqu  xmm6, XMMWORD PTR [r12]
      +0xb1  movdqu  xmm7, XMMWORD PTR [r12+0x10]
      +0xb8  lea     rax, [rbp-0x1850]
      +0xbf  lea     rbx, [rbp-0x1c50]
      +0xc6  mov     QWORD PTR [rbp-0x28f8], rax
      +0xcd  lea     rax, [rbp-0x2870]
      +0xd4  movaps  XMMWORD PTR [rbp-0x2870], xmm6
      +0xdb  movdqu  xmm6, XMMWORD PTR [r12+0x20]
      +0xe2  movaps  XMMWORD PTR [rbp-0x2860], xmm7
      +0xe9  movdqu  xmm7, XMMWORD PTR [r12+0x30]
      +0xf0  mov     QWORD PTR [rbp-0x2928], rax
      +0xf7  movaps  XMMWORD PTR [rbp-0x2850], xmm6
      +0xfe  movaps  XMMWORD PTR [rbp-0x2840], xmm7
     join1:
     +0x105  mov     rdi, QWORD PTR [rbp-0x2900]
     +0x10c  mov     QWORD PTR [rbp-0x2918], r11
     +0x113  lea     r12, [rbp-0x2050]
     +0x11a  call    mldsa65_polyvecl_ntt
     after_mldsa65_polyvecl_ntt:
     +0x11f  mov     rsi, QWORD PTR [rbp-0x2910]
     +0x126  mov     rdi, QWORD PTR [rbp-0x28f8]
     +0x12d  call    mldsa65_polyvec_matrix_expand_lazy
     after_mldsa65_polyvec_matrix_expand_lazy:
     +0x132  lea     rax, [rbp-0x2450]
     +0x139  lea     r8, [rbp-0x28f0]
     +0x140  mov     r14, rax
     +0x143  mov     rdi, rax
     +0x146  mov     rsi, r8
     +0x149  mov     QWORD PTR [rbp-0x2908], rax
     +0x150  mov     QWORD PTR [rbp-0x2930], r8
     +0x157  call    mldsa65_poly_challenge
     after_mldsa65_poly_challenge:
     +0x15c  mov     rdi, r14
     +0x15f  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_1:
     +0x164  lea     rax, [rbp-0x2750]
     +0x16b  mov     QWORD PTR [rbp-0x2920], rax
     +0x172  mov     r15, rax
     loop1:
     +0x175  mov     rdx, QWORD PTR [rbp-0x2900]
     +0x17c  mov     rsi, QWORD PTR [rbp-0x28f8]
     +0x183  mov     ecx, r13d
     +0x186  mov     rdi, r12
     +0x189  call    mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy
     after_mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy:
     +0x18e  mov     rsi, QWORD PTR [rbp-0x2910]
     +0x195  mov     edx, r13d
     +0x198  mov     rdi, rbx
     +0x19b  call    mldsa65_unpack_pk_t1
     after_mldsa65_unpack_pk_t1:
     +0x1a0  mov     rdi, rbx
     +0x1a3  call    mldsa_poly_shiftl
     after_mldsa_poly_shiftl:
     +0x1a8  mov     rdi, rbx
     +0x1ab  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_2:
     +0x1b0  mov     rsi, QWORD PTR [rbp-0x2908]
     +0x1b7  mov     rdi, rbx
     +0x1ba  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery:
     +0x1bf  mov     rsi, rbx
     +0x1c2  mov     rdi, r12
     +0x1c5  call    mldsa_poly_sub
     after_mldsa_poly_sub:
     +0x1ca  mov     rdi, r12
     +0x1cd  call    mldsa_poly_reduce
     after_mldsa_poly_reduce:
     +0x1d2  mov     rdi, r12
     +0x1d5  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont:
     +0x1da  mov     rdi, r12
     +0x1dd  call    mldsa_poly_caddq
     after_mldsa_poly_caddq:
     +0x1e2  mov     rsi, QWORD PTR [rbp-0x2918]
     +0x1e9  mov     edx, r13d
     +0x1ec  mov     rdi, rbx
     +0x1ef  call    mldsa65_sig_unpack_hints
     after_mldsa65_sig_unpack_hints:
     +0x1f4  mov     r14d, eax
     loop1_test1:
     +0x1f7  test    eax, eax
     +0x1f9  jne     join4
     loop1_next1:
     +0x1ff  mov     rsi, rbx
     +0x202  mov     rdi, r12
     +0x205  add     r13d, 0x1
     +0x209  call    mldsa65_poly_use_hint
     after_mldsa65_poly_use_hint:
     +0x20e  mov     rdi, r15
     +0x211  mov     rsi, r12
     +0x214  sub     r15, 0xffffffffffffff80
     +0x218  call    mldsa_polyw1_pack_32
     loop1_test2: after_mldsa_polyw1_pack_32:
     +0x21d  cmp     r13d, 0x6
     loop1_back:
     +0x221  jne     loop1
     loop1_exit1:
     +0x227  mov     r8, QWORD PTR [rbp-0x2930]
     +0x22e  lea     r13, [rbp-0x2820]
     +0x235  lea     r15, [rbp-0x28b0]
     +0x23c  mov     rdi, r13
     +0x23f  mov     QWORD PTR [rbp-0x2910], r8
     +0x246  call    mldsa_shake256_init
     after_mldsa_shake256_init_1:
     +0x24b  mov     rsi, QWORD PTR [rbp-0x2928]
     +0x252  mov     rdi, r13
     +0x255  mov     edx, 0x40
     +0x25a  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_1:
     +0x25f  mov     rsi, QWORD PTR [rbp-0x2920]
     +0x266  mov     edx, 0x300
     +0x26b  mov     rdi, r13
     +0x26e  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_2:
     +0x273  mov     rdi, r13
     +0x276  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize_1:
     +0x27b  mov     rdx, r13
     +0x27e  mov     esi, 0x30
     +0x283  mov     rdi, r15
     +0x286  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze_1:
     +0x28b  mov     rdi, r13
     +0x28e  call    mldsa_shake256_release
     after_mldsa_shake256_release_1:
     +0x293  xor     eax, eax
     +0x295  mov     rdi, r13
     +0x298  mov     ecx, 0x1a
     +0x29d  rep stos QWORD PTR es:[rdi], rax
     +0x2a0  pxor    xmm1, xmm1
     +0x2a4  mov     r8, QWORD PTR [rbp-0x2910]
     +0x2ab  movdqa  xmm0, xmm1
     loop2:
     +0x2af  movdqa  xmm2, XMMWORD PTR [r8+rax*1]
     +0x2b5  pxor    xmm2, XMMWORD PTR [r15+rax*1]
     +0x2bb  add     rax, 0x10
     +0x2bf  por     xmm0, xmm2
     +0x2c3  pxor    xmm1, xmm2
     loop2_test:
     +0x2c7  cmp     rax, 0x30
     loop2_back:
     +0x2cb  jne     loop2
     loop2_exit:
     +0x2cd  movdqa  xmm2, xmm1
     +0x2d1  psrldq  xmm2, 0x8
     +0x2d6  pxor    xmm1, xmm2
     +0x2da  movdqa  xmm2, xmm1
     +0x2de  psrldq  xmm2, 0x4
     +0x2e3  pxor    xmm1, xmm2
     +0x2e7  movdqa  xmm2, xmm1
     +0x2eb  psrldq  xmm2, 0x2
     +0x2f0  pxor    xmm1, xmm2
     +0x2f4  movdqa  xmm2, xmm1
     +0x2f8  psrldq  xmm2, 0x1
     +0x2fd  pxor    xmm1, xmm2
     +0x301  movd    edx, xmm1
     +0x305  movdqa  xmm1, xmm0
     +0x309  psrldq  xmm1, 0x8
     +0x30e  por     xmm0, xmm1
     +0x312  movdqa  xmm1, xmm0
     +0x316  psrldq  xmm1, 0x4
     +0x31b  por     xmm0, xmm1
     +0x31f  movdqa  xmm1, xmm0
     +0x323  psrldq  xmm1, 0x2
     +0x328  por     xmm0, xmm1
     +0x32c  movdqa  xmm1, xmm0
     +0x330  psrldq  xmm1, 0x1
     +0x335  por     xmm0, xmm1
     +0x339  movd    eax, xmm0
     +0x33d  movzx   eax, al
     +0x340  neg     rax
     +0x343  sar     rax, 0x20
     +0x347  xor     eax, edx
     +0x349  cmp     al, dl
     +0x34b  jne     join5
     join2:
     +0x351  xor     eax, eax
     +0x353  mov     rdi, rbx
     +0x356  mov     ecx, 0x80
     +0x35b  rep stos QWORD PTR es:[rdi], rax
     +0x35e  mov     ecx, 0x80
     +0x363  mov     rdi, r12
     +0x366  rep stos QWORD PTR es:[rdi], rax
     +0x369  mov     rdi, QWORD PTR [rbp-0x28f8]
     +0x370  mov     ecx, 0x84
     +0x375  rep stos QWORD PTR es:[rdi], rax
     +0x378  mov     rdi, QWORD PTR [rbp-0x28f8]
     +0x37f  mov     rdi, QWORD PTR [rbp-0x2908]
     +0x386  mov     ecx, 0x80
     +0x38b  rep stos QWORD PTR es:[rdi], rax
     +0x38e  mov     rdi, QWORD PTR [rbp-0x2908]
     +0x395  mov     rdi, QWORD PTR [rbp-0x2900]
     +0x39c  mov     ecx, 0x280
     +0x3a1  rep stos QWORD PTR es:[rdi], rax
     +0x3a4  mov     rdi, QWORD PTR [rbp-0x2900]
     +0x3ab  pxor    xmm0, xmm0
     +0x3af  movaps  XMMWORD PTR [rbp-0x28b0], xmm0
     +0x3b6  movaps  XMMWORD PTR [rbp-0x28a0], xmm0
     +0x3bd  movaps  XMMWORD PTR [rbp-0x2890], xmm0
     +0x3c4  movaps  XMMWORD PTR [rbp-0x28f0], xmm0
     +0x3cb  movaps  XMMWORD PTR [rbp-0x28e0], xmm0
     +0x3d2  movaps  XMMWORD PTR [rbp-0x28d0], xmm0
     +0x3d9  mov     rdx, QWORD PTR [rbp-0x2928]
     +0x3e0  movaps  XMMWORD PTR [rbp-0x2870], xmm0
     +0x3e7  movaps  XMMWORD PTR [rbp-0x2860], xmm0
     +0x3ee  movaps  XMMWORD PTR [rbp-0x2850], xmm0
     +0x3f5  movaps  XMMWORD PTR [rbp-0x2840], xmm0
     +0x3fc  mov     rdi, QWORD PTR [rbp-0x2920]
     +0x403  mov     ecx, 0x60
     +0x408  rep stos QWORD PTR es:[rdi], rax
     +0x40b  mov     rdi, QWORD PTR [rbp-0x2920]
     +0x412  lea     rsp, [rbp-0x30]
     +0x416  mov     eax, r14d
     +0x419  pop     rbx
     +0x41a  pop     r10
     +0x41c  pop     r12
     +0x41e  pop     r13
     +0x420  pop     r14
     +0x422  pop     r15
     +0x424  pop     rbp
     +0x425  lea     rsp, [r10-0x8]
     ret:
     +0x429  ret
     +0x42a  nop     WORD PTR [rax+rax*1+0x0]
     join3:
     +0x430  lea     rax, [rbp-0x1850]
     +0x437  mov     QWORD PTR [rbp-0x2918], r11
     +0x43e  mov     rdi, rax
     +0x441  mov     rbx, rax
     +0x444  call    mldsa_shake256_init
     after_mldsa_shake256_init_2:
     +0x449  mov     rsi, QWORD PTR [rbp-0x2910]
     +0x450  mov     edx, 0x7a0
     +0x455  mov     rdi, rbx
     +0x458  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_3:
     +0x45d  mov     rdi, rbx
     +0x460  mov     QWORD PTR [rbp-0x28f8], rbx
     +0x467  lea     rbx, [rbp-0x1c50]
     +0x46e  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize_2:
     +0x473  mov     rdx, QWORD PTR [rbp-0x28f8]
     +0x47a  mov     esi, 0x40
     +0x47f  mov     rdi, rbx
     +0x482  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze_2:
     +0x487  mov     rdi, QWORD PTR [rbp-0x28f8]
     +0x48e  call    mldsa_shake256_release
     after_mldsa_shake256_release_2:
     +0x493  mov     rdi, QWORD PTR [rbp-0x28f8]
     +0x49a  xor     eax, eax
     +0x49c  mov     ecx, 0x1a
     +0x4a1  rep stos QWORD PTR es:[rdi], rax
     +0x4a4  mov     rdi, QWORD PTR [rbp-0x28f8]
     +0x4ab  mov     ecx, 0x40
     +0x4b0  mov     r8, r14
     +0x4b3  mov     rdx, rbx
     +0x4b6  mov     esi, 0x40
     +0x4bb  lea     rax, [rbp-0x2870]
     +0x4c2  mov     r9, QWORD PTR [rbp-0x2908]
     +0x4c9  mov     QWORD PTR [rbp-0x2928], rax
     +0x4d0  mov     rdi, rax
     +0x4d3  push    r15
     +0x4d5  push    r12
     +0x4d7  call    mld_H65
     after_mld_H65:
     +0x4dc  pxor    xmm0, xmm0
     +0x4e0  movaps  XMMWORD PTR [rbp-0x1c50], xmm0
     +0x4e7  movaps  XMMWORD PTR [rbp-0x1c40], xmm0
     +0x4ee  movaps  XMMWORD PTR [rbp-0x1c30], xmm0
     +0x4f5  movaps  XMMWORD PTR [rbp-0x1c20], xmm0
     +0x4fc  pop     rax
     +0x4fd  mov     r11, QWORD PTR [rbp-0x2918]
     +0x504  pop     rdx
     +0x505  jmp     join1
     +0x50a  nop     WORD PTR [rax+rax*1+0x0]
     join4: loop1_exit2:
     +0x510  mov     r8, QWORD PTR [rbp-0x2930]
     +0x517  lea     r15, [rbp-0x28b0]
     join5:
     +0x51e  mov     r14d, 0xfffffffa
     +0x524  jmp     join2
     +0x529  lea     rax, [rbp-0x1850]
     +0x530  lea     rbx, [rbp-0x1c50]
     +0x537  mov     QWORD PTR [rbp-0x28f8], rax
     +0x53e  lea     rax, [rbp-0x2870]
     +0x545  lea     r8, [rbp-0x28f0]
     +0x54c  mov     QWORD PTR [rbp-0x2928], rax
     +0x553  lea     rax, [rbp-0x2450]
     +0x55a  lea     r12, [rbp-0x2050]
     +0x561  mov     QWORD PTR [rbp-0x2908], rax
     +0x568  lea     rax, [rbp-0x2750]
     +0x56f  lea     r15, [rbp-0x28b0]
     +0x576  mov     QWORD PTR [rbp-0x2920], rax
     +0x57d  jmp     join5
 ***)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa65_verify_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The signature sigb at sig (3309 bytes), the message M of     *)
(* mlen bytes at m and the prefix PRE of prelen bytes at pre (or, if ext is  *)
(* nonzero as a 32-bit integer, mu in the first 64 bytes at m), the public   *)
(* key pkb at pk (1952 bytes): the result is 0 if the signature is accepted, *)
(* and -6 otherwise. ext, the seventh argument, is on the stack above the    *)
(* return address, as a 64-bit word whose low 32 bits the code reads. The    *)
(* function keeps the stack pointer of the entry in R10, lowers RSP by up to *)
(* 31 bytes to align it to 32 bytes, copies the return address there and     *)
(* saves RBP, the frame pointer, and six more registers, reserves the stack  *)
(* for its buffers, below which the callees use theirs: 12269 bytes of stack *)
(* below the return address in all.                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!sig m mlen pre prelen pk ext sigb pkb M PRE pc stackpointer
   returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
        (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
        mld_matrix_terminates 6 5 (num_of_bytelist(list_of_seq pkb 32)) /\
        mld_poly_challenge_terminates 49 48
         (num_of_bytelist(list_of_seq sigb 48)) /\
        ALL (nonoverlapping (word_sub stackpointer (word 12269),12269))
            [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
             (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_verify_internal) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  ext /\
                  (read DF s <=> false) /\
                  (!j. j < 3309
                       ==> read(memory :> bytes8(word_add sig (word j))) s =
                           sigb j) /\
                  read (memory :> bytes(m,mlen)) s = M /\
                  read (memory :> bytes(pre,prelen)) s = PRE /\
                  (!j. j < 1952
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           pkb j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                  (if mld_verify_internal_ok 6 5 48
                         mld_polyz_unpack_19 640 524092
                         mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49
                         sigb pkb
                         (if word_zx ext = (word 0:int32)
                          then mld_verify_mu 1952 pkb prelen PRE mlen M
                          else M MOD 2 EXP 512)
                   then word 0 else word 4294967290))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 12269),12269)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the flag ext, the    *)
(* signature, the message, the prefix and the public key, all public, and    *)
(* the stack, with all accesses within the arguments, the stack, the return  *)
(* address and ext above it and the constants of the callees, and the writes *)
(* within the stack.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e sig m mlen pre prelen pk ext sigb pkb M PRE pc
            stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
        (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
        mld_matrix_terminates 6 5 (num_of_bytelist(list_of_seq pkb 32)) /\
        mld_poly_challenge_terminates 49 48
         (num_of_bytelist(list_of_seq sigb 48)) /\
        ALL (nonoverlapping (word_sub stackpointer (word 12269),12269))
            [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
             (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_verify_internal) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  ext /\
                  (read DF s <=> false) /\
                  (!j. j < 3309
                       ==> read(memory :> bytes8(word_add sig (word j))) s =
                           sigb j) /\
                  read (memory :> bytes(m,mlen)) s = M /\
                  read (memory :> bytes(pre,prelen)) s = PRE /\
                  (!j. j < 1952
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           pkb j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                  (if mld_verify_internal_ok 6 5 48
                         mld_polyz_unpack_19 640 524092
                         mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49
                         sigb pkb
                         (if word_zx ext = (word 0:int32)
                          then mld_verify_mu 1952 pkb prelen PRE mlen M
                          else M MOD 2 EXP 512)
                   then word 0 else word 4294967290) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events sig m mlen pre prelen pk ext sigb pkb M PRE
                            pc (word_sub stackpointer (word 12269))
                            returnaddress /\
                     memaccess_inbounds e2
                      [sig,3309; m,mlen; pre,prelen; pk,1952;
                       word_sub stackpointer (word 12269),12269;
                       stackpointer,8; word_add stackpointer (word 8),8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [word_sub stackpointer (word 12269),12269]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 12269),12269)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e sig m mlen pre prelen pk ext sigb pkb M PRE pc
            stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
        (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
        mld_matrix_terminates 6 5 (num_of_bytelist(list_of_seq pkb 32)) /\
        mld_poly_challenge_terminates 49 48
         (num_of_bytelist(list_of_seq sigb 48)) /\
        ALL (nonoverlapping (word_sub stackpointer (word 12269),12269))
            [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
             (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_verify_internal) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  ext /\
                  (read DF s <=> false) /\
                  (!j. j < 3309
                       ==> read(memory :> bytes8(word_add sig (word j))) s =
                           sigb j) /\
                  read (memory :> bytes(m,mlen)) s = M /\
                  read (memory :> bytes(pre,prelen)) s = PRE /\
                  (!j. j < 1952
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           pkb j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events sig m mlen pre prelen pk ext sigb pkb M PRE
                            pc (word_sub stackpointer (word 12269))
                            returnaddress /\
                     memaccess_inbounds e2
                      [sig,3309; m,mlen; pre,prelen; pk,1952;
                       word_sub stackpointer (word 12269),12269;
                       stackpointer,8; word_add stackpointer (word 8),8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [word_sub stackpointer (word 12269),12269]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 12269),12269)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
