(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the statement. This is the code for          *)
(* mldsa44_verify_internal (mld_sign_verify_internal in sign.c) from         *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 and  *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which unpacks z and   *)
(* checks its norm, computes mu (or takes it from m if ext is nonzero),      *)
(* copies rho into the structure of the matrix, whose entries are sampled    *)
(* when they are needed, the challenge from c~, and for each row computes    *)
(* w1' = UseHint(h, A z - c t1 2^d), with the row of A z computed by         *)
(* mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy, unpacking the hints *)
(* of the row, and packs it, and then compares c~ with the hash of mu and    *)
(* w1'. It zeroes its buffers at the end with REP STOSQ and 128-bit stores,  *)
(* so the direction flag must be clear, as the ABI requires on entry. It is  *)
(* verified in the whole image (see libmldsa.ml) against                     *)
(* mld_verify_internal_ok of common/mldsa_native_sign.ml, the model of the   *)
(* default configuration, using the theorems for the callees and             *)
(* MLD_VERIFY_W1_LAZY_44 of lazy_spec.ml (the rows of w1' are those of the   *)
(* default configuration once the norm of z is checked), assuming that the   *)
(* sampling of the matrix and of the challenge terminate, and shown to be    *)
(* constant time and memory safe, with events depending on the signature,    *)
(* the message, the prefix and the public key, which are all public.         *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec_lazy.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_unpack_z_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_chknorm_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_ntt_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_expand_lazy_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_challenge_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/unpack_pk_t1_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_shiftl_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_pointwise_montgomery_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_sub_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_reduce_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_caddq_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/sig_unpack_hints_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_use_hint_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyw1_pack_88_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_absorb_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_finalize_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_squeeze_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/H_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/lazy_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_verify_internal:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  push    QWORD PTR [r10-0x8]
       +0xd  push    rbp
       +0xe  mov     rbp, rsp
      +0x11  push    r15
      +0x13  mov     r15, rdx
      +0x16  push    r14
      +0x18  lea     rax, [rbp-0x1030]
      +0x1f  mov     r14, rdi
      +0x22  push    r13
      +0x24  mov     r13, rax
      +0x27  push    r12
      +0x29  mov     r12, rsi
      +0x2c  lea     rsi, [rdi+0x20]
      +0x30  push    r10
      +0x32  push    rbx
      +0x33  sub     rsp, 0x24c0
      +0x3a  movdqu  xmm3, XMMWORD PTR [rdi]
      +0x3e  movdqu  xmm4, XMMWORD PTR [rdi+0x10]
      +0x43  mov     rdi, rax
      +0x46  mov     QWORD PTR [rbp-0x24c8], rcx
      +0x4d  mov     ebx, DWORD PTR [r10]
      +0x50  mov     QWORD PTR [rbp-0x24d8], r8
      +0x57  mov     QWORD PTR [rbp-0x24d0], r9
      +0x5e  mov     QWORD PTR [rbp-0x24c0], rax
      +0x65  movaps  XMMWORD PTR [rbp-0x24b0], xmm3
      +0x6c  movaps  XMMWORD PTR [rbp-0x24a0], xmm4
      +0x73  call    mldsa44_polyvecl_unpack_z
     after_mldsa44_polyvecl_unpack_z:
      +0x78  mov     esi, 0x1ffb2
      +0x7d  mov     rdi, r13
      +0x80  call    mldsa44_polyvecl_chknorm
     after_mldsa44_polyvecl_chknorm:
      +0x85  test    eax, eax
      +0x87  jne     +0x4f2
      +0x8d  mov     r13d, eax
      +0x90  test    ebx, ebx
      +0x92  je      join3
      +0x98  movdqu  xmm5, XMMWORD PTR [r12]
      +0x9e  lea     rax, [rbp-0x1450]
      +0xa5  movdqu  xmm6, XMMWORD PTR [r12+0x10]
      +0xac  lea     rbx, [rbp-0x1850]
      +0xb3  mov     QWORD PTR [rbp-0x24b8], rax
      +0xba  lea     rax, [rbp-0x2470]
      +0xc1  movdqu  xmm7, XMMWORD PTR [r12+0x20]
      +0xc8  movaps  XMMWORD PTR [rbp-0x2470], xmm5
      +0xcf  movdqu  xmm5, XMMWORD PTR [r12+0x30]
      +0xd6  mov     QWORD PTR [rbp-0x24e8], rax
      +0xdd  movaps  XMMWORD PTR [rbp-0x2460], xmm6
      +0xe4  movaps  XMMWORD PTR [rbp-0x2450], xmm7
      +0xeb  movaps  XMMWORD PTR [rbp-0x2440], xmm5
     join1:
      +0xf2  mov     rdi, QWORD PTR [rbp-0x24c0]
      +0xf9  lea     r12, [rbp-0x1c50]
     +0x100  call    mldsa44_polyvecl_ntt
     after_mldsa44_polyvecl_ntt:
     +0x105  mov     rsi, QWORD PTR [rbp-0x24d0]
     +0x10c  mov     rdi, QWORD PTR [rbp-0x24b8]
     +0x113  call    mldsa44_polyvec_matrix_expand_lazy
     after_mldsa44_polyvec_matrix_expand_lazy:
     +0x118  lea     rax, [rbp-0x2050]
     +0x11f  lea     rsi, [rbp-0x24b0]
     +0x126  mov     r15, rax
     +0x129  mov     rdi, rax
     +0x12c  mov     QWORD PTR [rbp-0x24c8], rax
     +0x133  mov     QWORD PTR [rbp-0x24f0], rsi
     +0x13a  call    mldsa44_poly_challenge
     after_mldsa44_poly_challenge:
     +0x13f  mov     rdi, r15
     +0x142  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_1:
     +0x147  lea     rax, [rbp-0x2350]
     +0x14e  mov     QWORD PTR [rbp-0x24d8], r14
     +0x155  mov     QWORD PTR [rbp-0x24e0], rax
     +0x15c  mov     r15, rax
     loop1:
     +0x15f  mov     rdx, QWORD PTR [rbp-0x24c0]
     +0x166  mov     rsi, QWORD PTR [rbp-0x24b8]
     +0x16d  mov     ecx, r13d
     +0x170  mov     rdi, r12
     +0x173  call    mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy
     after_mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy:
     +0x178  mov     rsi, QWORD PTR [rbp-0x24d0]
     +0x17f  mov     edx, r13d
     +0x182  mov     rdi, rbx
     +0x185  call    mldsa44_unpack_pk_t1
     after_mldsa44_unpack_pk_t1:
     +0x18a  mov     rdi, rbx
     +0x18d  call    mldsa_poly_shiftl
     after_mldsa_poly_shiftl:
     +0x192  mov     rdi, rbx
     +0x195  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_2:
     +0x19a  mov     rsi, QWORD PTR [rbp-0x24c8]
     +0x1a1  mov     rdi, rbx
     +0x1a4  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery:
     +0x1a9  mov     rsi, rbx
     +0x1ac  mov     rdi, r12
     +0x1af  call    mldsa_poly_sub
     after_mldsa_poly_sub:
     +0x1b4  mov     rdi, r12
     +0x1b7  call    mldsa_poly_reduce
     after_mldsa_poly_reduce:
     +0x1bc  mov     rdi, r12
     +0x1bf  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont:
     +0x1c4  mov     rdi, r12
     +0x1c7  call    mldsa_poly_caddq
     after_mldsa_poly_caddq:
     +0x1cc  mov     rsi, QWORD PTR [rbp-0x24d8]
     +0x1d3  mov     edx, r13d
     +0x1d6  mov     rdi, rbx
     +0x1d9  call    mldsa44_sig_unpack_hints
     after_mldsa44_sig_unpack_hints:
     +0x1de  mov     r14d, eax
     loop1_test1:
     +0x1e1  test    eax, eax
     +0x1e3  jne     join4
     loop1_next1:
     +0x1e9  mov     rsi, rbx
     +0x1ec  mov     rdi, r12
     +0x1ef  add     r13d, 0x1
     +0x1f3  call    mldsa44_poly_use_hint
     after_mldsa44_poly_use_hint:
     +0x1f8  mov     rdi, r15
     +0x1fb  mov     rsi, r12
     +0x1fe  add     r15, 0xc0
     +0x205  call    mldsa_polyw1_pack_88
     loop1_test2: after_mldsa_polyw1_pack_88:
     +0x20a  cmp     r13d, 0x4
     loop1_back:
     +0x20e  jne     loop1
     loop1_exit1:
     +0x214  lea     r13, [rbp-0x2420]
     +0x21b  lea     r15, [rbp-0x2490]
     +0x222  mov     rdi, r13
     +0x225  call    mldsa_shake256_init
     after_mldsa_shake256_init_1:
     +0x22a  mov     rsi, QWORD PTR [rbp-0x24e8]
     +0x231  mov     rdi, r13
     +0x234  mov     edx, 0x40
     +0x239  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_1:
     +0x23e  mov     rsi, QWORD PTR [rbp-0x24e0]
     +0x245  mov     edx, 0x300
     +0x24a  mov     rdi, r13
     +0x24d  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_2:
     +0x252  mov     rdi, r13
     +0x255  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize_1:
     +0x25a  mov     rdx, r13
     +0x25d  mov     esi, 0x20
     +0x262  mov     rdi, r15
     +0x265  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze_1:
     +0x26a  mov     rdi, r13
     +0x26d  call    mldsa_shake256_release
     after_mldsa_shake256_release_1:
     +0x272  xor     eax, eax
     +0x274  mov     rdi, r13
     +0x277  mov     ecx, 0x1a
     +0x27c  rep stos QWORD PTR es:[rdi], rax
     +0x27f  movdqa  xmm1, XMMWORD PTR [rbp-0x24b0]
     +0x287  movdqa  xmm2, XMMWORD PTR [rbp-0x24a0]
     +0x28f  pxor    xmm1, XMMWORD PTR [rbp-0x2490]
     +0x297  pxor    xmm2, XMMWORD PTR [rbp-0x2480]
     +0x29f  movdqa  xmm0, xmm1
     +0x2a3  pxor    xmm1, xmm2
     +0x2a7  por     xmm0, xmm2
     +0x2ab  movdqa  xmm2, xmm1
     +0x2af  psrldq  xmm2, 0x8
     +0x2b4  pxor    xmm1, xmm2
     +0x2b8  movdqa  xmm2, xmm1
     +0x2bc  psrldq  xmm2, 0x4
     +0x2c1  pxor    xmm1, xmm2
     +0x2c5  movdqa  xmm2, xmm1
     +0x2c9  psrldq  xmm2, 0x2
     +0x2ce  pxor    xmm1, xmm2
     +0x2d2  movdqa  xmm2, xmm1
     +0x2d6  psrldq  xmm2, 0x1
     +0x2db  pxor    xmm1, xmm2
     +0x2df  movd    edx, xmm1
     +0x2e3  movdqa  xmm1, xmm0
     +0x2e7  psrldq  xmm1, 0x8
     +0x2ec  por     xmm0, xmm1
     +0x2f0  movdqa  xmm1, xmm0
     +0x2f4  psrldq  xmm1, 0x4
     +0x2f9  por     xmm0, xmm1
     +0x2fd  movdqa  xmm1, xmm0
     +0x301  psrldq  xmm1, 0x2
     +0x306  por     xmm0, xmm1
     +0x30a  movdqa  xmm1, xmm0
     +0x30e  psrldq  xmm1, 0x1
     +0x313  por     xmm0, xmm1
     +0x317  movd    eax, xmm0
     +0x31b  movzx   eax, al
     +0x31e  neg     rax
     +0x321  sar     rax, 0x20
     +0x325  xor     eax, edx
     +0x327  cmp     al, dl
     +0x329  jne     join5
     join2:
     +0x32f  xor     eax, eax
     +0x331  mov     rdi, rbx
     +0x334  mov     ecx, 0x80
     +0x339  rep stos QWORD PTR es:[rdi], rax
     +0x33c  mov     ecx, 0x80
     +0x341  mov     rdi, r12
     +0x344  rep stos QWORD PTR es:[rdi], rax
     +0x347  mov     rdi, QWORD PTR [rbp-0x24b8]
     +0x34e  mov     ecx, 0x84
     +0x353  rep stos QWORD PTR es:[rdi], rax
     +0x356  mov     rdi, QWORD PTR [rbp-0x24b8]
     +0x35d  mov     rdi, QWORD PTR [rbp-0x24c8]
     +0x364  mov     ecx, 0x80
     +0x369  rep stos QWORD PTR es:[rdi], rax
     +0x36c  mov     rdi, QWORD PTR [rbp-0x24c8]
     +0x373  mov     rdi, QWORD PTR [rbp-0x24c0]
     +0x37a  mov     ecx, 0x200
     +0x37f  rep stos QWORD PTR es:[rdi], rax
     +0x382  mov     rdi, QWORD PTR [rbp-0x24c0]
     +0x389  pxor    xmm0, xmm0
     +0x38d  movaps  XMMWORD PTR [rbp-0x2490], xmm0
     +0x394  movaps  XMMWORD PTR [rbp-0x2480], xmm0
     +0x39b  mov     rdx, QWORD PTR [rbp-0x24f0]
     +0x3a2  movaps  XMMWORD PTR [rbp-0x24b0], xmm0
     +0x3a9  movaps  XMMWORD PTR [rbp-0x24a0], xmm0
     +0x3b0  mov     rdx, QWORD PTR [rbp-0x24e8]
     +0x3b7  movaps  XMMWORD PTR [rbp-0x2470], xmm0
     +0x3be  movaps  XMMWORD PTR [rbp-0x2460], xmm0
     +0x3c5  movaps  XMMWORD PTR [rbp-0x2450], xmm0
     +0x3cc  movaps  XMMWORD PTR [rbp-0x2440], xmm0
     +0x3d3  mov     rdi, QWORD PTR [rbp-0x24e0]
     +0x3da  mov     ecx, 0x60
     +0x3df  rep stos QWORD PTR es:[rdi], rax
     +0x3e2  mov     rdi, QWORD PTR [rbp-0x24e0]
     +0x3e9  lea     rsp, [rbp-0x30]
     +0x3ed  mov     eax, r14d
     +0x3f0  pop     rbx
     +0x3f1  pop     r10
     +0x3f3  pop     r12
     +0x3f5  pop     r13
     +0x3f7  pop     r14
     +0x3f9  pop     r15
     +0x3fb  pop     rbp
     +0x3fc  lea     rsp, [r10-0x8]
     ret:
     +0x400  ret
     +0x401  nop     DWORD PTR [rax+0x0]
     join3:
     +0x408  lea     rax, [rbp-0x1450]
     +0x40f  mov     rdi, rax
     +0x412  mov     rbx, rax
     +0x415  call    mldsa_shake256_init
     after_mldsa_shake256_init_2:
     +0x41a  mov     rsi, QWORD PTR [rbp-0x24d0]
     +0x421  mov     edx, 0x520
     +0x426  mov     rdi, rbx
     +0x429  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_3:
     +0x42e  mov     rdi, rbx
     +0x431  mov     QWORD PTR [rbp-0x24b8], rbx
     +0x438  lea     rbx, [rbp-0x1850]
     +0x43f  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize_2:
     +0x444  mov     rdx, QWORD PTR [rbp-0x24b8]
     +0x44b  mov     esi, 0x40
     +0x450  mov     rdi, rbx
     +0x453  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze_2:
     +0x458  mov     rdi, QWORD PTR [rbp-0x24b8]
     +0x45f  call    mldsa_shake256_release
     after_mldsa_shake256_release_2:
     +0x464  mov     rdi, QWORD PTR [rbp-0x24b8]
     +0x46b  xor     eax, eax
     +0x46d  mov     ecx, 0x1a
     +0x472  rep stos QWORD PTR es:[rdi], rax
     +0x475  mov     rdi, QWORD PTR [rbp-0x24b8]
     +0x47c  lea     rax, [rbp-0x2470]
     +0x483  mov     r9, QWORD PTR [rbp-0x24d8]
     +0x48a  mov     ecx, 0x40
     +0x48f  mov     rdx, rbx
     +0x492  mov     QWORD PTR [rbp-0x24e8], rax
     +0x499  mov     r8, QWORD PTR [rbp-0x24c8]
     +0x4a0  mov     esi, 0x40
     +0x4a5  mov     rdi, rax
     +0x4a8  push    r15
     +0x4aa  push    r12
     +0x4ac  call    mld_H44
     after_mld_H44:
     +0x4b1  pxor    xmm0, xmm0
     +0x4b5  movaps  XMMWORD PTR [rbp-0x1850], xmm0
     +0x4bc  movaps  XMMWORD PTR [rbp-0x1840], xmm0
     +0x4c3  movaps  XMMWORD PTR [rbp-0x1830], xmm0
     +0x4ca  movaps  XMMWORD PTR [rbp-0x1820], xmm0
     +0x4d1  pop     rax
     +0x4d2  pop     rdx
     +0x4d3  jmp     join1
     +0x4d8  nop     DWORD PTR [rax+rax*1+0x0]
     join4: loop1_exit2:
     +0x4e0  lea     r15, [rbp-0x2490]
     join5:
     +0x4e7  mov     r14d, 0xfffffffa
     +0x4ed  jmp     join2
     +0x4f2  lea     rax, [rbp-0x1450]
     +0x4f9  lea     rbx, [rbp-0x1850]
     +0x500  mov     QWORD PTR [rbp-0x24b8], rax
     +0x507  lea     rax, [rbp-0x2470]
     +0x50e  lea     r12, [rbp-0x1c50]
     +0x515  mov     QWORD PTR [rbp-0x24e8], rax
     +0x51c  lea     rax, [rbp-0x24b0]
     +0x523  lea     r15, [rbp-0x2490]
     +0x52a  mov     QWORD PTR [rbp-0x24f0], rax
     +0x531  lea     rax, [rbp-0x2050]
     +0x538  mov     QWORD PTR [rbp-0x24c8], rax
     +0x53f  lea     rax, [rbp-0x2350]
     +0x546  mov     QWORD PTR [rbp-0x24e0], rax
     +0x54d  jmp     join5
 ***)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa44_verify_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The signature sigb at sig (2420 bytes), the message M of     *)
(* mlen bytes at m and the prefix PRE of prelen bytes at pre (or, if ext is  *)
(* nonzero as a 32-bit integer, mu in the first 64 bytes at m), the public   *)
(* key pkb at pk (1312 bytes): the result is 0 if the signature is accepted, *)
(* and -6 otherwise. ext, the seventh argument, is on the stack above the    *)
(* return address, as a 64-bit word whose low 32 bits the code reads. The    *)
(* function keeps the stack pointer of the entry in R10, lowers RSP by up to *)
(* 31 bytes to align it to 32 bytes, copies the return address there and     *)
(* saves RBP, the frame pointer, and six more registers, reserves the stack  *)
(* for its buffers, below which the callees use theirs: 11181 bytes of stack *)
(* below the return address in all.                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!sig m mlen pre prelen pk ext sigb pkb M PRE pc stackpointer
   returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
        (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
        mld_matrix_terminates 4 4 (num_of_bytelist(list_of_seq pkb 32)) /\
        mld_poly_challenge_terminates 39 32
         (num_of_bytelist(list_of_seq sigb 32)) /\
        ALL (nonoverlapping (word_sub stackpointer (word 11181),11181))
            [(sig,2420); (m,mlen); (pre,prelen); (pk,1312);
             (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa44_verify_internal) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  ext /\
                  (read DF s <=> false) /\
                  (!j. j < 2420
                       ==> read(memory :> bytes8(word_add sig (word j))) s =
                           sigb j) /\
                  read (memory :> bytes(m,mlen)) s = M /\
                  read (memory :> bytes(pre,prelen)) s = PRE /\
                  (!j. j < 1312
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           pkb j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                  (if mld_verify_internal_ok 4 4 32
                         mld_polyz_unpack_17 576 130994
                         mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39
                         sigb pkb
                         (if word_zx ext = (word 0:int32)
                          then mld_verify_mu 1312 pkb prelen PRE mlen M
                          else M MOD 2 EXP 512)
                   then word 0 else word 4294967290))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 11181),11181)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the flag ext, the    *)
(* signature, the message, the prefix and the public key, all public, and    *)
(* the stack, with all accesses within the arguments, the stack, the return  *)
(* address and ext above it and the constants of the callees, and the writes *)
(* within the stack.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e sig m mlen pre prelen pk ext sigb pkb M PRE pc
            stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
        (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
        mld_matrix_terminates 4 4 (num_of_bytelist(list_of_seq pkb 32)) /\
        mld_poly_challenge_terminates 39 32
         (num_of_bytelist(list_of_seq sigb 32)) /\
        ALL (nonoverlapping (word_sub stackpointer (word 11181),11181))
            [(sig,2420); (m,mlen); (pre,prelen); (pk,1312);
             (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa44_verify_internal) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  ext /\
                  (read DF s <=> false) /\
                  (!j. j < 2420
                       ==> read(memory :> bytes8(word_add sig (word j))) s =
                           sigb j) /\
                  read (memory :> bytes(m,mlen)) s = M /\
                  read (memory :> bytes(pre,prelen)) s = PRE /\
                  (!j. j < 1312
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           pkb j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                  (if mld_verify_internal_ok 4 4 32
                         mld_polyz_unpack_17 576 130994
                         mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39
                         sigb pkb
                         (if word_zx ext = (word 0:int32)
                          then mld_verify_mu 1312 pkb prelen PRE mlen M
                          else M MOD 2 EXP 512)
                   then word 0 else word 4294967290) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events sig m mlen pre prelen pk ext sigb pkb M PRE
                            pc (word_sub stackpointer (word 11181))
                            returnaddress /\
                     memaccess_inbounds e2
                      [sig,2420; m,mlen; pre,prelen; pk,1312;
                       word_sub stackpointer (word 11181),11181;
                       stackpointer,8; word_add stackpointer (word 8),8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [word_sub stackpointer (word 11181),11181]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 11181),11181)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e sig m mlen pre prelen pk ext sigb pkb M PRE pc
            stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
        (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
        mld_matrix_terminates 4 4 (num_of_bytelist(list_of_seq pkb 32)) /\
        mld_poly_challenge_terminates 39 32
         (num_of_bytelist(list_of_seq sigb 32)) /\
        ALL (nonoverlapping (word_sub stackpointer (word 11181),11181))
            [(sig,2420); (m,mlen); (pre,prelen); (pk,1312);
             (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa44_verify_internal) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  ext /\
                  (read DF s <=> false) /\
                  (!j. j < 2420
                       ==> read(memory :> bytes8(word_add sig (word j))) s =
                           sigb j) /\
                  read (memory :> bytes(m,mlen)) s = M /\
                  read (memory :> bytes(pre,prelen)) s = PRE /\
                  (!j. j < 1312
                       ==> read(memory :> bytes8(word_add pk (word j))) s =
                           pkb j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events sig m mlen pre prelen pk ext sigb pkb M PRE
                            pc (word_sub stackpointer (word 11181))
                            returnaddress /\
                     memaccess_inbounds e2
                      [sig,2420; m,mlen; pre,prelen; pk,1312;
                       word_sub stackpointer (word 11181),11181;
                       stackpointer,8; word_add stackpointer (word 8),8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [word_sub stackpointer (word 11181),11181]))
             (MAYCHANGE [RSP] ,,
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 11181),11181)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
