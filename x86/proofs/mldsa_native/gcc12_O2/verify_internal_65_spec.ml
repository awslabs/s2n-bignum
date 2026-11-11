(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the statement. This is the code for          *)
(* mldsa65_verify_internal (mld_sign_verify_internal in sign.c) from         *)
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
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_unpack_z_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_chknorm_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_ntt_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvec_matrix_expand_eager_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_challenge_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvec_matrix_pointwise_montgomery_row_eager_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/unpack_pk_t1_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_shiftl_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_pointwise_montgomery_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_sub_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_reduce_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_invntt_tomont_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_caddq_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/sig_unpack_hints_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_use_hint_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyw1_pack_32_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_absorb_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/H_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa65_verify_internal:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  push    QWORD PTR [r10-0x8]
       +0xd  push    rbp
       +0xe  mov     rbp, rsp
      +0x11  push    r15
      +0x13  mov     r15, rdx
      +0x16  push    r14
      +0x18  lea     rax, [rbp-0x8c30]
      +0x1f  mov     r14, rcx
      +0x22  push    r13
      +0x24  mov     r13, rax
      +0x27  push    r12
      +0x29  mov     r12, rsi
      +0x2c  lea     rsi, [rdi+0x30]
      +0x30  push    r10
      +0x32  push    rbx
      +0x33  sub     rsp, 0x9ce0
      +0x3a  movdqu  xmm3, XMMWORD PTR [rdi]
      +0x3e  movdqu  xmm4, XMMWORD PTR [rdi+0x10]
      +0x43  mov     QWORD PTR [rbp-0x9cd8], rdi
      +0x4a  movdqu  xmm5, XMMWORD PTR [rdi+0x20]
      +0x4f  mov     rdi, rax
      +0x52  mov     QWORD PTR [rbp-0x9ce8], r8
      +0x59  mov     QWORD PTR [rbp-0x9cf0], r9
      +0x60  mov     ebx, DWORD PTR [r10]
      +0x63  mov     QWORD PTR [rbp-0x9ce0], rax
      +0x6a  movaps  XMMWORD PTR [rbp-0x9cd0], xmm3
      +0x71  movaps  XMMWORD PTR [rbp-0x9cc0], xmm4
      +0x78  movaps  XMMWORD PTR [rbp-0x9cb0], xmm5
      +0x7f  call    mldsa65_polyvecl_unpack_z
     after_mldsa65_polyvecl_unpack_z:
      +0x84  mov     esi, 0x7ff3c
      +0x89  mov     rdi, r13
      +0x8c  call    mldsa65_polyvecl_chknorm
     after_mldsa65_polyvecl_chknorm:
      +0x91  mov     r11, QWORD PTR [rbp-0x9cd8]
      +0x98  test    eax, eax
      +0x9a  jne     +0x522
      +0xa0  mov     r13d, eax
      +0xa3  test    ebx, ebx
      +0xa5  je      join3
      +0xab  movdqu  xmm6, XMMWORD PTR [r12]
      +0xb1  movdqu  xmm7, XMMWORD PTR [r12+0x10]
      +0xb8  lea     rax, [rbp-0x7830]
      +0xbf  lea     rbx, [rbp-0x9030]
      +0xc6  mov     QWORD PTR [rbp-0x9cd8], rax
      +0xcd  lea     rax, [rbp-0x9c50]
      +0xd4  movaps  XMMWORD PTR [rbp-0x9c50], xmm6
      +0xdb  movdqu  xmm6, XMMWORD PTR [r12+0x20]
      +0xe2  movaps  XMMWORD PTR [rbp-0x9c40], xmm7
      +0xe9  movdqu  xmm7, XMMWORD PTR [r12+0x30]
      +0xf0  mov     QWORD PTR [rbp-0x9d10], rax
      +0xf7  movaps  XMMWORD PTR [rbp-0x9c30], xmm6
      +0xfe  movaps  XMMWORD PTR [rbp-0x9c20], xmm7
     join1:
     +0x105  mov     rdi, QWORD PTR [rbp-0x9ce0]
     +0x10c  mov     QWORD PTR [rbp-0x9cf8], r11
     +0x113  lea     r12, [rbp-0x9430]
     +0x11a  call    mldsa65_polyvecl_ntt
     after_mldsa65_polyvecl_ntt:
     +0x11f  mov     rsi, QWORD PTR [rbp-0x9cf0]
     +0x126  mov     rdi, QWORD PTR [rbp-0x9cd8]
     +0x12d  call    mldsa65_polyvec_matrix_expand_eager
     after_mldsa65_polyvec_matrix_expand_eager:
     +0x132  lea     rax, [rbp-0x9830]
     +0x139  lea     rsi, [rbp-0x9cd0]
     +0x140  mov     r14, rax
     +0x143  mov     rdi, rax
     +0x146  mov     QWORD PTR [rbp-0x9ce8], rax
     +0x14d  mov     QWORD PTR [rbp-0x9d08], rsi
     +0x154  call    mldsa65_poly_challenge
     after_mldsa65_poly_challenge:
     +0x159  mov     rdi, r14
     +0x15c  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_1:
     +0x161  lea     rax, [rbp-0x9b30]
     +0x168  mov     QWORD PTR [rbp-0x9d00], rax
     +0x16f  mov     r15, rax
     loop1:
     +0x172  mov     rdx, QWORD PTR [rbp-0x9ce0]
     +0x179  mov     rsi, QWORD PTR [rbp-0x9cd8]
     +0x180  mov     ecx, r13d
     +0x183  mov     rdi, r12
     +0x186  call    mldsa65_polyvec_matrix_pointwise_montgomery_row_eager
     after_mldsa65_polyvec_matrix_pointwise_montgomery_row_eager:
     +0x18b  mov     rsi, QWORD PTR [rbp-0x9cf0]
     +0x192  mov     edx, r13d
     +0x195  mov     rdi, rbx
     +0x198  call    mldsa65_unpack_pk_t1
     after_mldsa65_unpack_pk_t1:
     +0x19d  mov     rdi, rbx
     +0x1a0  call    mldsa_poly_shiftl
     after_mldsa_poly_shiftl:
     +0x1a5  mov     rdi, rbx
     +0x1a8  call    mldsa_poly_ntt
     after_mldsa_poly_ntt_2:
     +0x1ad  mov     rsi, QWORD PTR [rbp-0x9ce8]
     +0x1b4  mov     rdi, rbx
     +0x1b7  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery:
     +0x1bc  mov     rsi, rbx
     +0x1bf  mov     rdi, r12
     +0x1c2  call    mldsa_poly_sub
     after_mldsa_poly_sub:
     +0x1c7  mov     rdi, r12
     +0x1ca  call    mldsa_poly_reduce
     after_mldsa_poly_reduce:
     +0x1cf  mov     rdi, r12
     +0x1d2  call    mldsa_poly_invntt_tomont
     after_mldsa_poly_invntt_tomont:
     +0x1d7  mov     rdi, r12
     +0x1da  call    mldsa_poly_caddq
     after_mldsa_poly_caddq:
     +0x1df  mov     rsi, QWORD PTR [rbp-0x9cf8]
     +0x1e6  mov     edx, r13d
     +0x1e9  mov     rdi, rbx
     +0x1ec  call    mldsa65_sig_unpack_hints
     after_mldsa65_sig_unpack_hints:
     +0x1f1  mov     r14d, eax
     loop1_test1:
     +0x1f4  test    eax, eax
     +0x1f6  jne     join4
     loop1_next1:
     +0x1fc  mov     rsi, rbx
     +0x1ff  mov     rdi, r12
     +0x202  add     r13d, 0x1
     +0x206  call    mldsa65_poly_use_hint
     after_mldsa65_poly_use_hint:
     +0x20b  mov     rdi, r15
     +0x20e  mov     rsi, r12
     +0x211  sub     r15, 0xffffffffffffff80
     +0x215  call    mldsa_polyw1_pack_32
     loop1_test2: after_mldsa_polyw1_pack_32:
     +0x21a  cmp     r13d, 0x6
     loop1_back:
     +0x21e  jne     loop1
     loop1_exit1:
     +0x224  lea     r13, [rbp-0x9c00]
     +0x22b  lea     r15, [rbp-0x9c90]
     +0x232  mov     rdi, r13
     +0x235  call    mldsa_shake256_init
     after_mldsa_shake256_init_1:
     +0x23a  mov     rsi, QWORD PTR [rbp-0x9d10]
     +0x241  mov     rdi, r13
     +0x244  mov     edx, 0x40
     +0x249  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_1:
     +0x24e  mov     rsi, QWORD PTR [rbp-0x9d00]
     +0x255  mov     edx, 0x300
     +0x25a  mov     rdi, r13
     +0x25d  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_2:
     +0x262  mov     rdi, r13
     +0x265  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize_1:
     +0x26a  mov     rdx, r13
     +0x26d  mov     esi, 0x30
     +0x272  mov     rdi, r15
     +0x275  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze_1:
     +0x27a  mov     rdi, r13
     +0x27d  call    mldsa_shake256_release
     after_mldsa_shake256_release_1:
     +0x282  xor     eax, eax
     +0x284  mov     rdi, r13
     +0x287  mov     ecx, 0x1a
     +0x28c  rep stos QWORD PTR es:[rdi], rax
     +0x28f  pxor    xmm1, xmm1
     +0x293  mov     rdx, QWORD PTR [rbp-0x9d08]
     +0x29a  movdqa  xmm0, xmm1
     loop2:
     +0x29e  movdqa  xmm2, XMMWORD PTR [rdx+rax*1]
     +0x2a3  pxor    xmm2, XMMWORD PTR [r15+rax*1]
     +0x2a9  add     rax, 0x10
     +0x2ad  por     xmm0, xmm2
     +0x2b1  pxor    xmm1, xmm2
     loop2_test:
     +0x2b5  cmp     rax, 0x30
     loop2_back:
     +0x2b9  jne     loop2
     loop2_exit:
     +0x2bb  movdqa  xmm2, xmm1
     +0x2bf  psrldq  xmm2, 0x8
     +0x2c4  pxor    xmm1, xmm2
     +0x2c8  movdqa  xmm2, xmm1
     +0x2cc  psrldq  xmm2, 0x4
     +0x2d1  pxor    xmm1, xmm2
     +0x2d5  movdqa  xmm2, xmm1
     +0x2d9  psrldq  xmm2, 0x2
     +0x2de  pxor    xmm1, xmm2
     +0x2e2  movdqa  xmm2, xmm1
     +0x2e6  psrldq  xmm2, 0x1
     +0x2eb  pxor    xmm1, xmm2
     +0x2ef  movd    edx, xmm1
     +0x2f3  movdqa  xmm1, xmm0
     +0x2f7  psrldq  xmm1, 0x8
     +0x2fc  por     xmm0, xmm1
     +0x300  movdqa  xmm1, xmm0
     +0x304  psrldq  xmm1, 0x4
     +0x309  por     xmm0, xmm1
     +0x30d  movdqa  xmm1, xmm0
     +0x311  psrldq  xmm1, 0x2
     +0x316  por     xmm0, xmm1
     +0x31a  movdqa  xmm1, xmm0
     +0x31e  psrldq  xmm1, 0x1
     +0x323  por     xmm0, xmm1
     +0x327  movd    eax, xmm0
     +0x32b  movzx   eax, al
     +0x32e  neg     rax
     +0x331  sar     rax, 0x20
     +0x335  xor     eax, edx
     +0x337  cmp     al, dl
     +0x339  jne     join5
     join2:
     +0x33f  xor     r13d, r13d
     +0x342  mov     rdi, rbx
     +0x345  mov     ecx, 0x80
     +0x34a  mov     rax, r13
     +0x34d  rep stos QWORD PTR es:[rdi], rax
     +0x350  mov     ecx, 0x80
     +0x355  mov     rdi, r12
     +0x358  rep stos QWORD PTR es:[rdi], rax
     +0x35b  mov     rbx, QWORD PTR [rbp-0x9cd8]
     +0x362  mov     edx, 0x7800
     +0x367  xor     esi, esi
     +0x369  mov     rdi, rbx
     +0x36c  call    memset
     after_memset:
     +0x371  mov     rdi, QWORD PTR [rbp-0x9ce8]
     +0x378  mov     rax, r13
     +0x37b  mov     ecx, 0x80
     +0x380  rep stos QWORD PTR es:[rdi], rax
     +0x383  mov     rdi, QWORD PTR [rbp-0x9ce8]
     +0x38a  mov     rdi, QWORD PTR [rbp-0x9ce0]
     +0x391  mov     ecx, 0x280
     +0x396  rep stos QWORD PTR es:[rdi], rax
     +0x399  mov     rdi, QWORD PTR [rbp-0x9ce0]
     +0x3a0  pxor    xmm0, xmm0
     +0x3a4  movaps  XMMWORD PTR [rbp-0x9c90], xmm0
     +0x3ab  movaps  XMMWORD PTR [rbp-0x9c80], xmm0
     +0x3b2  movaps  XMMWORD PTR [rbp-0x9c70], xmm0
     +0x3b9  mov     rax, QWORD PTR [rbp-0x9d08]
     +0x3c0  movaps  XMMWORD PTR [rbp-0x9cd0], xmm0
     +0x3c7  movaps  XMMWORD PTR [rbp-0x9cc0], xmm0
     +0x3ce  movaps  XMMWORD PTR [rbp-0x9cb0], xmm0
     +0x3d5  mov     rax, QWORD PTR [rbp-0x9d10]
     +0x3dc  movaps  XMMWORD PTR [rbp-0x9c50], xmm0
     +0x3e3  movaps  XMMWORD PTR [rbp-0x9c40], xmm0
     +0x3ea  movaps  XMMWORD PTR [rbp-0x9c30], xmm0
     +0x3f1  movaps  XMMWORD PTR [rbp-0x9c20], xmm0
     +0x3f8  mov     rdi, QWORD PTR [rbp-0x9d00]
     +0x3ff  mov     rax, r13
     +0x402  mov     ecx, 0x60
     +0x407  rep stos QWORD PTR es:[rdi], rax
     +0x40a  mov     rdi, QWORD PTR [rbp-0x9d00]
     +0x411  lea     rsp, [rbp-0x30]
     +0x415  mov     eax, r14d
     +0x418  pop     rbx
     +0x419  pop     r10
     +0x41b  pop     r12
     +0x41d  pop     r13
     +0x41f  pop     r14
     +0x421  pop     r15
     +0x423  pop     rbp
     +0x424  lea     rsp, [r10-0x8]
     ret:
     +0x428  ret
     +0x429  nop     DWORD PTR [rax+0x0]
     join3:
     +0x430  lea     rax, [rbp-0x7830]
     +0x437  mov     QWORD PTR [rbp-0x9cf8], r11
     +0x43e  mov     rdi, rax
     +0x441  mov     rbx, rax
     +0x444  call    mldsa_shake256_init
     after_mldsa_shake256_init_2:
     +0x449  mov     rsi, QWORD PTR [rbp-0x9cf0]
     +0x450  mov     edx, 0x7a0
     +0x455  mov     rdi, rbx
     +0x458  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_3:
     +0x45d  mov     rdi, rbx
     +0x460  mov     QWORD PTR [rbp-0x9cd8], rbx
     +0x467  lea     rbx, [rbp-0x9030]
     +0x46e  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize_2:
     +0x473  mov     rdx, QWORD PTR [rbp-0x9cd8]
     +0x47a  mov     esi, 0x40
     +0x47f  mov     rdi, rbx
     +0x482  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze_2:
     +0x487  mov     rdi, QWORD PTR [rbp-0x9cd8]
     +0x48e  call    mldsa_shake256_release
     after_mldsa_shake256_release_2:
     +0x493  mov     rdi, QWORD PTR [rbp-0x9cd8]
     +0x49a  xor     eax, eax
     +0x49c  mov     ecx, 0x1a
     +0x4a1  rep stos QWORD PTR es:[rdi], rax
     +0x4a4  mov     rdi, QWORD PTR [rbp-0x9cd8]
     +0x4ab  mov     ecx, 0x40
     +0x4b0  mov     r8, r14
     +0x4b3  mov     rdx, rbx
     +0x4b6  mov     esi, 0x40
     +0x4bb  lea     rax, [rbp-0x9c50]
     +0x4c2  mov     r9, QWORD PTR [rbp-0x9ce8]
     +0x4c9  mov     QWORD PTR [rbp-0x9d10], rax
     +0x4d0  mov     rdi, rax
     +0x4d3  push    r15
     +0x4d5  push    r12
     +0x4d7  call    mld_H65
     after_mld_H65:
     +0x4dc  pxor    xmm0, xmm0
     +0x4e0  movaps  XMMWORD PTR [rbp-0x9030], xmm0
     +0x4e7  movaps  XMMWORD PTR [rbp-0x9020], xmm0
     +0x4ee  movaps  XMMWORD PTR [rbp-0x9010], xmm0
     +0x4f5  movaps  XMMWORD PTR [rbp-0x9000], xmm0
     +0x4fc  pop     rax
     +0x4fd  mov     r11, QWORD PTR [rbp-0x9cf8]
     +0x504  pop     rdx
     +0x505  jmp     join1
     +0x50a  nop     WORD PTR [rax+rax*1+0x0]
     join4: loop1_exit2:
     +0x510  lea     r15, [rbp-0x9c90]
     join5:
     +0x517  mov     r14d, 0xfffffffa
     +0x51d  jmp     join2
     +0x522  lea     rax, [rbp-0x7830]
     +0x529  lea     rbx, [rbp-0x9030]
     +0x530  mov     QWORD PTR [rbp-0x9cd8], rax
     +0x537  lea     rax, [rbp-0x9c50]
     +0x53e  lea     r12, [rbp-0x9430]
     +0x545  mov     QWORD PTR [rbp-0x9d10], rax
     +0x54c  lea     rax, [rbp-0x9cd0]
     +0x553  lea     r15, [rbp-0x9c90]
     +0x55a  mov     QWORD PTR [rbp-0x9d08], rax
     +0x561  lea     rax, [rbp-0x9830]
     +0x568  mov     QWORD PTR [rbp-0x9ce8], rax
     +0x56f  lea     rax, [rbp-0x9b30]
     +0x576  mov     QWORD PTR [rbp-0x9d00], rax
     +0x57d  jmp     join5

    plt_memset:
       +0x0  jmp     QWORD PTR [rip+0xefc2]
                     // got_memset
       +0x6  push    0x2
       +0xb  jmp     <.plt>
 ***)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_verify_internal"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The signature sigb at sig  *)
(* (3309 bytes), the message M of mlen bytes at m and the prefix PRE of      *)
(* prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu in the *)
(* first 64 bytes at m), the public key pkb at pk (1952 bytes): the result   *)
(* is 0 if the signature is accepted, and -6 otherwise. ext, the seventh     *)
(* argument, is on the stack above the return address, as a 64-bit word      *)
(* whose low 32 bits the code reads. The function keeps the stack pointer of *)
(* the entry in R10, lowers RSP by up to 31 bytes to align it to 32 bytes,   *)
(* copies the return address there and saves RBP, the frame pointer, and six *)
(* more registers, reserves the stack for its buffers, below which the       *)
(* callees use theirs: 45429 bytes of stack below the return address in all. *)
(* The GOT entry of memset, which the stub reads, and the region (ea,el)     *)
(* that memset may read are apart from the stack.                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !sig m mlen pre prelen pk ext sigb pkb M PRE pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 6 5 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 49 48
           (num_of_bytelist(list_of_seq sigb 48)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 45429),45429))
              [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa65_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
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
                 [memory :> bytes(word_sub stackpointer (word 45429),45429)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the flag ext, the    *)
(* signature, the message, the prefix and the public key, all public, the    *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the return address and ext above it, the GOT entry of memset,  *)
(* the region (ea,el) that memset may read and the constants of the callees, *)
(* and the writes within the stack.                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk ext sigb pkb M PRE pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 6 5 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 49 48
           (num_of_bytelist(list_of_seq sigb 48)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 45429),45429))
              [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa65_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
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
                              mf pc (word_sub stackpointer (word 45429))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; pk,1952;
                         word_sub stackpointer (word 45429),45429;
                         stackpointer,8; word_add stackpointer (word 8),8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                          mldsa65_polyvec_matrix_expand_eager_consts),4]
                        [word_sub stackpointer (word 45429),45429]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 45429),45429)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk ext sigb pkb M PRE pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 6 5 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 49 48
           (num_of_bytelist(list_of_seq sigb 48)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 45429),45429))
              [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa65_verify_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8))) s =
                    ext /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
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
                              mf pc (word_sub stackpointer (word 45429))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; pk,1952;
                         word_sub stackpointer (word 45429),45429;
                         stackpointer,8; word_add stackpointer (word 8),8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                          mldsa65_polyvec_matrix_expand_eager_consts),4]
                        [word_sub stackpointer (word 45429),45429]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 45429),45429)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
