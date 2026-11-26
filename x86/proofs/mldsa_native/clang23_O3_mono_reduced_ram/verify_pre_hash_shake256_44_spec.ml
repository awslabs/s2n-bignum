(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature with a SHAKE256 pre-hash: the statement. This is    *)
(* the code for mldsa44_verify_pre_hash_shake256                             *)
(* (mld_sign_verify_pre_hash_shake256 in sign.c, an external API function)   *)
(* from mldsa-native's portable C implementation compiled by clang 23 with   *)
(* -O3 and MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which hashes  *)
(* the message to 64 bytes with an inlined SHAKE256 (it absorbs full blocks  *)
(* of 136 bytes with calls of mldsa_keccakf1600_permute, then the rest,      *)
(* pads, permutes and squeezes), returns -9 if ctxlen > 255, and otherwise   *)
(* builds the prefix 1 || ctxlen || ctx || OID || ph of hashalg =            *)
(* MLD_PREHASH_SHAKE_256 (12) on the stack, copying the context with memcpy, *)
(* called through the PLT, unless ctxlen is 0, and verifies it as the        *)
(* message with mldsa44_verify_internal. It zeroes the prefix with memset,   *)
(* called through the PLT, and the pre-hash with SSE stores. It realigns its *)
(* stack frame to 32 bytes (utils/mldsa_native_realign.ml). It is verified   *)
(* in the whole image (see libmldsa.ml), using the theorems for the callees  *)
(* and the contracts memset_full_contract and memcpy_full_contract of        *)
(* utils/mldsa_native_libc.ml for the C library functions that they and it   *)
(* call, and shown to be constant time and memory safe.                      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_internal_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stubs for memcpy, memset:

    mldsa44_verify_pre_hash_shake256:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r15
       +0x6  push    r14
       +0x8  push    r13
       +0xa  push    r12
       +0xc  push    rbx
       +0xd  and     rsp, 0xffffffffffffffe0
      +0x11  sub     rsp, 0x1e0
      +0x18  mov     QWORD PTR [rsp+0x18], r9
      +0x1d  mov     r14, r8
      +0x20  mov     QWORD PTR [rsp+0x10], rcx
      +0x25  mov     r13, rdx
      +0x28  mov     r12, rsi
      +0x2b  mov     r15, rdi
      +0x2e  xorps   xmm0, xmm0
      +0x31  movups  XMMWORD PTR [rsp+0xdc], xmm0
      +0x39  movaps  XMMWORD PTR [rsp+0xd0], xmm0
      +0x41  movaps  XMMWORD PTR [rsp+0xc0], xmm0
      +0x49  movaps  XMMWORD PTR [rsp+0xb0], xmm0
      +0x51  movaps  XMMWORD PTR [rsp+0xa0], xmm0
      +0x59  movaps  XMMWORD PTR [rsp+0x90], xmm0
      +0x61  movaps  XMMWORD PTR [rsp+0x80], xmm0
      +0x69  movaps  XMMWORD PTR [rsp+0x70], xmm0
      +0x6e  movaps  XMMWORD PTR [rsp+0x60], xmm0
      +0x73  movaps  XMMWORD PTR [rsp+0x50], xmm0
      +0x78  movaps  XMMWORD PTR [rsp+0x40], xmm0
      +0x7d  movaps  XMMWORD PTR [rsp+0x30], xmm0
      +0x82  movaps  XMMWORD PTR [rsp+0x20], xmm0
      +0x87  cmp     rdx, 0x88
      +0x8e  jb      join1                                         ---+
      +0x94  lea     rbx, [rsp+0x20]                                  |
      +0x99  nop     DWORD PTR [rax+0x0]                              |
    loop1:                                                            |
      +0xa0  movups  xmm0, XMMWORD PTR [r12]                       <+ |
      +0xa5  movups  xmm1, XMMWORD PTR [r12+0x10]                   | |
      +0xab  xorps   xmm0, XMMWORD PTR [rsp+0x20]                   | |
      +0xb0  xorps   xmm1, XMMWORD PTR [rsp+0x30]                   | |
      +0xb5  movaps  XMMWORD PTR [rsp+0x20], xmm0                   | |
      +0xba  movaps  XMMWORD PTR [rsp+0x30], xmm1                   | |
      +0xbf  movups  xmm0, XMMWORD PTR [r12+0x20]                   | |
      +0xc5  movups  xmm1, XMMWORD PTR [r12+0x30]                   | |
      +0xcb  xorps   xmm0, XMMWORD PTR [rsp+0x40]                   | |
      +0xd0  xorps   xmm1, XMMWORD PTR [rsp+0x50]                   | |
      +0xd5  movaps  XMMWORD PTR [rsp+0x40], xmm0                   | |
      +0xda  movaps  XMMWORD PTR [rsp+0x50], xmm1                   | |
      +0xdf  movups  xmm0, XMMWORD PTR [r12+0x40]                   | |
      +0xe5  movups  xmm1, XMMWORD PTR [r12+0x50]                   | |
      +0xeb  xorps   xmm0, XMMWORD PTR [rsp+0x60]                   | |
      +0xf0  xorps   xmm1, XMMWORD PTR [rsp+0x70]                   | |
      +0xf5  movaps  XMMWORD PTR [rsp+0x60], xmm0                   | |
      +0xfa  movaps  XMMWORD PTR [rsp+0x70], xmm1                   | |
      +0xff  movups  xmm0, XMMWORD PTR [r12+0x60]                   | |
     +0x105  movups  xmm1, XMMWORD PTR [r12+0x70]                   | |
     +0x10b  xorps   xmm0, XMMWORD PTR [rsp+0x80]                   | |
     +0x113  xorps   xmm1, XMMWORD PTR [rsp+0x90]                   | |
     +0x11b  movaps  XMMWORD PTR [rsp+0x80], xmm0                   | |
     +0x123  movaps  XMMWORD PTR [rsp+0x90], xmm1                   | |
     +0x12b  mov     rax, QWORD PTR [r12+0x80]                      | |
     +0x133  xor     QWORD PTR [rsp+0xa0], rax                      | |
     +0x13b  add     r13, 0xffffffffffffff78                        | |
     +0x142  add     r12, 0x88                                      | |
     +0x149  mov     rdi, rbx                                       | |
     +0x14c  call    mldsa_keccakf1600_permute                      | |
    loop1_test:                                                     | |
    after_mldsa_keccakf1600_permute_1:                              | |
     +0x151  cmp     r13, 0x87                                      | |
    loop1_back:                                                     | |
     +0x158  ja      loop1                                         -+ |
    join1: loop1_exit:                                                |
     +0x15e  test    r13, r13                                      <--+
     +0x161  je      join5                                         -----+
     +0x167  cmp     r13, 0x4                                           |
     +0x16b  jb      join2                                         -+   |
     +0x16d  lea     rax, [rsp+r13*1]                               |   |
     +0x171  add     rax, 0x20                                      |   |
     +0x175  lea     rcx, [r12+r13*1]                               |   |
     +0x179  lea     rdx, [rsp+0x20]                                |   |
     +0x17e  cmp     rdx, rcx                                       |   |
     +0x181  setb    cl                                             |   |
     +0x184  cmp     r12, rax                                       |   |
     +0x187  setb    al                                             |   |
     +0x18a  test    cl, al                                         |   |
     +0x18c  je      +0x3c3                                        ---------+
    join2:                                                          |   |   |
     +0x192  xor     eax, eax                                      <+   |   |
    join3:                                                              |   |
     +0x194  mov     rdx, r13                                           |   |
     +0x197  mov     rcx, rax                                           |   |
     +0x19a  and     rdx, 0x3                                           |   |
     +0x19e  je      join4                                         ---+ |   |
     +0x1a0  mov     rcx, rax                                         | |   |
     +0x1a3  data16 data16 data16 cs nop WORD PTR [rax+rax*1+0x0]     | |   |
    loop2:                                                            | |   |
     +0x1b0  movzx   esi, BYTE PTR [r12+rcx*1]                     <+ | |   |
     +0x1b5  xor     BYTE PTR [rsp+rcx*1+0x20], sil                 | | |   |
     +0x1ba  inc     rcx                                            | | |   |
    loop2_test:                                                     | | |   |
     +0x1bd  dec     rdx                                            | | |   |
    loop2_back:                                                     | | |   |
     +0x1c0  jne     loop2                                         -+ | |   |
    join4: loop2_exit:                                                | |   |
     +0x1c2  sub     rax, r13                                      <--+ |   |
     +0x1c5  cmp     rax, 0xfffffffffffffffc                            |   |
     +0x1c9  ja      join5                                         ---+ |   |
     +0x1cb  nop     DWORD PTR [rax+rax*1+0x0]                        | |   |
    loop3:                                                            | |   |
     +0x1d0  movzx   eax, BYTE PTR [r12+rcx*1]                     <+ | |   |
     +0x1d5  xor     BYTE PTR [rsp+rcx*1+0x20], al                  | | |   |
     +0x1d9  movzx   eax, BYTE PTR [r12+rcx*1+0x1]                  | | |   |
     +0x1df  xor     BYTE PTR [rsp+rcx*1+0x21], al                  | | |   |
     +0x1e3  movzx   eax, BYTE PTR [r12+rcx*1+0x2]                  | | |   |
     +0x1e9  xor     BYTE PTR [rsp+rcx*1+0x22], al                  | | |   |
     +0x1ed  movzx   eax, BYTE PTR [r12+rcx*1+0x3]                  | | |   |
     +0x1f3  xor     BYTE PTR [rsp+rcx*1+0x23], al                  | | |   |
     +0x1f7  add     rcx, 0x4                                       | | |   |
    loop3_test:                                                     | | |   |
     +0x1fb  cmp     r13, rcx                                       | | |   |
    loop3_back:                                                     | | |   |
     +0x1fe  jne     loop3                                         -+ | |   |
    join5: loop3_exit:                                                | |   |
     +0x200  mov     DWORD PTR [rsp+0xe8], r13d                    <--+-+-+---+
     +0x208  xor     BYTE PTR [rsp+r13*1+0x20], 0x1f                      | | |
     +0x20e  xor     BYTE PTR [rsp+0xa7], 0x80                            | | |
     +0x216  mov     DWORD PTR [rsp+0xe8], 0x88                           | | |
     +0x221  lea     rbx, [rsp+0x20]                                      | | |
     +0x226  mov     rdi, rbx                                             | | |
     +0x229  call    mldsa_keccakf1600_permute                            | | |
    after_mldsa_keccakf1600_permute_2:                                    | | |
     +0x22e  movaps  xmm0, XMMWORD PTR [rsp+0x20]                         | | |
     +0x233  movaps  xmm1, XMMWORD PTR [rsp+0x30]                         | | |
     +0x238  movaps  xmm2, XMMWORD PTR [rsp+0x40]                         | | |
     +0x23d  movaps  xmm3, XMMWORD PTR [rsp+0x50]                         | | |
     +0x242  movaps  XMMWORD PTR [rsp+0x1b0], xmm3                        | | |
     +0x24a  movaps  XMMWORD PTR [rsp+0x1a0], xmm2                        | | |
     +0x252  movaps  XMMWORD PTR [rsp+0x190], xmm1                        | | |
     +0x25a  movaps  XMMWORD PTR [rsp+0x180], xmm0                        | | |
     +0x262  xorps   xmm0, xmm0                                           | | |
     +0x265  movaps  XMMWORD PTR [rsp+0x60], xmm0                         | | |
     +0x26a  movaps  XMMWORD PTR [rsp+0x70], xmm0                         | | |
     +0x26f  movaps  XMMWORD PTR [rsp+0x80], xmm0                         | | |
     +0x277  movaps  XMMWORD PTR [rsp+0x90], xmm0                         | | |
     +0x27f  movaps  XMMWORD PTR [rsp+0xa0], xmm0                         | | |
     +0x287  movaps  XMMWORD PTR [rsp+0xb0], xmm0                         | | |
     +0x28f  movaps  XMMWORD PTR [rsp+0xc0], xmm0                         | | |
     +0x297  movaps  XMMWORD PTR [rsp+0xd0], xmm0                         | | |
     +0x29f  movaps  XMMWORD PTR [rsp+0xe0], xmm0                         | | |
     +0x2a7  movaps  XMMWORD PTR [rsp+0x20], xmm0                         | | |
     +0x2ac  movaps  XMMWORD PTR [rsp+0x30], xmm0                         | | |
     +0x2b1  movaps  XMMWORD PTR [rsp+0x40], xmm0                         | | |
     +0x2b6  movaps  XMMWORD PTR [rsp+0x50], xmm0                         | | |
     +0x2bb  mov     ebx, 0xfffffff7                                      | | |
     +0x2c0  cmp     r14, 0xff                                            | | |
     +0x2c7  ja      join7                                         ---+   | | |
     +0x2cd  mov     BYTE PTR [rsp+0x20], 0x1                         |   | | |
     +0x2d2  mov     BYTE PTR [rsp+0x21], r14b                        |   | | |
     +0x2d7  test    r14, r14                                         |   | | |
     +0x2da  je      join6                                         -+ |   | | |
     +0x2dc  lea     rdi, [rsp+0x22]                                | |   | | |
     +0x2e1  mov     rsi, QWORD PTR [rsp+0x10]                      | |   | | |
     +0x2e6  mov     rdx, r14                                       | |   | | |
     +0x2e9  call    memcpy                                         | |   | | |
    join6: after_memcpy:                                            | |   | | |
     +0x2ee  movabs  rax, 0x365014886600906                        <+ |   | | |
     +0x2f8  mov     QWORD PTR [rsp+r14*1+0x22], rax                  |   | | |
     +0x2fd  mov     DWORD PTR [rsp+r14*1+0x29], 0xc020403            |   | | |
     +0x306  movaps  xmm0, XMMWORD PTR [rsp+0x180]                    |   | | |
     +0x30e  movaps  xmm1, XMMWORD PTR [rsp+0x190]                    |   | | |
     +0x316  movaps  xmm2, XMMWORD PTR [rsp+0x1a0]                    |   | | |
     +0x31e  movaps  xmm3, XMMWORD PTR [rsp+0x1b0]                    |   | | |
     +0x326  movups  XMMWORD PTR [rsp+r14*1+0x2d], xmm0               |   | | |
     +0x32c  movups  XMMWORD PTR [rsp+r14*1+0x3d], xmm1               |   | | |
     +0x332  movups  XMMWORD PTR [rsp+r14*1+0x4d], xmm2               |   | | |
     +0x338  movups  XMMWORD PTR [rsp+r14*1+0x5d], xmm3               |   | | |
     +0x33e  add     r14, 0x4d                                        |   | | |
     +0x342  mov     DWORD PTR [rsp], 0x0                             |   | | |
     +0x349  lea     rsi, [rsp+0x20]                                  |   | | |
     +0x34e  mov     rdi, r15                                         |   | | |
     +0x351  mov     rdx, r14                                         |   | | |
     +0x354  xor     ecx, ecx                                         |   | | |
     +0x356  xor     r8d, r8d                                         |   | | |
     +0x359  mov     r9, QWORD PTR [rsp+0x18]                         |   | | |
     +0x35e  call    mldsa44_verify_internal                          |   | | |
    after_mldsa44_verify_internal:                                    |   | | |
     +0x363  mov     ebx, eax                                         |   | | |
    join7:                                                            |   | | |
     +0x365  lea     r14, [rsp+0x20]                               <--+   | | |
     +0x36a  mov     edx, 0x14c                                           | | |
     +0x36f  mov     rdi, r14                                             | | |
     +0x372  xor     esi, esi                                             | | |
     +0x374  call    memset                                               | | |
    after_memset:                                                         | | |
     +0x379  xorps   xmm0, xmm0                                           | | |
     +0x37c  movaps  XMMWORD PTR [rsp+0x180], xmm0                        | | |
     +0x384  movaps  XMMWORD PTR [rsp+0x190], xmm0                        | | |
     +0x38c  movaps  XMMWORD PTR [rsp+0x1a0], xmm0                        | | |
     +0x394  movaps  XMMWORD PTR [rsp+0x1b0], xmm0                        | | |
     +0x39c  lea     rax, [rsp+0x180]                                     | | |
     +0x3a4  mov     eax, ebx                                             | | |
     +0x3a6  lea     rsp, [rbp-0x28]                                      | | |
     +0x3aa  pop     rbx                                                  | | |
     +0x3ab  pop     r12                                                  | | |
     +0x3ad  pop     r13                                                  | | |
     +0x3af  pop     r14                                                  | | |
     +0x3b1  pop     r15                                                  | | |
     +0x3b3  pop     rbp                                                  | | |
     +0x3b4  xor     ecx, ecx                                             | | |
     +0x3b6  xor     edi, edi                                             | | |
     +0x3b8  xor     edx, edx                                             | | |
     +0x3ba  xor     esi, esi                                             | | |
     +0x3bc  xor     r8d, r8d                                             | | |
     +0x3bf  xor     r9d, r9d                                             | | |
    ret:                                                                  | | |
     +0x3c2  ret                                                          | | |
     +0x3c3  cmp     r13, 0x20                                     <--------+ |
     +0x3c7  jae     +0x3cd                                        -+     |   |
     +0x3c9  xor     eax, eax                                       |     |   |
     +0x3cb  jmp     join8                                         ---+   |   |
     +0x3cd  mov     eax, r13d                                     <+ |   |   |
     +0x3d0  and     eax, 0xe0                                        |   |   |
     +0x3d5  xor     ecx, ecx                                         |   |   |
     +0x3d7  nop     WORD PTR [rax+rax*1+0x0]                         |   |   |
    loop4:                                                            |   |   |
     +0x3e0  movups  xmm0, XMMWORD PTR [r12+rcx*1]                 <+ |   |   |
     +0x3e5  movups  xmm1, XMMWORD PTR [r12+rcx*1+0x10]             | |   |   |
     +0x3eb  xorps   xmm0, XMMWORD PTR [rsp+rcx*1+0x20]             | |   |   |
     +0x3f0  xorps   xmm1, XMMWORD PTR [rsp+rcx*1+0x30]             | |   |   |
     +0x3f5  movaps  XMMWORD PTR [rsp+rcx*1+0x20], xmm0             | |   |   |
     +0x3fa  movaps  XMMWORD PTR [rsp+rcx*1+0x30], xmm1             | |   |   |
     +0x3ff  add     rcx, 0x20                                      | |   |   |
    loop4_test:                                                     | |   |   |
     +0x403  cmp     rax, rcx                                       | |   |   |
    loop4_back:                                                     | |   |   |
     +0x406  jne     loop4                                         -+ |   |   |
    loop4_exit:                                                       |   |   |
     +0x408  cmp     r13, rax                                         |   |   |
     +0x40b  je      join5                                         -------+   |
     +0x411  test    r13b, 0x1c                                       |       |
     +0x415  je      join3                                            |       |
    join8:                                                            |       |
     +0x41b  mov     rcx, rax                                      <--+       |
     +0x41e  mov     eax, r13d                                                |
     +0x421  and     eax, 0xfc                                                |
     +0x426  cs nop  WORD PTR [rax+rax*1+0x0]                                 |
    loop5:                                                                    |
     +0x430  mov     edx, DWORD PTR [r12+rcx*1]                    <+         |
     +0x434  xor     DWORD PTR [rsp+rcx*1+0x20], edx                |         |
     +0x438  add     rcx, 0x4                                       |         |
    loop5_test:                                                     |         |
     +0x43c  cmp     rax, rcx                                       |         |
    loop5_back:                                                     |         |
     +0x43f  jne     loop5                                         -+         |
    loop5_exit:                                                               |
     +0x441  cmp     r13, rax                                                 |
     +0x444  je      join5                                         -----------+
     +0x44a  jmp     join3

    plt_memcpy:
       +0x0  jmp     QWORD PTR [rip+0x26fd2]
                     // got_memcpy
       +0x6  push    0x0
       +0xb  jmp     <.plt>

    plt_memset:
       +0x0  jmp     QWORD PTR [rip+0x26fc2]
                     // got_memset
       +0x6  push    0x2
       +0xb  jmp     <.plt>
 ***)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_verify_pre_hash_shake256";
    layout_range "plt_memcpy";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* signature sigb at sig (2420 bytes), the message M of mlen bytes at m, the *)
(* context C of ctxlen bytes at ctx and the public key pkb at pk (1312       *)
(* bytes), with PH the 64 bytes of the SHAKE256 pre-hash of M and PRE the    *)
(* prefix 1 || ctxlen || ctx || OID || PH: the result is -9 if ctxlen > 255, *)
(* and otherwise 0 if the signature is accepted for PRE as the message, and  *)
(* -6 if not. The function saves RBP, the frame pointer, and five more       *)
(* registers below the return address, lowers RSP by up to 31 bytes to align *)
(* it to 32 bytes, reserves its frame for the sponge state, the pre-hash and *)
(* the prefix, and ext, the seventh argument of mldsa44_verify_internal,     *)
(* below which that function uses 10949 bytes with its return address: 11516 *)
(* bytes of stack below the return address in all. The GOT entries of memset *)
(* and memcpy and the region (ea,el) that they may read are apart from the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen pk sigb pkb M C PH PRE pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 39 32
                (num_of_bytelist(list_of_seq sigb 32))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 11516),11516))
              [(sig,2420); (m,mlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa44_verify_pre_hash_shake256) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_verify_internal_ok 4 4 32
                           mld_polyz_unpack_17 576 130994
                           mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39
                           sigb pkb
                       (mld_verify_mu 1312 pkb 0 0 (ctxlen + 77) PRE)
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 11516),11516)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the signature, the   *)
(* message, the context and the public key, all public, the addresses of     *)
(* memset and memcpy and the stack, with all accesses within the arguments,  *)
(* the stack, the return address, the GOT entries, the region (ea,el) that   *)
(* the C library functions may read and the constants of the callees, and    *)
(* the writes within the stack.                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen pk sigb pkb M C PH PRE pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 39 32
                (num_of_bytelist(list_of_seq sigb 32))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 11516),11516))
              [(sig,2420); (m,mlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa44_verify_pre_hash_shake256) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_verify_internal_ok 4 4 32
                           mld_polyz_unpack_17 576 130994
                           mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39
                           sigb pkb
                       (mld_verify_mu 1312 pkb 0 0 (ctxlen + 77) PRE)
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen pk sigb pkb M C
                            mf mc pc (word_sub stackpointer (word 11516))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; ctx,ctxlen; pk,1312;
                         word_sub stackpointer (word 11516),11516;
                         stackpointer,8; word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa44_poly_challenge_consts),64;
                          word(pc + mldsa44_verify_internal_const1),16;
                          word(pc + mldsa44_verify_internal_const2),16;
                          word(pc + mldsa44_verify_internal_const3),8;
                          word(pc + mldsa44_verify_internal_const4),8;
                          word(pc + mld_compute_pack_t0_t144_const1),16;
                          word(pc + mld_compute_pack_t0_t144_const2),16;
                          word(pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448]
                        [word_sub stackpointer (word 11516),11516]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 11516),11516)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen pk sigb pkb M C PH PRE pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 39 32
                (num_of_bytelist(list_of_seq sigb 32))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 11516),11516))
              [(sig,2420); (m,mlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa44_verify_pre_hash_shake256) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen pk sigb pkb M C
                            mf mc pc (word_sub stackpointer (word 11516))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; ctx,ctxlen; pk,1312;
                         word_sub stackpointer (word 11516),11516;
                         stackpointer,8; word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa44_poly_challenge_consts),64;
                          word(pc + mldsa44_verify_internal_const1),16;
                          word(pc + mldsa44_verify_internal_const2),16;
                          word(pc + mldsa44_verify_internal_const3),8;
                          word(pc + mldsa44_verify_internal_const4),8;
                          word(pc + mld_compute_pack_t0_t144_const1),16;
                          word(pc + mld_compute_pack_t0_t144_const2),16;
                          word(pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448]
                        [word_sub stackpointer (word 11516),11516]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 11516),11516)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
