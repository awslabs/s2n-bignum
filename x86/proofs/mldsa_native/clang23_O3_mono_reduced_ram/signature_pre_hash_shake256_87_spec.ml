(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a message with a SHAKE256 pre-hash (HashML-DSA): the statement.   *)
(* This is the code for mldsa87_signature_pre_hash_shake256                  *)
(* (mld_sign_signature_pre_hash_shake256 in sign.c, an external API          *)
(* function) from mldsa-native's portable C implementation compiled by clang *)
(* 23 with -O3 and MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which *)
(* aligns its frame to 32 bytes, hashes the message into a 64-byte buffer on *)
(* the stack with an inlined SHAKE256 (it absorbs full blocks of 136 bytes   *)
(* with calls of mldsa_keccakf1600_permute, then the rest, pads, permutes    *)
(* and squeezes), returns -9 (MLD_ERR_INVALID_ARG) if ctxlen > 255, and      *)
(* otherwise builds the prefix 1 || ctxlen || ctx || OID || ph of hashalg =  *)
(* MLD_PREHASH_SHAKE_256 (12) on the stack, copying the context with memcpy, *)
(* called through the PLT, unless ctxlen is 0, and signs it with             *)
(* mldsa87_signature_internal. It zeroes the signature on any failure and    *)
(* the prefix with memset, called through the PLT, and the pre-hash with SSE *)
(* stores, so that the direction flag must be clear, as the ABI requires on  *)
(* entry. It is verified in the whole image (see libmldsa.ml), using the     *)
(* theorems for the callees and the contracts memset_full_contract and       *)
(* memcpy_full_contract of utils/mldsa_native_libc.ml for the C library      *)
(* functions that they and it call, and shown to be constant time and memory *)
(* safe.                                                                     *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stubs for memcpy, memset:

    mldsa87_signature_pre_hash_shake256:
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
      +0x1d  mov     r15, r8
      +0x20  mov     QWORD PTR [rsp+0x10], rcx
      +0x25  mov     r13, rdx
      +0x28  mov     r12, rsi
      +0x2b  mov     rbx, rdi
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
      +0x94  lea     r14, [rsp+0x20]                                  |
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
     +0x149  mov     rdi, r14                                       | |
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
     +0x18c  je      +0x3e4                                        ---------+
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
     +0x221  lea     r14, [rsp+0x20]                                      | | |
     +0x226  mov     rdi, r14                                             | | |
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
     +0x2bb  mov     r12d, 0xfffffff7                                     | | |
     +0x2c1  cmp     r15, 0xff                                            | | |
     +0x2c8  ja      join7                                         ---+   | | |
     +0x2ce  mov     r12, QWORD PTR [rbp+0x10]                        |   | | |
     +0x2d2  mov     BYTE PTR [rsp+0x20], 0x1                         |   | | |
     +0x2d7  mov     BYTE PTR [rsp+0x21], r15b                        |   | | |
     +0x2dc  test    r15, r15                                         |   | | |
     +0x2df  je      join6                                         -+ |   | | |
     +0x2e1  lea     rdi, [rsp+0x22]                                | |   | | |
     +0x2e6  mov     rsi, QWORD PTR [rsp+0x10]                      | |   | | |
     +0x2eb  mov     rdx, r15                                       | |   | | |
     +0x2ee  call    memcpy                                         | |   | | |
    join6: after_memcpy:                                            | |   | | |
     +0x2f3  movabs  rax, 0x365014886600906                        <+ |   | | |
     +0x2fd  mov     QWORD PTR [rsp+r15*1+0x22], rax                  |   | | |
     +0x302  mov     DWORD PTR [rsp+r15*1+0x29], 0xc020403            |   | | |
     +0x30b  movaps  xmm0, XMMWORD PTR [rsp+0x180]                    |   | | |
     +0x313  movaps  xmm1, XMMWORD PTR [rsp+0x190]                    |   | | |
     +0x31b  movaps  xmm2, XMMWORD PTR [rsp+0x1a0]                    |   | | |
     +0x323  movaps  xmm3, XMMWORD PTR [rsp+0x1b0]                    |   | | |
     +0x32b  movups  XMMWORD PTR [rsp+r15*1+0x2d], xmm0               |   | | |
     +0x331  movups  XMMWORD PTR [rsp+r15*1+0x3d], xmm1               |   | | |
     +0x337  movups  XMMWORD PTR [rsp+r15*1+0x4d], xmm2               |   | | |
     +0x33d  movups  XMMWORD PTR [rsp+r15*1+0x5d], xmm3               |   | | |
     +0x343  add     r15, 0x4d                                        |   | | |
     +0x347  xor     r14d, r14d                                       |   | | |
     +0x34a  lea     rsi, [rsp+0x20]                                  |   | | |
     +0x34f  mov     rdi, rbx                                         |   | | |
     +0x352  mov     rdx, r15                                         |   | | |
     +0x355  xor     ecx, ecx                                         |   | | |
     +0x357  xor     r8d, r8d                                         |   | | |
     +0x35a  mov     r9, QWORD PTR [rsp+0x18]                         |   | | |
     +0x35f  push    0x0                                              |   | | |
     +0x361  push    r12                                              |   | | |
     +0x363  call    mldsa87_signature_internal                       |   | | |
    after_mldsa87_signature_internal:                                 |   | | |
     +0x368  add     rsp, 0x10                                        |   | | |
     +0x36c  mov     r12d, eax                                        |   | | |
     +0x36f  test    eax, eax                                         |   | | |
     +0x371  je      join8                                         -+ |   | | |
    join7:                                                          | |   | | |
     +0x373  mov     edx, 0x1213                                   <--+   | | |
     +0x378  mov     rdi, rbx                                       |     | | |
     +0x37b  xor     esi, esi                                       |     | | |
     +0x37d  call    memset                                         |     | | |
    after_memset_1:                                                 |     | | |
     +0x382  mov     r14d, r12d                                     |     | | |
    join8:                                                          |     | | |
     +0x385  lea     rbx, [rsp+0x20]                               <+     | | |
     +0x38a  mov     edx, 0x14c                                           | | |
     +0x38f  mov     rdi, rbx                                             | | |
     +0x392  xor     esi, esi                                             | | |
     +0x394  call    memset                                               | | |
    after_memset_2:                                                       | | |
     +0x399  xorps   xmm0, xmm0                                           | | |
     +0x39c  movaps  XMMWORD PTR [rsp+0x180], xmm0                        | | |
     +0x3a4  movaps  XMMWORD PTR [rsp+0x190], xmm0                        | | |
     +0x3ac  movaps  XMMWORD PTR [rsp+0x1a0], xmm0                        | | |
     +0x3b4  movaps  XMMWORD PTR [rsp+0x1b0], xmm0                        | | |
     +0x3bc  lea     rax, [rsp+0x180]                                     | | |
     +0x3c4  mov     eax, r14d                                            | | |
     +0x3c7  lea     rsp, [rbp-0x28]                                      | | |
     +0x3cb  pop     rbx                                                  | | |
     +0x3cc  pop     r12                                                  | | |
     +0x3ce  pop     r13                                                  | | |
     +0x3d0  pop     r14                                                  | | |
     +0x3d2  pop     r15                                                  | | |
     +0x3d4  pop     rbp                                                  | | |
     +0x3d5  xor     ecx, ecx                                             | | |
     +0x3d7  xor     edi, edi                                             | | |
     +0x3d9  xor     edx, edx                                             | | |
     +0x3db  xor     esi, esi                                             | | |
     +0x3dd  xor     r8d, r8d                                             | | |
     +0x3e0  xor     r9d, r9d                                             | | |
    ret:                                                                  | | |
     +0x3e3  ret                                                          | | |
     +0x3e4  cmp     r13, 0x20                                     <--------+ |
     +0x3e8  jae     +0x3ee                                        -+     |   |
     +0x3ea  xor     eax, eax                                       |     |   |
     +0x3ec  jmp     join9                                         ---+   |   |
     +0x3ee  mov     eax, r13d                                     <+ |   |   |
     +0x3f1  and     eax, 0xe0                                        |   |   |
     +0x3f6  xor     ecx, ecx                                         |   |   |
     +0x3f8  nop     DWORD PTR [rax+rax*1+0x0]                        |   |   |
    loop4:                                                            |   |   |
     +0x400  movups  xmm0, XMMWORD PTR [r12+rcx*1]                 <+ |   |   |
     +0x405  movups  xmm1, XMMWORD PTR [r12+rcx*1+0x10]             | |   |   |
     +0x40b  xorps   xmm0, XMMWORD PTR [rsp+rcx*1+0x20]             | |   |   |
     +0x410  xorps   xmm1, XMMWORD PTR [rsp+rcx*1+0x30]             | |   |   |
     +0x415  movaps  XMMWORD PTR [rsp+rcx*1+0x20], xmm0             | |   |   |
     +0x41a  movaps  XMMWORD PTR [rsp+rcx*1+0x30], xmm1             | |   |   |
     +0x41f  add     rcx, 0x20                                      | |   |   |
    loop4_test:                                                     | |   |   |
     +0x423  cmp     rax, rcx                                       | |   |   |
    loop4_back:                                                     | |   |   |
     +0x426  jne     loop4                                         -+ |   |   |
    loop4_exit:                                                       |   |   |
     +0x428  cmp     r13, rax                                         |   |   |
     +0x42b  je      join5                                         -------+   |
     +0x431  test    r13b, 0x1c                                       |       |
     +0x435  je      join3                                            |       |
    join9:                                                            |       |
     +0x43b  mov     rcx, rax                                      <--+       |
     +0x43e  mov     eax, r13d                                                |
     +0x441  and     eax, 0xfc                                                |
     +0x446  cs nop  WORD PTR [rax+rax*1+0x0]                                 |
    loop5:                                                                    |
     +0x450  mov     edx, DWORD PTR [r12+rcx*1]                    <+         |
     +0x454  xor     DWORD PTR [rsp+rcx*1+0x20], edx                |         |
     +0x458  add     rcx, 0x4                                       |         |
    loop5_test:                                                     |         |
     +0x45c  cmp     rax, rcx                                       |         |
    loop5_back:                                                     |         |
     +0x45f  jne     loop5                                         -+         |
    loop5_exit:                                                               |
     +0x461  cmp     r13, rax                                                 |
     +0x464  je      join5                                         -----------+
     +0x46a  jmp     join3

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

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa87_signature_pre_hash_shake256";
    layout_range "plt_memcpy";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* message M of mlen bytes at m, the context C of ctxlen bytes at ctx, the   *)
(* 32 bytes RND at rnd and the secret key skb at sk (4896 bytes), the        *)
(* seventh argument, on the stack above the return address, with PH the pre- *)
(* hash, PRE the prefix 1 || ctxlen || ctx || OID || PH and MU the mu of     *)
(* signing it: the result is -9 if ctxlen > 255, with the signature zeroed,  *)
(* and otherwise that of signing, with the signature mld_sign_sig_87 skb MU  *)
(* RND (zero if signing fails). The function saves RBP, the frame pointer,   *)
(* and five more registers below the return address, lowers RSP by up to 31  *)
(* bytes to align it to 32 bytes, reserves its frame for the sponge state,   *)
(* the pre-hash and the prefix, and the two arguments of                     *)
(* mldsa87_signature_internal on the stack, whose call uses 16462 bytes      *)
(* below them, with its return address: 17045 bytes of stack below the       *)
(* return address in all. The GOT entries of memset and memcpy and the       *)
(* region (ea,el) that they may read are apart from the signature and the    *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen rnd sk skb M C RND PH PRE MU
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0
                (mld_domain_separation_prefix_length 12 ctxlen 64) PRE /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
               mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 17045),17045)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 17045),17045)]
           [(m,mlen); (ctx,ctxlen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s =
                    word(pc + mldsa87_signature_pre_hash_shake256) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; rnd] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8)))
                         s = sk /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_sign_ok_87 skb MU RND then word 0
                     else word 4294967292) /\
                    (!t. t < 4627
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             if 255 < ctxlen then word 0
                             else mld_sign_sig_87 skb MU RND t))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 17045),17045)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, rho and what the C   *)
(* code declassifies in signing (mld_sign_declass_87), with all accesses     *)
(* within the arguments, the stack, the return address and the argument      *)
(* above it, the GOT entries, the region (ea,el) that the C library          *)
(* functions may read and the constants of the callees, and the writes       *)
(* within the signature and the stack.                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen rnd sk skb M C RND PH PRE MU
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0
                (mld_domain_separation_prefix_length 12 ctxlen 64) PRE /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
               mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 17045),17045)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 17045),17045)]
           [(m,mlen); (ctx,ctxlen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s =
                    word(pc + mldsa87_signature_pre_hash_shake256) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; rnd] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8)))
                         s = sk /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_sign_ok_87 skb MU RND then word 0
                     else word 4294967292) /\
                    (!t. t < 4627
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             if 255 < ctxlen then word 0
                             else mld_sign_sig_87 skb MU RND t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen rnd sk
                            (mld_sk_rho skb) (mld_sign_declass_87 skb MU RND)
                            mf mc pc (word_sub stackpointer (word 17045))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; ctx,ctxlen; rnd,32; sk,4896;
                         word_sub stackpointer (word 17045),17045;
                         stackpointer,8; word_add stackpointer (word 8),8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa87_signature_internal_consts),784;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448]
                        [sig,4627; word_sub stackpointer (word 17045),17045]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 17045),17045)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen rnd sk skb M C RND PH PRE MU
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0
                (mld_domain_separation_prefix_length 12 ctxlen 64) PRE /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
               mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 17045),17045)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 17045),17045)]
           [(m,mlen); (ctx,ctxlen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s =
                    word(pc + mldsa87_signature_pre_hash_shake256) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; rnd] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8)))
                         s = sk /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen rnd sk
                            (mld_sk_rho skb) (mld_sign_declass_87 skb MU RND)
                            mf mc pc (word_sub stackpointer (word 17045))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; ctx,ctxlen; rnd,32; sk,4896;
                         word_sub stackpointer (word 17045),17045;
                         stackpointer,8; word_add stackpointer (word 8),8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa87_signature_internal_consts),784;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448]
                        [sig,4627; word_sub stackpointer (word 17045),17045]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 17045),17045)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
