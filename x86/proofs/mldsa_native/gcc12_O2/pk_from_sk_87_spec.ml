(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the statement. This is the code for       *)
(* mldsa87_pk_from_sk (mld_sign_pk_from_sk in sign.c) from mldsa-native's    *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mldsa_native/README.md), which copies rho, the key and tr from the secret *)
(* key, unpacks s1 with mldsa87_polyvecl_unpack_eta and checks it and s2     *)
(* with mldsa87_polyvecl_chknorm and mldsa87_polyveck_unpack_eta_chknorm,    *)
(* transforms s1 with mldsa87_polyvecl_ntt, recomputes t1 into the public    *)
(* key and t0 into a buffer with mld_compute_pack_t0_t187, compares t0 with  *)
(* that in the secret key, hashes the public key with mldsa_shake256 and     *)
(* compares the hash with tr, all in constant time, and then zeroes the      *)
(* public key if a check failed, and the buffers, with memsets that gcc      *)
(* inlines with REP STOSQ and 128-bit stores, so the direction flag must be  *)
(* clear, as the ABI requires on entry. It is verified in the whole image    *)
(* (see libmldsa.ml) against mld_pk_from_sk_pk and mld_pk_from_sk_valid of   *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and the   *)
(* contract memset_full_contract of utils/mldsa_native_libc.ml for memset,   *)
(* which mld_compute_pack_t0_t187 calls, assuming that the expansion of the  *)
(* matrix terminates (mld_matrix_terminates), and shown to be constant time  *)
(* and memory safe, with the events depending on rho, which is part of the   *)
(* public key, and on the result of the checks, which the C code             *)
(* declassifies.                                                             *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_unpack_eta_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_chknorm_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyveck_unpack_eta_chknorm_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_ntt_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/compute_pack_t0_t1_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa87_pk_from_sk:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r15
       +0x6  push    r14
       +0x8  push    r13
       +0xa  push    r12
       +0xc  mov     r12, rdi
       +0xf  push    rbx
      +0x10  mov     rbx, rsi
      +0x13  sub     rsi, 0xffffffffffffff80
      +0x17  and     rsp, 0xffffffffffffffe0
      +0x1b  sub     rsp, 0x2e00
      +0x22  movdqu  xmm3, XMMWORD PTR [rsi-0x80]
      +0x27  movdqu  xmm4, XMMWORD PTR [rsi-0x70]
      +0x2c  movdqu  xmm5, XMMWORD PTR [rsi-0x60]
      +0x31  movdqu  xmm6, XMMWORD PTR [rsi-0x50]
      +0x36  lea     r14, [rsp+0x1200]
      +0x3e  lea     r15, [rsp+0x100]
      +0x46  movdqu  xmm7, XMMWORD PTR [rsi-0x40]
      +0x4b  movaps  XMMWORD PTR [rsp+0x40], xmm3
      +0x50  movdqu  xmm3, XMMWORD PTR [rsi-0x30]
      +0x55  mov     rdi, r14
      +0x58  movaps  XMMWORD PTR [rsp+0x50], xmm4
      +0x5d  movdqu  xmm4, XMMWORD PTR [rsi-0x20]
      +0x62  movaps  XMMWORD PTR [rsp+0x60], xmm5
      +0x67  movdqu  xmm5, XMMWORD PTR [rsi-0x10]
      +0x6c  movaps  XMMWORD PTR [rsp+0x70], xmm6
      +0x71  movaps  XMMWORD PTR [rsp+0x80], xmm7
      +0x79  movaps  XMMWORD PTR [rsp+0x90], xmm3
      +0x81  movaps  XMMWORD PTR [rsp+0xa0], xmm4
      +0x89  movaps  XMMWORD PTR [rsp+0xb0], xmm5
      +0x91  call    mldsa87_polyvecl_unpack_eta
     after_mldsa87_polyvecl_unpack_eta:
      +0x96  mov     esi, 0x3
      +0x9b  mov     rdi, r14
      +0x9e  call    mldsa87_polyvecl_chknorm
     after_mldsa87_polyvecl_chknorm:
      +0xa3  lea     rcx, [rbx+0x320]
      +0xaa  mov     rdx, r15
      +0xad  mov     esi, 0x3
      +0xb2  mov     rdi, rcx
      +0xb5  mov     QWORD PTR [rsp+0x38], rcx
      +0xba  mov     r13d, eax
      +0xbd  call    mldsa87_polyveck_unpack_eta_chknorm
     after_mldsa87_polyveck_unpack_eta_chknorm:
      +0xc2  mov     rdi, r14
      +0xc5  mov     DWORD PTR [rsp+0x2c], eax
      +0xc9  call    mldsa87_polyvecl_ntt
     after_mldsa87_polyvecl_ntt:
      +0xce  movdqa  xmm6, XMMWORD PTR [rsp+0x40]
      +0xd4  movdqa  xmm7, XMMWORD PTR [rsp+0x50]
      +0xda  lea     r9, [rsp+0x500]
      +0xe2  mov     rcx, QWORD PTR [rsp+0x38]
      +0xe7  lea     r8, [rsp+0x40]
      +0xec  mov     rsi, r9
      +0xef  mov     rdx, r14
      +0xf2  movups  XMMWORD PTR [r12], xmm6
      +0xf7  lea     rdi, [r12+0x20]
      +0xfc  movups  XMMWORD PTR [r12+0x10], xmm7
     +0x102  mov     QWORD PTR [rsp+0x30], r8
     +0x107  mov     QWORD PTR [rsp+0x38], r9
     +0x10c  call    mld_compute_pack_t0_t187
     after_mld_compute_pack_t0_t187:
     +0x111  mov     r9, QWORD PTR [rsp+0x38]
     +0x116  mov     r8, QWORD PTR [rsp+0x30]
     +0x11b  test    eax, eax
     +0x11d  mov     r11d, eax
     +0x120  je      join3
     +0x126  lea     rbx, [rsp+0xc0]
     +0x12e  lea     rdx, [rsp+0x80]
     join1:
     +0x136  lea     rdi, [r12+0x8]
     +0x13b  mov     rcx, r12
     +0x13e  xor     eax, eax
     +0x140  mov     QWORD PTR [r12], 0x0
     +0x148  mov     QWORD PTR [r12+0xa18], 0x0
     +0x154  and     rdi, 0xfffffffffffffff8
     +0x158  sub     rcx, rdi
     +0x15b  add     ecx, 0xa20
     +0x161  shr     ecx, 0x3
     +0x164  rep stos QWORD PTR es:[rdi], rax
     join2:
     +0x167  xor     eax, eax
     +0x169  mov     rdi, r9
     +0x16c  mov     ecx, 0x1a0
     +0x171  rep stos QWORD PTR es:[rdi], rax
     +0x174  mov     ecx, 0x80
     +0x179  mov     rdi, r15
     +0x17c  rep stos QWORD PTR es:[rdi], rax
     +0x17f  mov     ecx, 0x380
     +0x184  mov     rdi, r14
     +0x187  rep stos QWORD PTR es:[rdi], rax
     +0x18a  pxor    xmm0, xmm0
     +0x18e  lea     rax, [rsp+0x60]
     +0x193  movaps  XMMWORD PTR [rsp+0x60], xmm0
     +0x198  movaps  XMMWORD PTR [rsp+0x70], xmm0
     +0x19d  movaps  XMMWORD PTR [rsp+0xc0], xmm0
     +0x1a5  movaps  XMMWORD PTR [rsp+0xd0], xmm0
     +0x1ad  movaps  XMMWORD PTR [rsp+0xe0], xmm0
     +0x1b5  movaps  XMMWORD PTR [rsp+0xf0], xmm0
     +0x1bd  movaps  XMMWORD PTR [rsp+0x80], xmm0
     +0x1c5  movaps  XMMWORD PTR [rsp+0x90], xmm0
     +0x1cd  movaps  XMMWORD PTR [rsp+0xa0], xmm0
     +0x1d5  movaps  XMMWORD PTR [rsp+0xb0], xmm0
     +0x1dd  movaps  XMMWORD PTR [rsp+0x40], xmm0
     +0x1e2  movaps  XMMWORD PTR [rsp+0x50], xmm0
     +0x1e7  lea     rsp, [rbp-0x28]
     +0x1eb  mov     eax, r11d
     +0x1ee  pop     rbx
     +0x1ef  pop     r12
     +0x1f1  pop     r13
     +0x1f3  pop     r14
     +0x1f5  pop     r15
     +0x1f7  pop     rbp
     ret:
     +0x1f8  ret
     +0x1f9  nop     DWORD PTR [rax+0x0]
     join3:
     +0x200  pxor    xmm2, xmm2
     +0x204  xor     eax, eax
     +0x206  movdqa  xmm0, xmm2
     +0x20a  nop     WORD PTR [rax+rax*1+0x0]
     loop1:
     +0x210  movdqu  xmm1, XMMWORD PTR [rbx+rax*1+0x620]
     +0x219  pxor    xmm1, XMMWORD PTR [r9+rax*1]
     +0x21f  add     rax, 0x10
     +0x223  por     xmm0, xmm1
     +0x227  pxor    xmm2, xmm1
     loop1_test:
     +0x22b  cmp     rax, 0xd00
     loop1_back:
     +0x231  jne     loop1
     loop1_exit:
     +0x233  movdqa  xmm1, xmm2
     +0x237  mov     QWORD PTR [rsp+0x18], r8
     +0x23c  psrldq  xmm1, 0x8
     +0x241  mov     QWORD PTR [rsp+0x20], r9
     +0x246  pxor    xmm2, xmm1
     +0x24a  mov     DWORD PTR [rsp+0x30], r11d
     +0x24f  movdqa  xmm1, xmm2
     +0x253  psrldq  xmm1, 0x4
     +0x258  pxor    xmm2, xmm1
     +0x25c  movdqa  xmm1, xmm2
     +0x260  psrldq  xmm1, 0x2
     +0x265  pxor    xmm2, xmm1
     +0x269  movdqa  xmm1, xmm2
     +0x26d  psrldq  xmm1, 0x1
     +0x272  pxor    xmm2, xmm1
     +0x276  movdqa  xmm1, xmm0
     +0x27a  psrldq  xmm1, 0x8
     +0x27f  movd    edx, xmm2
     +0x283  por     xmm0, xmm1
     +0x287  movdqa  xmm1, xmm0
     +0x28b  psrldq  xmm1, 0x4
     +0x290  por     xmm0, xmm1
     +0x294  movdqa  xmm1, xmm0
     +0x298  psrldq  xmm1, 0x2
     +0x29d  por     xmm0, xmm1
     +0x2a1  movdqa  xmm1, xmm0
     +0x2a5  psrldq  xmm1, 0x1
     +0x2aa  por     xmm0, xmm1
     +0x2ae  movd    eax, xmm0
     +0x2b2  movzx   eax, al
     +0x2b5  neg     rax
     +0x2b8  sar     rax, 0x20
     +0x2bc  xor     eax, edx
     +0x2be  lea     rbx, [rsp+0xc0]
     +0x2c6  xor     eax, edx
     +0x2c8  mov     ecx, 0xa20
     +0x2cd  mov     rdx, r12
     +0x2d0  mov     esi, 0x40
     +0x2d5  mov     rdi, rbx
     +0x2d8  mov     BYTE PTR [rsp+0x38], al
     +0x2dc  call    mldsa_shake256
     after_mldsa_shake256:
     +0x2e1  pxor    xmm1, xmm1
     +0x2e5  mov     r8, QWORD PTR [rsp+0x18]
     +0x2ea  xor     eax, eax
     +0x2ec  mov     r9, QWORD PTR [rsp+0x20]
     +0x2f1  mov     r11d, DWORD PTR [rsp+0x30]
     +0x2f6  movdqa  xmm0, xmm1
     +0x2fa  lea     rdx, [rsp+0x80]
     loop2:
     +0x302  movdqa  xmm2, XMMWORD PTR [rbx+rax*1]
     +0x307  pxor    xmm2, XMMWORD PTR [rdx+rax*1]
     +0x30c  add     rax, 0x10
     +0x310  por     xmm0, xmm2
     +0x314  pxor    xmm1, xmm2
     loop2_test:
     +0x318  cmp     rax, 0x40
     loop2_back:
     +0x31c  jne     loop2
     loop2_exit:
     +0x31e  movdqa  xmm2, xmm1
     +0x322  psrldq  xmm2, 0x8
     +0x327  pxor    xmm1, xmm2
     +0x32b  movdqa  xmm2, xmm1
     +0x32f  psrldq  xmm2, 0x4
     +0x334  pxor    xmm1, xmm2
     +0x338  movdqa  xmm2, xmm1
     +0x33c  psrldq  xmm2, 0x2
     +0x341  pxor    xmm1, xmm2
     +0x345  movdqa  xmm2, xmm1
     +0x349  psrldq  xmm2, 0x1
     +0x34e  pxor    xmm1, xmm2
     +0x352  movd    esi, xmm1
     +0x356  movdqa  xmm1, xmm0
     +0x35a  psrldq  xmm1, 0x8
     +0x35f  por     xmm0, xmm1
     +0x363  movdqa  xmm1, xmm0
     +0x367  psrldq  xmm1, 0x4
     +0x36c  por     xmm0, xmm1
     +0x370  movdqa  xmm1, xmm0
     +0x374  psrldq  xmm1, 0x2
     +0x379  por     xmm0, xmm1
     +0x37d  movdqa  xmm1, xmm0
     +0x381  psrldq  xmm1, 0x1
     +0x386  por     xmm0, xmm1
     +0x38a  movd    ecx, xmm0
     +0x38e  movzx   ecx, cl
     +0x391  neg     rcx
     +0x394  mov     rax, rcx
     +0x397  sar     rax, 0x20
     +0x39b  xor     eax, esi
     +0x39d  or      r13b, BYTE PTR [rsp+0x2c]
     +0x3a2  xor     eax, esi
     +0x3a4  or      r13b, BYTE PTR [rsp+0x38]
     +0x3a9  or      r13d, eax
     +0x3ac  test    r13b, r13b
     +0x3af  je      join2
     +0x3b5  mov     r11d, 0xfffffff9
     +0x3bb  jmp     join1
 ***)

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_pk_from_sk"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The secret key at sk is    *)
(* the 4896 bytes skb; if it passes the checks, mld_pk_from_sk_valid, the    *)
(* public key at pk becomes mld_pk_from_sk_pk and the result is 0, and       *)
(* otherwise the public key is zeroed and the result is MLD_ERR_INVALID_KEY  *)
(* (-7 as a 32-bit integer). The expansion of the matrix from rho is assumed *)
(* to terminate. The function saves RBP, the frame pointer, and five more    *)
(* registers below the return address, lowers RSP by up to 31 bytes to align *)
(* it to 32 bytes, and then reserves 11776 bytes for its buffers and spills, *)
(* below which the call of mld_compute_pack_t0_t187 uses 64677 bytes, with   *)
(* its return address: 76532 bytes of stack below the return address in all. *)
(* The GOT entry of memset and the region (ea,el) that memset may read are   *)
(* apart from the public key and the stack.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk skb pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          nonoverlapping (pk,2592) (word_sub stackpointer (word 76532),76532) /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (word_sub stackpointer (word 76532),76532)]
           [(sk,4896); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (ea,el)] /\
          nonoverlapping (pk,2592) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_pk_from_sk) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2 96
                          skb
                     then word 0 else word 4294967289) /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             if mld_pk_from_sk_valid 8 7 2
                                  mld_polyeta_unpack_2 96 skb
                             then mld_pk_from_sk_pk 7 mld_polyeta_unpack_2 96
                                   skb j
                             else word 0))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592);
                  memory :> bytes(word_sub stackpointer (word 76532),76532)])`;;

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the result of the checks,    *)
(* the address of memset and the stack, with all accesses within the         *)
(* arguments, the stack, the return address, the GOT entry of memset, the    *)
(* region (ea,el) that memset may read and the constants of the callees, and *)
(* the writes within the public key and the stack.                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk skb pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          nonoverlapping (pk,2592) (word_sub stackpointer (word 76532),76532) /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (word_sub stackpointer (word 76532),76532)]
           [(sk,4896); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (ea,el)] /\
          nonoverlapping (pk,2592) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_pk_from_sk) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2 96
                          skb
                     then word 0 else word 4294967289) /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             if mld_pk_from_sk_valid 8 7 2
                                  mld_polyeta_unpack_2 96 skb
                             then mld_pk_from_sk_pk 7 mld_polyeta_unpack_2 96
                                   skb j
                             else word 0) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk (mld_sk_rho skb)
                              (mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2
                                96 skb)
                              mf pc (word_sub stackpointer (word 76532))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sk,4896; pk,2592;
                         word_sub stackpointer (word 76532),76532;
                         stackpointer,8; word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_power2round_consts),32]
                        [pk,2592; word_sub stackpointer (word 76532),76532]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592);
                  memory :> bytes(word_sub stackpointer (word 76532),76532)])`;;

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk skb pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          nonoverlapping (pk,2592) (word_sub stackpointer (word 76532),76532) /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (word_sub stackpointer (word 76532),76532)]
           [(sk,4896); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (ea,el)] /\
          nonoverlapping (pk,2592) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_pk_from_sk) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk (mld_sk_rho skb)
                              (mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2
                                96 skb)
                              mf pc (word_sub stackpointer (word 76532))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sk,4896; pk,2592;
                         word_sub stackpointer (word 76532),76532;
                         stackpointer,8; word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_power2round_consts),32]
                        [pk,2592; word_sub stackpointer (word 76532),76532]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592);
                  memory :> bytes(word_sub stackpointer (word 76532),76532)])`;;

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
