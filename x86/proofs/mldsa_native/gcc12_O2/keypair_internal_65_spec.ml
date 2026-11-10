(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the statement. This is the code for                       *)
(* mldsa65_keypair_internal (mld_sign_keypair_internal in sign.c, with       *)
(* mld_sample_pack_s1_s2 inlined) from mldsa-native's portable C             *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which expands the seed with mldsa_shake256 into rho, rho' and the key,    *)
(* samples s1 and s2 from rho' with three calls of                           *)
(* mldsa65_poly_uniform_eta_4x, for the last four polynomials of s2, then    *)
(* the last of s1, the first two of s2 and one with the irrelevant nonce     *)
(* 255, and then the first four of s1, packing each polynomial into the      *)
(* secret key with mldsa65_polyeta_pack, transforms s1 to the NTT domain     *)
(* with mldsa65_polyvecl_ntt, copies rho into the public key, computes t and *)
(* packs t1 into the public key and t0 into the secret key with              *)
(* mld_compute_pack_t0_t165, hashes the public key into tr with              *)
(* mldsa_shake256, packs rho, the key and tr into the secret key with        *)
(* mldsa65_pack_sk_rho_key_tr, and zeroes its buffers, with REP STOSQ and    *)
(* SSE stores, so the direction flag must be clear, as the ABI requires on   *)
(* entry. It aligns its frame to 32 bytes, with a copy of the return address *)
(* (see utils/mldsa_native_realign.ml). It is verified in the whole image    *)
(* (see libmldsa.ml) against mld_keypair_pk_65 and mld_keypair_sk_65 of      *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and the   *)
(* contract memset_full_contract of utils/mldsa_native_libc.ml for the       *)
(* memset that mld_compute_pack_t0_t165 calls, assuming that the expansion   *)
(* of the matrix and the sampling of each polynomial terminate, and shown to *)
(* be constant time and memory safe, with the events depending only on the   *)
(* addresses and the values that the C code declassifies (rho and            *)
(* mld_keypair_declass_65).                                                  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_uniform_eta_4x_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyeta_pack_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_ntt_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/compute_pack_t0_t1_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/pack_sk_rho_key_tr_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_keypair_internal:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  mov     ecx, 0x22
       +0xe  push    QWORD PTR [r10-0x8]
      +0x12  push    rbp
      +0x13  mov     rbp, rsp
      +0x16  push    r15
      +0x18  push    r14
      +0x1a  mov     r14, rdi
      +0x1d  lea     r15, [rbp-0xc30]
      +0x24  push    r13
      +0x26  lea     r13, [rbp-0x1030]
      +0x2d  push    r12
      +0x2f  lea     r12, [rbp-0x1430]
      +0x36  push    r10
      +0x38  push    rbx
      +0x39  mov     rbx, rsi
      +0x3c  lea     rsi, [rbp-0x1530]
      +0x43  sub     rsp, 0x1540
      +0x4a  movdqu  xmm1, XMMWORD PTR [rdx]
      +0x4e  movzx   eax, WORD PTR [rip+0x5261]
                     // mldsa65_keypair_internal_consts
      +0x55  mov     QWORD PTR [rbp-0x1550], rsi
      +0x5c  movdqu  xmm2, XMMWORD PTR [rdx+0x10]
      +0x61  mov     rdx, rsi
      +0x64  mov     esi, 0x80
      +0x69  mov     WORD PTR [rbp-0x1510], ax
      +0x70  lea     rax, [rbp-0x14b0]
      +0x77  mov     rdi, rax
      +0x7a  movaps  XMMWORD PTR [rbp-0x1530], xmm1
      +0x81  movaps  XMMWORD PTR [rbp-0x1520], xmm2
      +0x88  mov     QWORD PTR [rbp-0x1538], rax
      +0x8f  call    mldsa_shake256
     after_mldsa_shake256_1:
      +0x94  sub     rsp, 0x8
      +0x98  mov     rsi, r13
      +0x9b  lea     rdx, [rbx+0x300]
      +0xa2  mov     QWORD PTR [rbp-0x1548], rdx
      +0xa9  lea     rax, [rbp-0x830]
      +0xb0  mov     rdx, r15
      +0xb3  mov     rdi, r12
      +0xb6  push    0xa
      +0xb8  lea     r8, [rbp-0x1490]
      +0xbf  mov     rcx, rax
      +0xc2  mov     r9d, 0x7
      +0xc8  push    0x9
      +0xca  push    0x8
      +0xcc  mov     QWORD PTR [rbp-0x1558], r8
      +0xd3  mov     QWORD PTR [rbp-0x1540], rax
      +0xda  call    mldsa65_poly_uniform_eta_4x
     after_mldsa65_poly_uniform_eta_4x_1:
      +0xdf  add     rsp, 0x20
      +0xe3  lea     rdi, [rbx+0x400]
      +0xea  mov     rsi, r12
      +0xed  call    mldsa65_polyeta_pack
     after_mldsa65_polyeta_pack_1:
      +0xf2  mov     rsi, r13
      +0xf5  lea     rdi, [rbx+0x480]
      +0xfc  call    mldsa65_polyeta_pack
     after_mldsa65_polyeta_pack_2:
     +0x101  mov     rsi, r15
     +0x104  lea     rdi, [rbx+0x500]
     +0x10b  call    mldsa65_polyeta_pack
     after_mldsa65_polyeta_pack_3:
     +0x110  mov     rsi, QWORD PTR [rbp-0x1540]
     +0x117  lea     rdi, [rbx+0x580]
     +0x11e  call    mldsa65_polyeta_pack
     after_mldsa65_polyeta_pack_4:
     +0x123  sub     rsp, 0x8
     +0x127  mov     rcx, r15
     +0x12a  mov     rdx, r13
     +0x12d  push    0xff
     +0x132  lea     rax, [rbp-0x430]
     +0x139  mov     r8, QWORD PTR [rbp-0x1558]
     +0x140  mov     rsi, r12
     +0x143  push    0x6
     +0x145  mov     rdi, rax
     +0x148  mov     r9d, 0x4
     +0x14e  push    0x5
     +0x150  mov     QWORD PTR [rbp-0x1558], rax
     +0x157  mov     QWORD PTR [rbp-0x1560], r8
     +0x15e  call    mldsa65_poly_uniform_eta_4x
     after_mldsa65_poly_uniform_eta_4x_2:
     +0x163  mov     rsi, QWORD PTR [rbp-0x1558]
     +0x16a  add     rsp, 0x20
     +0x16e  lea     rdi, [rbx+0x280]
     +0x175  call    mldsa65_polyeta_pack
     after_mldsa65_polyeta_pack_5:
     +0x17a  mov     rdi, QWORD PTR [rbp-0x1548]
     +0x181  mov     rsi, r12
     +0x184  call    mldsa65_polyeta_pack
     after_mldsa65_polyeta_pack_6:
     +0x189  mov     rsi, r13
     +0x18c  lea     rdi, [rbx+0x380]
     +0x193  call    mldsa65_polyeta_pack
     after_mldsa65_polyeta_pack_7:
     +0x198  sub     rsp, 0x8
     +0x19c  mov     rdx, r15
     +0x19f  xor     r9d, r9d
     +0x1a2  push    0x3
     +0x1a4  mov     r8, QWORD PTR [rbp-0x1560]
     +0x1ab  mov     rsi, r13
     +0x1ae  mov     rdi, r12
     +0x1b1  push    0x2
     +0x1b3  mov     rcx, QWORD PTR [rbp-0x1540]
     +0x1ba  push    0x1
     +0x1bc  call    mldsa65_poly_uniform_eta_4x
     after_mldsa65_poly_uniform_eta_4x_3:
     +0x1c1  add     rsp, 0x20
     +0x1c5  lea     rdi, [rbx+0x80]
     +0x1cc  mov     rsi, r12
     +0x1cf  call    mldsa65_polyeta_pack
     after_mldsa65_polyeta_pack_8:
     +0x1d4  mov     rsi, r13
     +0x1d7  lea     rdi, [rbx+0x100]
     +0x1de  call    mldsa65_polyeta_pack
     after_mldsa65_polyeta_pack_9:
     +0x1e3  mov     rsi, r15
     +0x1e6  lea     rdi, [rbx+0x180]
     +0x1ed  lea     r15, [rbp-0x14f0]
     +0x1f4  call    mldsa65_polyeta_pack
     after_mldsa65_polyeta_pack_10:
     +0x1f9  mov     rsi, QWORD PTR [rbp-0x1540]
     +0x200  lea     rdi, [rbx+0x200]
     +0x207  call    mldsa65_polyeta_pack
     after_mldsa65_polyeta_pack_11:
     +0x20c  mov     rdi, r12
     +0x20f  call    mldsa65_polyvecl_ntt
     after_mldsa65_polyvecl_ntt:
     +0x214  movdqa  xmm3, XMMWORD PTR [rbp-0x14b0]
     +0x21c  lea     rdi, [r14+0x20]
     +0x220  movdqa  xmm4, XMMWORD PTR [rbp-0x14a0]
     +0x228  mov     r8, QWORD PTR [rbp-0x1538]
     +0x22f  mov     rcx, QWORD PTR [rbp-0x1548]
     +0x236  lea     rsi, [rbx+0x600]
     +0x23d  mov     rdx, r12
     +0x240  movups  XMMWORD PTR [r14], xmm3
     +0x244  movups  XMMWORD PTR [r14+0x10], xmm4
     +0x249  call    mld_compute_pack_t0_t165
     after_mld_compute_pack_t0_t165:
     +0x24e  mov     r13d, eax
     +0x251  test    eax, eax
     +0x253  jne     join1
     +0x255  mov     ecx, 0x7a0
     +0x25a  mov     rdx, r14
     +0x25d  mov     esi, 0x40
     +0x262  mov     rdi, r15
     +0x265  call    mldsa_shake256
     after_mldsa_shake256_2:
     +0x26a  mov     rsi, QWORD PTR [rbp-0x1538]
     +0x271  mov     rdx, r15
     +0x274  mov     rdi, rbx
     +0x277  lea     rcx, [rbp-0x1450]
     +0x27e  call    mldsa65_pack_sk_rho_key_tr
     join1: after_mldsa65_pack_sk_rho_key_tr:
     +0x283  xor     eax, eax
     +0x285  mov     rdi, r12
     +0x288  mov     ecx, 0x280
     +0x28d  rep stos QWORD PTR es:[rdi], rax
     +0x290  pxor    xmm0, xmm0
     +0x294  movaps  XMMWORD PTR [rbp-0x14f0], xmm0
     +0x29b  movaps  XMMWORD PTR [rbp-0x14e0], xmm0
     +0x2a2  movaps  XMMWORD PTR [rbp-0x14d0], xmm0
     +0x2a9  movaps  XMMWORD PTR [rbp-0x14c0], xmm0
     +0x2b0  xor     edx, edx
     +0x2b2  movaps  XMMWORD PTR [rbp-0x1530], xmm0
     +0x2b9  mov     WORD PTR [rbp-0x1510], dx
     +0x2c0  mov     rdx, QWORD PTR [rbp-0x1550]
     +0x2c7  movaps  XMMWORD PTR [rbp-0x1520], xmm0
     +0x2ce  mov     rdi, QWORD PTR [rbp-0x1538]
     +0x2d5  mov     ecx, 0x10
     +0x2da  rep stos QWORD PTR es:[rdi], rax
     +0x2dd  mov     rdi, QWORD PTR [rbp-0x1538]
     +0x2e4  test    r13d, r13d
     +0x2e7  jne     join3
     join2:
     +0x2e9  lea     rsp, [rbp-0x30]
     +0x2ed  mov     eax, r13d
     +0x2f0  pop     rbx
     +0x2f1  pop     r10
     +0x2f3  pop     r12
     +0x2f5  pop     r13
     +0x2f7  pop     r14
     +0x2f9  pop     r15
     +0x2fb  pop     rbp
     +0x2fc  lea     rsp, [r10-0x8]
     ret:
     +0x300  ret
     +0x301  nop     DWORD PTR [rax+0x0]
     join3:
     +0x308  lea     rdi, [r14+0x8]
     +0x30c  mov     rcx, r14
     +0x30f  mov     QWORD PTR [r14], 0x0
     +0x316  mov     QWORD PTR [r14+0x798], 0x0
     +0x321  and     rdi, 0xfffffffffffffff8
     +0x325  sub     rcx, rdi
     +0x328  add     ecx, 0x7a0
     +0x32e  shr     ecx, 0x3
     +0x331  rep stos QWORD PTR es:[rdi], rax
     +0x334  lea     rdi, [rbx+0x8]
     +0x338  mov     rcx, rbx
     +0x33b  mov     QWORD PTR [rbx], 0x0
     +0x342  mov     QWORD PTR [rbx+0xfb8], 0x0
     +0x34d  and     rdi, 0xfffffffffffffff8
     +0x351  sub     rcx, rdi
     +0x354  add     ecx, 0xfc0
     +0x35a  shr     ecx, 0x3
     +0x35d  rep stos QWORD PTR es:[rdi], rax
     +0x360  jmp     join2
 ***)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_keypair_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. From the seed SEED (32     *)
(* bytes at seed), the public key at pk (1952 bytes) becomes                 *)
(* mld_keypair_pk_65 SEED and the secret key at sk (4032 bytes)              *)
(* mld_keypair_sk_65 SEED, and the result is 0. The stack is the 43596 bytes *)
(* below the return address of the function, the realignment and the         *)
(* callees.                                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk seed SEED pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 6 5 (mld_keypair_rho 6 5 SEED) /\
          mld_keypair_terminates_65 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43596),43596)] /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43596),43596)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (ea,el)] /\
          ALL (nonoverlapping (stackpointer,8)) [(pk,1952); (sk,4032)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa65_keypair_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [pk; sk; seed] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,32)) s = SEED)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s = word 0 /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_65 SEED j) /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_65 SEED j))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                  memory :> bytes(word_sub stackpointer (word 43596),43596)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, whether each nibble read by  *)
(* the sampling of each polynomial is accepted (mld_keypair_declass_65), the *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the return address, the GOT entry of memset, the region        *)
(* (ea,el) that memset may read and the constants of the function and of the *)
(* callees, and the writes within the keys and the stack.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 6 5 (mld_keypair_rho 6 5 SEED) /\
          mld_keypair_terminates_65 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43596),43596)] /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43596),43596)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (ea,el)] /\
          ALL (nonoverlapping (stackpointer,8)) [(pk,1952); (sk,4032)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa65_keypair_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [pk; sk; seed] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,32)) s = SEED /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s = word 0 /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_65 SEED j) /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_65 SEED j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk seed (mld_keypair_rho 6 5 SEED)
                             (mld_keypair_declass_65 SEED) mf pc
                             (word_sub stackpointer (word 43596))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,1952; sk,4032;
                         word_sub stackpointer (word 43596),43596;
                         stackpointer,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_power2round_consts),32;
                         word(pc + mldsa65_keypair_internal_consts),2;
                         word(pc +
                           mldsa65_polyvec_matrix_expand_eager_consts),4]
                        [pk,1952; sk,4032;
                         word_sub stackpointer (word 43596),43596]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                  memory :> bytes(word_sub stackpointer (word 43596),43596)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 6 5 (mld_keypair_rho 6 5 SEED) /\
          mld_keypair_terminates_65 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43596),43596)] /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43596),43596)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (ea,el)] /\
          ALL (nonoverlapping (stackpointer,8)) [(pk,1952); (sk,4032)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa65_keypair_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [pk; sk; seed] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,32)) s = SEED /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk seed (mld_keypair_rho 6 5 SEED)
                             (mld_keypair_declass_65 SEED) mf pc
                             (word_sub stackpointer (word 43596))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,1952; sk,4032;
                         word_sub stackpointer (word 43596),43596;
                         stackpointer,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_power2round_consts),32;
                         word(pc + mldsa65_keypair_internal_consts),2;
                         word(pc +
                           mldsa65_polyvec_matrix_expand_eager_consts),4]
                        [pk,1952; sk,4032;
                         word_sub stackpointer (word 43596),43596]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                  memory :> bytes(word_sub stackpointer (word 43596),43596)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
