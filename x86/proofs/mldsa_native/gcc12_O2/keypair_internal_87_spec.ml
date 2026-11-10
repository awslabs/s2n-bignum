(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the statement. This is the code for                       *)
(* mldsa87_keypair_internal (mld_sign_keypair_internal in sign.c, with       *)
(* mld_sample_pack_s1_s2 inlined) from mldsa-native's portable C             *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which expands the seed with mldsa_shake256 into rho, rho' and the key,    *)
(* samples s1 and s2 from rho' with four calls of                            *)
(* mldsa87_poly_uniform_eta_4x, for the last four polynomials of s2, the     *)
(* first four, the last three of s1 and one with the irrelevant nonce 255,   *)
(* and the first four of s1, packing each polynomial into the secret key     *)
(* with mldsa87_polyeta_pack, transforms s1 to the NTT domain with           *)
(* mldsa87_polyvecl_ntt, copies rho into the public key, computes t and      *)
(* packs t1 into the public key and t0 into the secret key with              *)
(* mld_compute_pack_t0_t187, hashes the public key into tr with              *)
(* mldsa_shake256, packs rho, the key and tr into the secret key with        *)
(* mldsa87_pack_sk_rho_key_tr, and zeroes its buffers, with REP STOSQ and    *)
(* SSE stores, so the direction flag must be clear, as the ABI requires on   *)
(* entry. It aligns its frame to 32 bytes, with a copy of the return address *)
(* (see utils/mldsa_native_realign.ml). It is verified in the whole image    *)
(* (see libmldsa.ml) against mld_keypair_pk_87 and mld_keypair_sk_87 of      *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and the   *)
(* contract memset_full_contract of utils/mldsa_native_libc.ml for the       *)
(* memset that mld_compute_pack_t0_t187 calls, assuming that the expansion   *)
(* of the matrix and the sampling of each polynomial terminate, and shown to *)
(* be constant time and memory safe, with the events depending only on the   *)
(* addresses and the values that the C code declassifies (rho and            *)
(* mld_keypair_declass_87).                                                  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_uniform_eta_4x_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyeta_pack_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_ntt_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/compute_pack_t0_t1_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/pack_sk_rho_key_tr_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa87_keypair_internal:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  mov     ecx, 0x22
       +0xe  push    QWORD PTR [r10-0x8]
      +0x12  push    rbp
      +0x13  mov     rbp, rsp
      +0x16  push    r15
      +0x18  push    r14
      +0x1a  lea     r15, [rbp-0x1cb0]
      +0x21  lea     r14, [rbp-0x1430]
      +0x28  push    r13
      +0x2a  lea     r13, [rbp-0x1030]
      +0x31  push    r12
      +0x33  lea     r12, [rbp-0x1c30]
      +0x3a  push    r10
      +0x3c  push    rbx
      +0x3d  mov     rbx, rsi
      +0x40  lea     rsi, [rbp-0x1d30]
      +0x47  sub     rsp, 0x1d40
      +0x4e  movdqu  xmm1, XMMWORD PTR [rdx]
      +0x52  movdqu  xmm2, XMMWORD PTR [rdx+0x10]
      +0x57  mov     QWORD PTR [rbp-0x1d70], rdi
      +0x5e  movzx   eax, WORD PTR [rip+0x22b3]
                     // mldsa87_keypair_internal_consts
      +0x65  mov     rdx, rsi
      +0x68  mov     rdi, r15
      +0x6b  mov     QWORD PTR [rbp-0x1d58], rsi
      +0x72  mov     esi, 0x80
      +0x77  movaps  XMMWORD PTR [rbp-0x1d30], xmm1
      +0x7e  movaps  XMMWORD PTR [rbp-0x1d20], xmm2
      +0x85  mov     WORD PTR [rbp-0x1d10], ax
      +0x8c  mov     QWORD PTR [rbp-0x1d40], r15
      +0x93  lea     r15, [rbp-0x1830]
      +0x9a  call    mldsa_shake256
     after_mldsa_shake256_1:
      +0x9f  sub     rsp, 0x8
      +0xa3  mov     rcx, r13
      +0xa6  mov     rdx, r14
      +0xa9  lea     rax, [rbx+0x320]
      +0xb0  mov     r9d, 0xb
      +0xb6  mov     rsi, r15
      +0xb9  mov     rdi, r12
      +0xbc  mov     QWORD PTR [rbp-0x1d48], rax
      +0xc3  lea     rax, [rbp-0x1c90]
      +0xca  push    0xe
      +0xcc  mov     r8, rax
      +0xcf  push    0xd
      +0xd1  push    0xc
      +0xd3  mov     QWORD PTR [rbp-0x1d38], rax
      +0xda  call    mldsa87_poly_uniform_eta_4x
     after_mldsa87_poly_uniform_eta_4x_1:
      +0xdf  add     rsp, 0x20
      +0xe3  lea     rdi, [rbx+0x4a0]
      +0xea  mov     rsi, r12
      +0xed  call    mldsa87_polyeta_pack
     after_mldsa87_polyeta_pack_1:
      +0xf2  mov     rsi, r15
      +0xf5  lea     rdi, [rbx+0x500]
      +0xfc  call    mldsa87_polyeta_pack
     after_mldsa87_polyeta_pack_2:
     +0x101  mov     rsi, r14
     +0x104  lea     rdi, [rbx+0x560]
     +0x10b  call    mldsa87_polyeta_pack
     after_mldsa87_polyeta_pack_3:
     +0x110  mov     rsi, r13
     +0x113  lea     rdi, [rbx+0x5c0]
     +0x11a  call    mldsa87_polyeta_pack
     after_mldsa87_polyeta_pack_4:
     +0x11f  sub     rsp, 0x8
     +0x123  mov     rcx, r13
     +0x126  mov     rdx, r14
     +0x129  push    0xa
     +0x12b  mov     r8, QWORD PTR [rbp-0x1d38]
     +0x132  mov     rsi, r15
     +0x135  mov     rdi, r12
     +0x138  push    0x9
     +0x13a  mov     r9d, 0x7
     +0x140  push    0x8
     +0x142  call    mldsa87_poly_uniform_eta_4x
     after_mldsa87_poly_uniform_eta_4x_2:
     +0x147  mov     rdi, QWORD PTR [rbp-0x1d48]
     +0x14e  add     rsp, 0x20
     +0x152  mov     rsi, r12
     +0x155  call    mldsa87_polyeta_pack
     after_mldsa87_polyeta_pack_5:
     +0x15a  mov     rsi, r15
     +0x15d  lea     rdi, [rbx+0x380]
     +0x164  call    mldsa87_polyeta_pack
     after_mldsa87_polyeta_pack_6:
     +0x169  mov     rsi, r14
     +0x16c  lea     rdi, [rbx+0x3e0]
     +0x173  call    mldsa87_polyeta_pack
     after_mldsa87_polyeta_pack_7:
     +0x178  mov     rsi, r13
     +0x17b  lea     rdi, [rbx+0x440]
     +0x182  call    mldsa87_polyeta_pack
     after_mldsa87_polyeta_pack_8:
     +0x187  sub     rsp, 0x8
     +0x18b  mov     rcx, r12
     +0x18e  lea     rax, [rbp-0x430]
     +0x195  push    0xff
     +0x19a  mov     rdx, rax
     +0x19d  mov     r9d, 0x4
     +0x1a3  lea     r11, [rbp-0x830]
     +0x1aa  push    0x6
     +0x1ac  lea     r10, [rbp-0xc30]
     +0x1b3  mov     r8, QWORD PTR [rbp-0x1d38]
     +0x1ba  mov     rsi, r11
     +0x1bd  push    0x5
     +0x1bf  mov     rdi, r10
     +0x1c2  mov     QWORD PTR [rbp-0x1d68], rax
     +0x1c9  mov     QWORD PTR [rbp-0x1d60], r11
     +0x1d0  mov     QWORD PTR [rbp-0x1d50], r10
     +0x1d7  call    mldsa87_poly_uniform_eta_4x
     after_mldsa87_poly_uniform_eta_4x_3:
     +0x1dc  mov     rsi, QWORD PTR [rbp-0x1d50]
     +0x1e3  add     rsp, 0x20
     +0x1e7  lea     rdi, [rbx+0x200]
     +0x1ee  call    mldsa87_polyeta_pack
     after_mldsa87_polyeta_pack_9:
     +0x1f3  mov     rsi, QWORD PTR [rbp-0x1d60]
     +0x1fa  lea     rdi, [rbx+0x260]
     +0x201  call    mldsa87_polyeta_pack
     after_mldsa87_polyeta_pack_10:
     +0x206  mov     rsi, QWORD PTR [rbp-0x1d68]
     +0x20d  lea     rdi, [rbx+0x2c0]
     +0x214  call    mldsa87_polyeta_pack
     after_mldsa87_polyeta_pack_11:
     +0x219  sub     rsp, 0x8
     +0x21d  mov     rcx, r13
     +0x220  mov     rdx, r14
     +0x223  push    0x3
     +0x225  mov     r8, QWORD PTR [rbp-0x1d38]
     +0x22c  xor     r9d, r9d
     +0x22f  mov     rsi, r15
     +0x232  push    0x2
     +0x234  mov     rdi, r12
     +0x237  push    0x1
     +0x239  call    mldsa87_poly_uniform_eta_4x
     after_mldsa87_poly_uniform_eta_4x_4:
     +0x23e  add     rsp, 0x20
     +0x242  lea     rdi, [rbx+0x80]
     +0x249  mov     rsi, r12
     +0x24c  call    mldsa87_polyeta_pack
     after_mldsa87_polyeta_pack_12:
     +0x251  mov     rsi, r15
     +0x254  lea     rdi, [rbx+0xe0]
     +0x25b  call    mldsa87_polyeta_pack
     after_mldsa87_polyeta_pack_13:
     +0x260  mov     rsi, r14
     +0x263  lea     rdi, [rbx+0x140]
     +0x26a  lea     r14, [rbp-0x1cf0]
     +0x271  call    mldsa87_polyeta_pack
     after_mldsa87_polyeta_pack_14:
     +0x276  mov     rsi, r13
     +0x279  lea     rdi, [rbx+0x1a0]
     +0x280  call    mldsa87_polyeta_pack
     after_mldsa87_polyeta_pack_15:
     +0x285  mov     rdi, r12
     +0x288  call    mldsa87_polyvecl_ntt
     after_mldsa87_polyvecl_ntt:
     +0x28d  mov     r10, QWORD PTR [rbp-0x1d70]
     +0x294  mov     rdx, r12
     +0x297  movdqa  xmm3, XMMWORD PTR [rbp-0x1cb0]
     +0x29f  movdqa  xmm4, XMMWORD PTR [rbp-0x1ca0]
     +0x2a7  mov     r15, QWORD PTR [rbp-0x1d40]
     +0x2ae  lea     rsi, [rbx+0x620]
     +0x2b5  mov     rcx, QWORD PTR [rbp-0x1d48]
     +0x2bc  movups  XMMWORD PTR [r10], xmm3
     +0x2c0  lea     rdi, [r10+0x20]
     +0x2c4  movups  XMMWORD PTR [r10+0x10], xmm4
     +0x2c9  mov     r8, r15
     +0x2cc  mov     QWORD PTR [rbp-0x1d38], r10
     +0x2d3  call    mld_compute_pack_t0_t187
     after_mld_compute_pack_t0_t187:
     +0x2d8  mov     r10, QWORD PTR [rbp-0x1d38]
     +0x2df  test    eax, eax
     +0x2e1  mov     r13d, eax
     +0x2e4  jne     join1
     +0x2e6  mov     rdx, r10
     +0x2e9  mov     ecx, 0xa20
     +0x2ee  mov     esi, 0x40
     +0x2f3  mov     rdi, r14
     +0x2f6  call    mldsa_shake256
     after_mldsa_shake256_2:
     +0x2fb  mov     rdx, r14
     +0x2fe  mov     rsi, r15
     +0x301  mov     rdi, rbx
     +0x304  lea     rcx, [rbp-0x1c50]
     +0x30b  call    mldsa87_pack_sk_rho_key_tr
     after_mldsa87_pack_sk_rho_key_tr:
     +0x310  mov     r10, QWORD PTR [rbp-0x1d38]
     join1:
     +0x317  xor     eax, eax
     +0x319  mov     rdi, r12
     +0x31c  mov     ecx, 0x380
     +0x321  rep stos QWORD PTR es:[rdi], rax
     +0x324  pxor    xmm0, xmm0
     +0x328  movaps  XMMWORD PTR [rbp-0x1cf0], xmm0
     +0x32f  movaps  XMMWORD PTR [rbp-0x1ce0], xmm0
     +0x336  movaps  XMMWORD PTR [rbp-0x1cd0], xmm0
     +0x33d  movaps  XMMWORD PTR [rbp-0x1cc0], xmm0
     +0x344  xor     edx, edx
     +0x346  movaps  XMMWORD PTR [rbp-0x1d30], xmm0
     +0x34d  mov     WORD PTR [rbp-0x1d10], dx
     +0x354  mov     rdx, QWORD PTR [rbp-0x1d58]
     +0x35b  movaps  XMMWORD PTR [rbp-0x1d20], xmm0
     +0x362  mov     rdi, QWORD PTR [rbp-0x1d40]
     +0x369  mov     ecx, 0x10
     +0x36e  rep stos QWORD PTR es:[rdi], rax
     +0x371  mov     rdi, QWORD PTR [rbp-0x1d40]
     +0x378  test    r13d, r13d
     +0x37b  jne     join3
     join2:
     +0x37d  lea     rsp, [rbp-0x30]
     +0x381  mov     eax, r13d
     +0x384  pop     rbx
     +0x385  pop     r10
     +0x387  pop     r12
     +0x389  pop     r13
     +0x38b  pop     r14
     +0x38d  pop     r15
     +0x38f  pop     rbp
     +0x390  lea     rsp, [r10-0x8]
     ret:
     +0x394  ret
     +0x395  nop     DWORD PTR [rax]
     join3:
     +0x398  lea     rdi, [r10+0x8]
     +0x39c  mov     rcx, r10
     +0x39f  mov     QWORD PTR [r10], 0x0
     +0x3a6  mov     QWORD PTR [r10+0xa18], 0x0
     +0x3b1  and     rdi, 0xfffffffffffffff8
     +0x3b5  sub     rcx, rdi
     +0x3b8  add     ecx, 0xa20
     +0x3be  shr     ecx, 0x3
     +0x3c1  rep stos QWORD PTR es:[rdi], rax
     +0x3c4  lea     rdi, [rbx+0x8]
     +0x3c8  mov     rcx, rbx
     +0x3cb  mov     QWORD PTR [rbx], 0x0
     +0x3d2  mov     QWORD PTR [rbx+0x1318], 0x0
     +0x3dd  and     rdi, 0xfffffffffffffff8
     +0x3e1  sub     rcx, rdi
     +0x3e4  add     ecx, 0x1320
     +0x3ea  shr     ecx, 0x3
     +0x3ed  rep stos QWORD PTR es:[rdi], rax
     +0x3f0  jmp     join2
 ***)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_keypair_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. From the seed SEED (32     *)
(* bytes at seed), the public key at pk (2592 bytes) becomes                 *)
(* mld_keypair_pk_87 SEED and the secret key at sk (4896 bytes)              *)
(* mld_keypair_sk_87 SEED, and the result is 0. The stack is the 72260 bytes *)
(* below the return address of the function, the realignment and the         *)
(* callees.                                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk seed SEED pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 8 7 (mld_keypair_rho 8 7 SEED) /\
          mld_keypair_terminates_87 SEED /\
          PAIRWISE nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72260),72260)] /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72260),72260)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (ea,el)] /\
          ALL (nonoverlapping (stackpointer,8)) [(pk,2592); (sk,4896)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_keypair_internal) /\
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
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_87 SEED j) /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_87 SEED j))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                  memory :> bytes(word_sub stackpointer (word 72260),72260)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, whether each nibble read by  *)
(* the sampling of each polynomial is accepted (mld_keypair_declass_87), the *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the return address, the GOT entry of memset, the region        *)
(* (ea,el) that memset may read and the constants of the function and of the *)
(* callees, and the writes within the keys and the stack.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 8 7 (mld_keypair_rho 8 7 SEED) /\
          mld_keypair_terminates_87 SEED /\
          PAIRWISE nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72260),72260)] /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72260),72260)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (ea,el)] /\
          ALL (nonoverlapping (stackpointer,8)) [(pk,2592); (sk,4896)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_keypair_internal) /\
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
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_87 SEED j) /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_87 SEED j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk seed (mld_keypair_rho 8 7 SEED)
                             (mld_keypair_declass_87 SEED) mf pc
                             (word_sub stackpointer (word 72260))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,2592; sk,4896;
                         word_sub stackpointer (word 72260),72260;
                         stackpointer,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_power2round_consts),32;
                         word(pc + mldsa87_keypair_internal_consts),2]
                        [pk,2592; sk,4896;
                         word_sub stackpointer (word 72260),72260]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                  memory :> bytes(word_sub stackpointer (word 72260),72260)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 8 7 (mld_keypair_rho 8 7 SEED) /\
          mld_keypair_terminates_87 SEED /\
          PAIRWISE nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72260),72260)] /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72260),72260)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (ea,el)] /\
          ALL (nonoverlapping (stackpointer,8)) [(pk,2592); (sk,4896)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_keypair_internal) /\
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
                       e2 = f_events pk sk seed (mld_keypair_rho 8 7 SEED)
                             (mld_keypair_declass_87 SEED) mf pc
                             (word_sub stackpointer (word 72260))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,2592; sk,4896;
                         word_sub stackpointer (word 72260),72260;
                         stackpointer,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_power2round_consts),32;
                         word(pc + mldsa87_keypair_internal_consts),2]
                        [pk,2592; sk,4896;
                         word_sub stackpointer (word 72260),72260]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                  memory :> bytes(word_sub stackpointer (word 72260),72260)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
