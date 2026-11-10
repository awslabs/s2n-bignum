(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the statement. This is the code for                       *)
(* mldsa44_keypair_internal (mld_sign_keypair_internal in sign.c, with       *)
(* mld_sample_pack_s1_s2 inlined) from mldsa-native's portable C             *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which expands the seed with mldsa_shake256 into rho, rho' and the key,    *)
(* samples s1 and s2 from rho' with two calls of                             *)
(* mldsa44_poly_uniform_eta_4x, for s2 and then s1, packing each polynomial  *)
(* into the secret key with mldsa44_polyeta_pack, transforms s1 to the NTT   *)
(* domain with mldsa44_polyvecl_ntt, copies rho into the public key,         *)
(* computes t and packs t1 into the public key and t0 into the secret key    *)
(* with mld_compute_pack_t0_t144, hashes the public key into tr with         *)
(* mldsa_shake256, packs rho, the key and tr into the secret key with        *)
(* mldsa44_pack_sk_rho_key_tr, and zeroes its buffers, with REP STOSQ and    *)
(* SSE stores, so the direction flag must be clear, as the ABI requires on   *)
(* entry. It aligns its frame to 32 bytes, with a copy of the return address *)
(* (see utils/mldsa_native_realign.ml). It is verified in the whole image    *)
(* (see libmldsa.ml) against mld_keypair_pk_44 and mld_keypair_sk_44 of      *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and the   *)
(* contract memset_full_contract of utils/mldsa_native_libc.ml for the       *)
(* memset that mld_compute_pack_t0_t144 calls, assuming that the expansion   *)
(* of the matrix and the sampling of each polynomial terminate, and shown to *)
(* be constant time and memory safe, with the events depending only on the   *)
(* addresses and the values that the C code declassifies (rho and            *)
(* mld_keypair_declass_44).                                                  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_uniform_eta_4x_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyeta_pack_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_ntt_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/compute_pack_t0_t1_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/pack_sk_rho_key_tr_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_keypair_internal:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  mov     ecx, 0x22
       +0xe  push    QWORD PTR [r10-0x8]
      +0x12  push    rbp
      +0x13  mov     rbp, rsp
      +0x16  push    r15
      +0x18  push    r14
      +0x1a  lea     r15, [rbp-0xc30]
      +0x21  lea     r14, [rbp-0x830]
      +0x28  push    r13
      +0x2a  mov     r13, rdi
      +0x2d  push    r12
      +0x2f  lea     r12, [rbp-0x1030]
      +0x36  push    r10
      +0x38  push    rbx
      +0x39  mov     rbx, rsi
      +0x3c  lea     rsi, [rbp-0x1130]
      +0x43  sub     rsp, 0x1140
      +0x4a  movdqu  xmm1, XMMWORD PTR [rdx]
      +0x4e  movzx   eax, WORD PTR [rip+0x804b]
                     // mldsa44_keypair_internal_consts
      +0x55  mov     QWORD PTR [rbp-0x1150], rsi
      +0x5c  movdqu  xmm2, XMMWORD PTR [rdx+0x10]
      +0x61  mov     rdx, rsi
      +0x64  mov     esi, 0x80
      +0x69  mov     WORD PTR [rbp-0x1110], ax
      +0x70  lea     rax, [rbp-0x10b0]
      +0x77  mov     rdi, rax
      +0x7a  movaps  XMMWORD PTR [rbp-0x1130], xmm1
      +0x81  movaps  XMMWORD PTR [rbp-0x1120], xmm2
      +0x88  mov     QWORD PTR [rbp-0x1138], rax
      +0x8f  call    mldsa_shake256
     after_mldsa_shake256_1:
      +0x94  sub     rsp, 0x8
      +0x98  mov     rsi, r15
      +0x9b  lea     rdx, [rbx+0x200]
      +0xa2  mov     QWORD PTR [rbp-0x1148], rdx
      +0xa9  lea     rax, [rbp-0x430]
      +0xb0  mov     rdx, r14
      +0xb3  mov     rdi, r12
      +0xb6  push    0x7
      +0xb8  mov     rcx, rax
      +0xbb  lea     r8, [rbp-0x1090]
      +0xc2  mov     r9d, 0x4
      +0xc8  push    0x6
      +0xca  push    0x5
      +0xcc  mov     QWORD PTR [rbp-0x1140], rax
      +0xd3  mov     QWORD PTR [rbp-0x1158], r8
      +0xda  call    mldsa44_poly_uniform_eta_4x
     after_mldsa44_poly_uniform_eta_4x_1:
      +0xdf  mov     rdi, QWORD PTR [rbp-0x1148]
      +0xe6  add     rsp, 0x20
      +0xea  mov     rsi, r12
      +0xed  call    mldsa44_polyeta_pack
     after_mldsa44_polyeta_pack_1:
      +0xf2  mov     rsi, r15
      +0xf5  lea     rdi, [rbx+0x260]
      +0xfc  call    mldsa44_polyeta_pack
     after_mldsa44_polyeta_pack_2:
     +0x101  mov     rsi, r14
     +0x104  lea     rdi, [rbx+0x2c0]
     +0x10b  call    mldsa44_polyeta_pack
     after_mldsa44_polyeta_pack_3:
     +0x110  mov     rsi, QWORD PTR [rbp-0x1140]
     +0x117  lea     rdi, [rbx+0x320]
     +0x11e  call    mldsa44_polyeta_pack
     after_mldsa44_polyeta_pack_4:
     +0x123  sub     rsp, 0x8
     +0x127  mov     rdx, r14
     +0x12a  xor     r9d, r9d
     +0x12d  push    0x3
     +0x12f  mov     r8, QWORD PTR [rbp-0x1158]
     +0x136  mov     rsi, r15
     +0x139  mov     rdi, r12
     +0x13c  push    0x2
     +0x13e  mov     rcx, QWORD PTR [rbp-0x1140]
     +0x145  push    0x1
     +0x147  call    mldsa44_poly_uniform_eta_4x
     after_mldsa44_poly_uniform_eta_4x_2:
     +0x14c  add     rsp, 0x20
     +0x150  lea     rdi, [rbx+0x80]
     +0x157  mov     rsi, r12
     +0x15a  call    mldsa44_polyeta_pack
     after_mldsa44_polyeta_pack_5:
     +0x15f  mov     rsi, r15
     +0x162  lea     rdi, [rbx+0xe0]
     +0x169  lea     r15, [rbp-0x10f0]
     +0x170  call    mldsa44_polyeta_pack
     after_mldsa44_polyeta_pack_6:
     +0x175  mov     rsi, r14
     +0x178  lea     rdi, [rbx+0x140]
     +0x17f  call    mldsa44_polyeta_pack
     after_mldsa44_polyeta_pack_7:
     +0x184  mov     rsi, QWORD PTR [rbp-0x1140]
     +0x18b  lea     rdi, [rbx+0x1a0]
     +0x192  call    mldsa44_polyeta_pack
     after_mldsa44_polyeta_pack_8:
     +0x197  mov     rdi, r12
     +0x19a  call    mldsa44_polyvecl_ntt
     after_mldsa44_polyvecl_ntt:
     +0x19f  movdqa  xmm3, XMMWORD PTR [rbp-0x10b0]
     +0x1a7  lea     rdi, [r13+0x20]
     +0x1ab  movdqa  xmm4, XMMWORD PTR [rbp-0x10a0]
     +0x1b3  mov     r8, QWORD PTR [rbp-0x1138]
     +0x1ba  mov     rcx, QWORD PTR [rbp-0x1148]
     +0x1c1  lea     rsi, [rbx+0x380]
     +0x1c8  mov     rdx, r12
     +0x1cb  movups  XMMWORD PTR [r13+0x0], xmm3
     +0x1d0  movups  XMMWORD PTR [r13+0x10], xmm4
     +0x1d5  call    mld_compute_pack_t0_t144
     after_mld_compute_pack_t0_t144:
     +0x1da  mov     r14d, eax
     +0x1dd  test    eax, eax
     +0x1df  jne     join1
     +0x1e1  mov     ecx, 0x520
     +0x1e6  mov     rdx, r13
     +0x1e9  mov     esi, 0x40
     +0x1ee  mov     rdi, r15
     +0x1f1  call    mldsa_shake256
     after_mldsa_shake256_2:
     +0x1f6  mov     rsi, QWORD PTR [rbp-0x1138]
     +0x1fd  mov     rdx, r15
     +0x200  mov     rdi, rbx
     +0x203  lea     rcx, [rbp-0x1050]
     +0x20a  call    mldsa44_pack_sk_rho_key_tr
     join1: after_mldsa44_pack_sk_rho_key_tr:
     +0x20f  xor     eax, eax
     +0x211  mov     rdi, r12
     +0x214  mov     ecx, 0x200
     +0x219  rep stos QWORD PTR es:[rdi], rax
     +0x21c  pxor    xmm0, xmm0
     +0x220  movaps  XMMWORD PTR [rbp-0x10f0], xmm0
     +0x227  movaps  XMMWORD PTR [rbp-0x10e0], xmm0
     +0x22e  movaps  XMMWORD PTR [rbp-0x10d0], xmm0
     +0x235  movaps  XMMWORD PTR [rbp-0x10c0], xmm0
     +0x23c  xor     edx, edx
     +0x23e  movaps  XMMWORD PTR [rbp-0x1130], xmm0
     +0x245  mov     WORD PTR [rbp-0x1110], dx
     +0x24c  mov     rdx, QWORD PTR [rbp-0x1150]
     +0x253  movaps  XMMWORD PTR [rbp-0x1120], xmm0
     +0x25a  mov     rdi, QWORD PTR [rbp-0x1138]
     +0x261  mov     ecx, 0x10
     +0x266  rep stos QWORD PTR es:[rdi], rax
     +0x269  mov     rdi, QWORD PTR [rbp-0x1138]
     +0x270  test    r14d, r14d
     +0x273  jne     join3
     join2:
     +0x275  lea     rsp, [rbp-0x30]
     +0x279  mov     eax, r14d
     +0x27c  pop     rbx
     +0x27d  pop     r10
     +0x27f  pop     r12
     +0x281  pop     r13
     +0x283  pop     r14
     +0x285  pop     r15
     +0x287  pop     rbp
     +0x288  lea     rsp, [r10-0x8]
     ret:
     +0x28c  ret
     +0x28d  nop     DWORD PTR [rax]
     join3:
     +0x290  lea     rdi, [r13+0x8]
     +0x294  mov     rcx, r13
     +0x297  mov     QWORD PTR [r13+0x0], 0x0
     +0x29f  mov     QWORD PTR [r13+0x518], 0x0
     +0x2aa  and     rdi, 0xfffffffffffffff8
     +0x2ae  sub     rcx, rdi
     +0x2b1  add     ecx, 0x520
     +0x2b7  shr     ecx, 0x3
     +0x2ba  rep stos QWORD PTR es:[rdi], rax
     +0x2bd  lea     rdi, [rbx+0x8]
     +0x2c1  mov     rcx, rbx
     +0x2c4  mov     QWORD PTR [rbx], 0x0
     +0x2cb  mov     QWORD PTR [rbx+0x9f8], 0x0
     +0x2d6  and     rdi, 0xfffffffffffffff8
     +0x2da  sub     rcx, rdi
     +0x2dd  add     ecx, 0xa00
     +0x2e3  shr     ecx, 0x3
     +0x2e6  rep stos QWORD PTR es:[rdi], rax
     +0x2e9  jmp     join2
 ***)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_keypair_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. From the seed SEED (32     *)
(* bytes at seed), the public key at pk (1312 bytes) becomes                 *)
(* mld_keypair_pk_44 SEED and the secret key at sk (2560 bytes)              *)
(* mld_keypair_sk_44 SEED, and the result is 0. The stack is the 28228 bytes *)
(* below the return address of the function, the realignment and the         *)
(* callees.                                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk seed SEED pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 4 4 (mld_keypair_rho 4 4 SEED) /\
          mld_keypair_terminates_44 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 28228),28228)] /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 28228),28228)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (ea,el)] /\
          ALL (nonoverlapping (stackpointer,8)) [(pk,1312); (sk,2560)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_keypair_internal) /\
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
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_44 SEED j) /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_44 SEED j))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312); memory :> bytes(sk,2560);
                  memory :> bytes(word_sub stackpointer (word 28228),28228)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, whether each nibble read by  *)
(* the sampling of each polynomial is accepted (mld_keypair_declass_44), the *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the return address, the GOT entry of memset, the region        *)
(* (ea,el) that memset may read and the constants of the function and of the *)
(* callees, and the writes within the keys and the stack.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 4 4 (mld_keypair_rho 4 4 SEED) /\
          mld_keypair_terminates_44 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 28228),28228)] /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 28228),28228)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (ea,el)] /\
          ALL (nonoverlapping (stackpointer,8)) [(pk,1312); (sk,2560)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_keypair_internal) /\
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
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_44 SEED j) /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_44 SEED j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk seed (mld_keypair_rho 4 4 SEED)
                             (mld_keypair_declass_44 SEED) mf pc
                             (word_sub stackpointer (word 28228))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,1312; sk,2560;
                         word_sub stackpointer (word 28228),28228;
                         stackpointer,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_power2round_consts),32;
                         word(pc + mldsa44_keypair_internal_consts),2]
                        [pk,1312; sk,2560;
                         word_sub stackpointer (word 28228),28228]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312); memory :> bytes(sk,2560);
                  memory :> bytes(word_sub stackpointer (word 28228),28228)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 4 4 (mld_keypair_rho 4 4 SEED) /\
          mld_keypair_terminates_44 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 28228),28228)] /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 28228),28228)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (ea,el)] /\
          ALL (nonoverlapping (stackpointer,8)) [(pk,1312); (sk,2560)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_keypair_internal) /\
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
                       e2 = f_events pk sk seed (mld_keypair_rho 4 4 SEED)
                             (mld_keypair_declass_44 SEED) mf pc
                             (word_sub stackpointer (word 28228))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,1312; sk,2560;
                         word_sub stackpointer (word 28228),28228;
                         stackpointer,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_power2round_consts),32;
                         word(pc + mldsa44_keypair_internal_consts),2]
                        [pk,1312; sk,2560;
                         word_sub stackpointer (word 28228),28228]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312); memory :> bytes(sk,2560);
                  memory :> bytes(word_sub stackpointer (word 28228),28228)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
