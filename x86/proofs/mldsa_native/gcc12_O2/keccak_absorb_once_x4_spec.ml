(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing four messages of the same length into four Keccak states, with  *)
(* the padding: the statement. This is the code for the static function      *)
(* mld_keccak_absorb_once_x4 from mldsa-native's portable C implementation   *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), where the       *)
(* compiler has made the first byte 0x1F of the padding a constant. It works *)
(* as absorbing on one state does, using mldsa_keccakf1600x4_xor_bytes and   *)
(* mldsa_keccakf1600x4_permute, except that the states are not zeroed first: *)
(* that is done by its callers. Its seventh argument, the length of the      *)
(* messages, is on the stack, and it passes the seventh argument of          *)
(* mldsa_keccakf1600x4_xor_bytes, the number of bytes, on the stack as a     *)
(* 64-bit word, of which the callee reads 32 bits. Its code is the same as   *)
(* that of mlk_keccak_absorb_once_x4.constprop.0 in the gcc 12 -O2 build of  *)
(* mlkem-native for x86-64, apart from the addresses, so the statement and   *)
(* proof are those of mlkem_native_keccak_absorb_once_x4_gcc12_O2.ml of the  *)
(* x86 proofs of mlkem-native. It is verified in the whole image (see        *)
(* libmldsa.ml), using the theorems for those functions in the image. The    *)
(* stack is the 88 bytes of the function, 16 bytes for the seventh argument  *)
(* of a call, its return address and the 272 bytes used by                   *)
(* mldsa_keccakf1600x4_permute below them, 384 bytes below the return        *)
(* address in all. It is also shown to be constant time and memory safe.     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "common/fips202.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/keccakf1600x4_xor_bytes_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/keccakf1600x4_permute_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mld_keccak_absorb_once_x4:
       +0x0  push    r15
       +0x2  mov     r15, r8
       +0x5  mov     r8, r9
       +0x8  push    r14
       +0xa  mov     r14, rdi
       +0xd  push    r13
       +0xf  mov     r13, rcx
      +0x12  push    r12
      +0x14  mov     r12, rdx
      +0x17  push    rbp
      +0x18  push    rbx
      +0x19  mov     ebx, esi
      +0x1b  sub     rsp, 0x28
      +0x1f  mov     rbp, QWORD PTR [rsp+0x60]
      +0x24  mov     DWORD PTR [rsp+0xc], esi
      +0x28  mov     BYTE PTR [rsp+0x1f], 0x1f
      +0x2d  cmp     rbp, rbx
      +0x30  jb      join1
      +0x32  nop     WORD PTR [rax+rax*1+0x0]
     loop1:
      +0x38  sub     rsp, 0x8
      +0x3c  xor     r9d, r9d
      +0x3f  mov     rcx, r15
      +0x42  mov     rdx, r13
      +0x45  mov     eax, DWORD PTR [rsp+0x14]
      +0x49  mov     rsi, r12
      +0x4c  mov     rdi, r14
      +0x4f  sub     rbp, rbx
      +0x52  add     r12, rbx
      +0x55  add     r13, rbx
      +0x58  add     r15, rbx
      +0x5b  push    rax
      +0x5c  mov     QWORD PTR [rsp+0x10], r8
      +0x61  call    mldsa_keccakf1600x4_xor_bytes
     after_mldsa_keccakf1600x4_xor_bytes_1:
      +0x66  mov     rdi, r14
      +0x69  call    mldsa_keccakf1600x4_permute
     after_mldsa_keccakf1600x4_permute:
      +0x6e  mov     r8, QWORD PTR [rsp+0x10]
      +0x73  pop     r9
      +0x75  pop     r10
      +0x77  add     r8, rbx
     loop1_test:
      +0x7a  cmp     rbp, rbx
     loop1_back:
      +0x7d  jae     loop1
     join1: loop1_exit:
      +0x7f  mov     eax, DWORD PTR [rsp+0xc]
      +0x83  mov     ebx, ebp
      +0x85  sub     eax, 0x1
      +0x88  mov     DWORD PTR [rsp], eax
      +0x8b  test    rbp, rbp
      +0x8e  jne     join3
     join2:
      +0x90  lea     rbp, [rsp+0x1f]
      +0x95  sub     rsp, 0x8
      +0x99  mov     r9d, ebx
      +0x9c  mov     rdi, r14
      +0x9f  push    0x1
      +0xa1  mov     r8, rbp
      +0xa4  mov     rcx, rbp
      +0xa7  mov     rdx, rbp
      +0xaa  mov     rsi, rbp
      +0xad  call    mldsa_keccakf1600x4_xor_bytes
     after_mldsa_keccakf1600x4_xor_bytes_2:
      +0xb2  mov     r9d, DWORD PTR [rsp+0x10]
      +0xb7  mov     rdx, rbp
      +0xba  mov     r8, rbp
      +0xbd  mov     rcx, rbp
      +0xc0  mov     rsi, rbp
      +0xc3  mov     rdi, r14
      +0xc6  mov     BYTE PTR [rsp+0x2f], 0x80
      +0xcb  mov     DWORD PTR [rsp], 0x1
      +0xd2  call    mldsa_keccakf1600x4_xor_bytes
     after_mldsa_keccakf1600x4_xor_bytes_3:
      +0xd7  pop     rax
      +0xd8  pop     rdx
      +0xd9  add     rsp, 0x28
      +0xdd  pop     rbx
      +0xde  pop     rbp
      +0xdf  pop     r12
      +0xe1  pop     r13
      +0xe3  pop     r14
      +0xe5  pop     r15
     ret1:
      +0xe7  ret
      +0xe8  nop     DWORD PTR [rax+rax*1+0x0]
     join3:
      +0xf0  sub     rsp, 0x8
      +0xf4  mov     rdi, r14
      +0xf7  xor     r9d, r9d
      +0xfa  mov     rcx, r15
      +0xfd  push    rbp
      +0xfe  mov     rdx, r13
     +0x101  mov     rsi, r12
     +0x104  call    mldsa_keccakf1600x4_xor_bytes
     after_mldsa_keccakf1600x4_xor_bytes_4:
     +0x109  mov     eax, DWORD PTR [rsp+0x10]
     +0x10d  pop     rdi
     +0x10e  pop     r8
     +0x110  cmp     rax, rbp
     +0x113  jne     join2
     +0x119  lea     rsi, [rsp+0x1f]
     +0x11e  or      BYTE PTR [rsp+0x1f], 0x80
     +0x123  mov     r9d, ebp
     +0x126  mov     rdi, r14
     +0x129  sub     rsp, 0x8
     +0x12d  mov     rcx, rsi
     +0x130  mov     r8, rsi
     +0x133  mov     rdx, rsi
     +0x136  push    0x1
     +0x138  call    mldsa_keccakf1600x4_xor_bytes
     after_mldsa_keccakf1600x4_xor_bytes_5:
     +0x13d  pop     rcx
     +0x13e  pop     rsi
     +0x13f  add     rsp, 0x28
     +0x143  pop     rbx
     +0x144  pop     rbp
     +0x145  pop     r12
     +0x147  pop     r13
     +0x149  pop     r14
     +0x14b  pop     r15
     ret2:
     +0x14d  ret
 ***)

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mld_keccak_absorb_once_x4"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!st r m0 m1 m2 m3 mlen M0 M1 M2 M3 pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        0 < r /\ r <= 200 /\
        ALL (nonoverlapping (st,800))
            [(word_sub stackpointer (word 384),384); (stackpointer,8);
             (word_add stackpointer (word 8),8)] /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 384),384)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mld_keccak_absorb_once_x4) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [st; word r; m0; m1; m2; m3] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  word mlen /\
                  read (memory :> bytes(st,800)) s = 0 /\
                  read (memory :> bytes(m0,mlen)) s = M0 /\
                  read (memory :> bytes(m1,mlen)) s = M1 /\
                  read (memory :> bytes(m2,mlen)) s = M2 /\
                  read (memory :> bytes(m3,mlen)) s = M3)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb r
                     (M0 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M0 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  word_xor
                   (keccak_absorb r
                     (M1 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M1 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  word_xor
                   (keccak_absorb r
                     (M2 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M2 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  word_xor
                   (keccak_absorb r
                     (M3 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M3 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 384),384)])`;;

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, and constant time  *)
(* and memory safety alone. The events depend on the length of the messages  *)
(* and the rate only.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e st r m0 m1 m2 m3 mlen M0 M1 M2 M3 pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        0 < r /\ r <= 200 /\
        ALL (nonoverlapping (st,800))
            [(word_sub stackpointer (word 384),384); (stackpointer,8);
             (word_add stackpointer (word 8),8)] /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 384),384)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mld_keccak_absorb_once_x4) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [st; word r; m0; m1; m2; m3] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  word mlen /\
                  read (memory :> bytes(st,800)) s = 0 /\
                  read (memory :> bytes(m0,mlen)) s = M0 /\
                  read (memory :> bytes(m1,mlen)) s = M1 /\
                  read (memory :> bytes(m2,mlen)) s = M2 /\
                  read (memory :> bytes(m3,mlen)) s = M3 /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb r
                     (M0 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M0 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  word_xor
                   (keccak_absorb r
                     (M1 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M1 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  word_xor
                   (keccak_absorb r
                     (M2 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M2 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  word_xor
                   (keccak_absorb r
                     (M3 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M3 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events m0 m1 m2 m3 st r mlen pc
                            (word_sub stackpointer (word 384)) returnaddress /\
                     memaccess_inbounds e2
                      [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                       word_sub stackpointer (word 384),384; stackpointer,8;
                       word_add stackpointer (word 8),8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [st,800; word_sub stackpointer (word 384),384]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 384),384)])`;;

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e st r m0 m1 m2 m3 mlen pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        0 < r /\ r <= 200 /\
        ALL (nonoverlapping (st,800))
            [(word_sub stackpointer (word 384),384); (stackpointer,8);
             (word_add stackpointer (word 8),8)] /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 384),384)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mld_keccak_absorb_once_x4) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [st; word r; m0; m1; m2; m3] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  word mlen /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events m0 m1 m2 m3 st r mlen pc
                            (word_sub stackpointer (word 384)) returnaddress /\
                     memaccess_inbounds e2
                      [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                       word_sub stackpointer (word 384),384; stackpointer,8;
                       word_add stackpointer (word 8),8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [st,800; word_sub stackpointer (word 384),384]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 384),384)])`;;

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
