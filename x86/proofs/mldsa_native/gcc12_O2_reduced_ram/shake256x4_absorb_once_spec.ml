(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing four messages of the same length into four SHAKE256 states: the *)
(* statement. This is the code for mldsa_shake256x4_absorb_once from         *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 and  *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which zeroes the 800  *)
(* bytes of the context, inlined with REP STOSQ, so the direction flag must  *)
(* be clear, as the ABI requires on entry, and then absorbs the messages     *)
(* with the rate 136 of SHAKE256 as mld_keccak_absorb_once_x4 does, which    *)
(* gcc has inlined here, with the first byte 0x1F of the padding: as         *)
(* absorbing on one state does, using mldsa_keccakf1600x4_xor_bytes and      *)
(* mldsa_keccakf1600x4_permute, passing the seventh argument of              *)
(* mldsa_keccakf1600x4_xor_bytes, the number of bytes, on the stack as a     *)
(* 64-bit word, of which the callee reads 32 bits. It is verified in the     *)
(* whole image (see libmldsa.ml), using the theorems for those functions in  *)
(* the image. The stack is the 88 bytes of the function, 16 bytes for the    *)
(* seventh argument of a call, its return address and the 272 bytes used by  *)
(* mldsa_keccakf1600x4_permute below them, 384 bytes below the return        *)
(* address in all. It is also shown to be constant time and memory safe.     *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "common/fips202/fips202.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/keccakf1600x4_xor_bytes_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/keccakf1600x4_permute_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa_shake256x4_absorb_once:
       +0x0  push    r15
       +0x2  mov     r15, rdi
       +0x5  add     rdi, 0x8
       +0x9  xor     eax, eax
       +0xb  push    r14
       +0xd  mov     r14, r8
      +0x10  push    r13
      +0x12  mov     r13, rcx
      +0x15  mov     rcx, r15
      +0x18  push    r12
      +0x1a  mov     r12, rdx
      +0x1d  push    rbp
      +0x1e  mov     rbp, rsi
      +0x21  push    rbx
      +0x22  mov     rbx, r9
      +0x25  sub     rsp, 0x28
      +0x29  mov     QWORD PTR [rdi-0x8], 0x0
      +0x31  mov     QWORD PTR [rdi+0x310], 0x0
      +0x3c  and     rdi, 0xfffffffffffffff8
      +0x40  sub     rcx, rdi
      +0x43  add     ecx, 0x320
      +0x49  shr     ecx, 0x3
      +0x4c  rep stos QWORD PTR es:[rdi], rax
      +0x4f  mov     BYTE PTR [rsp+0x1f], 0x1f
      +0x54  cmp     r9, 0x87
      +0x5b  jbe     join1
      +0x5d  nop     DWORD PTR [rax]
     loop1:
      +0x60  sub     rsp, 0x8
      +0x64  xor     r9d, r9d
      +0x67  mov     r8, r14
      +0x6a  mov     rcx, r13
      +0x6d  push    0x88
      +0x72  mov     rdx, r12
      +0x75  mov     rsi, rbp
      +0x78  mov     rdi, r15
      +0x7b  sub     rbx, 0x88
      +0x82  add     rbp, 0x88
      +0x89  add     r12, 0x88
      +0x90  add     r13, 0x88
      +0x97  add     r14, 0x88
      +0x9e  call    mldsa_keccakf1600x4_xor_bytes
     after_mldsa_keccakf1600x4_xor_bytes_1:
      +0xa3  mov     rdi, r15
      +0xa6  call    mldsa_keccakf1600x4_permute
     after_mldsa_keccakf1600x4_permute:
      +0xab  pop     r9
      +0xad  pop     r10
     loop1_test:
      +0xaf  cmp     rbx, 0x87
     loop1_back:
      +0xb6  ja      loop1
     join1: loop1_exit:
      +0xb8  mov     eax, ebx
      +0xba  test    rbx, rbx
      +0xbd  jne     join3
     join2:
      +0xbf  lea     rbx, [rsp+0x1f]
      +0xc4  sub     rsp, 0x8
      +0xc8  mov     r9d, eax
      +0xcb  mov     rdi, r15
      +0xce  push    0x1
      +0xd0  mov     r8, rbx
      +0xd3  mov     rcx, rbx
      +0xd6  mov     rdx, rbx
      +0xd9  mov     rsi, rbx
      +0xdc  call    mldsa_keccakf1600x4_xor_bytes
     after_mldsa_keccakf1600x4_xor_bytes_2:
      +0xe1  mov     rdx, rbx
      +0xe4  mov     r8, rbx
      +0xe7  mov     rcx, rbx
      +0xea  mov     rsi, rbx
      +0xed  mov     rdi, r15
      +0xf0  mov     r9d, 0x87
      +0xf6  mov     BYTE PTR [rsp+0x2f], 0x80
      +0xfb  mov     DWORD PTR [rsp], 0x1
     +0x102  call    mldsa_keccakf1600x4_xor_bytes
     after_mldsa_keccakf1600x4_xor_bytes_3:
     +0x107  pop     rax
     +0x108  pop     rdx
     +0x109  add     rsp, 0x28
     +0x10d  pop     rbx
     +0x10e  pop     rbp
     +0x10f  pop     r12
     +0x111  pop     r13
     +0x113  pop     r14
     +0x115  pop     r15
     ret1:
     +0x117  ret
     +0x118  nop     DWORD PTR [rax+rax*1+0x0]
     join3:
     +0x120  mov     DWORD PTR [rsp+0xc], ebx
     +0x124  sub     rsp, 0x8
     +0x128  xor     r9d, r9d
     +0x12b  mov     r8, r14
     +0x12e  push    rbx
     +0x12f  mov     rdi, r15
     +0x132  mov     rcx, r13
     +0x135  mov     rdx, r12
     +0x138  mov     rsi, rbp
     +0x13b  call    mldsa_keccakf1600x4_xor_bytes
     after_mldsa_keccakf1600x4_xor_bytes_4:
     +0x140  cmp     rbx, 0x87
     +0x147  pop     rdi
     +0x148  pop     r8
     +0x14a  mov     eax, DWORD PTR [rsp+0xc]
     +0x14e  jne     join2
     +0x154  lea     rsi, [rsp+0x1f]
     +0x159  or      BYTE PTR [rsp+0x1f], 0x80
     +0x15e  sub     rsp, 0x8
     +0x162  mov     rdi, r15
     +0x165  push    0x1
     +0x167  mov     rcx, rsi
     +0x16a  mov     r8, rsi
     +0x16d  mov     rdx, rsi
     +0x170  mov     r9d, 0x87
     +0x176  call    mldsa_keccakf1600x4_xor_bytes
     after_mldsa_keccakf1600x4_xor_bytes_5:
     +0x17b  pop     rcx
     +0x17c  pop     rsi
     +0x17d  add     rsp, 0x28
     +0x181  pop     rbx
     +0x182  pop     rbp
     +0x183  pop     r12
     +0x185  pop     r13
     +0x187  pop     r14
     +0x189  pop     r15
     ret2:
     +0x18b  ret
 ***)

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa_shake256x4_absorb_once"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!st m0 m1 m2 m3 mlen M0 M1 M2 M3 pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (st,800))
            [(word_sub stackpointer (word 384),384); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 384),384)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa_shake256x4_absorb_once) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [st; m0; m1; m2; m3; word mlen] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(m0,mlen)) s = M0 /\
                  read (memory :> bytes(m1,mlen)) s = M1 /\
                  read (memory :> bytes(m2,mlen)) s = M2 /\
                  read (memory :> bytes(m3,mlen)) s = M3)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb 136
                     (M0 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 136 0x1F mlen))
                     (mlen DIV 136))
                   (word((M0 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 136 0x1F mlen)) DIV
                         2 EXP (8 * 136 * mlen DIV 136) MOD
                         2 EXP (8 * 136))) /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  word_xor
                   (keccak_absorb 136
                     (M1 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 136 0x1F mlen))
                     (mlen DIV 136))
                   (word((M1 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 136 0x1F mlen)) DIV
                         2 EXP (8 * 136 * mlen DIV 136) MOD
                         2 EXP (8 * 136))) /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  word_xor
                   (keccak_absorb 136
                     (M2 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 136 0x1F mlen))
                     (mlen DIV 136))
                   (word((M2 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 136 0x1F mlen)) DIV
                         2 EXP (8 * 136 * mlen DIV 136) MOD
                         2 EXP (8 * 136))) /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  word_xor
                   (keccak_absorb 136
                     (M3 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 136 0x1F mlen))
                     (mlen DIV 136))
                   (word((M3 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 136 0x1F mlen)) DIV
                         2 EXP (8 * 136 * mlen DIV 136) MOD
                         2 EXP (8 * 136))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 384),384)])`;;

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, and constant time  *)
(* and memory safety alone. The events depend on the addresses and the       *)
(* length of the messages only.                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e st m0 m1 m2 m3 mlen M0 M1 M2 M3 pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (st,800))
            [(word_sub stackpointer (word 384),384); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 384),384)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa_shake256x4_absorb_once) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [st; m0; m1; m2; m3; word mlen] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(m0,mlen)) s = M0 /\
                  read (memory :> bytes(m1,mlen)) s = M1 /\
                  read (memory :> bytes(m2,mlen)) s = M2 /\
                  read (memory :> bytes(m3,mlen)) s = M3 /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb 136
                     (M0 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 136 0x1F mlen))
                     (mlen DIV 136))
                   (word((M0 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 136 0x1F mlen)) DIV
                         2 EXP (8 * 136 * mlen DIV 136) MOD
                         2 EXP (8 * 136))) /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  word_xor
                   (keccak_absorb 136
                     (M1 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 136 0x1F mlen))
                     (mlen DIV 136))
                   (word((M1 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 136 0x1F mlen)) DIV
                         2 EXP (8 * 136 * mlen DIV 136) MOD
                         2 EXP (8 * 136))) /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  word_xor
                   (keccak_absorb 136
                     (M2 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 136 0x1F mlen))
                     (mlen DIV 136))
                   (word((M2 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 136 0x1F mlen)) DIV
                         2 EXP (8 * 136 * mlen DIV 136) MOD
                         2 EXP (8 * 136))) /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  word_xor
                   (keccak_absorb 136
                     (M3 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 136 0x1F mlen))
                     (mlen DIV 136))
                   (word((M3 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 136 0x1F mlen)) DIV
                         2 EXP (8 * 136 * mlen DIV 136) MOD
                         2 EXP (8 * 136))) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events m0 m1 m2 m3 st mlen pc
                            (word_sub stackpointer (word 384)) returnaddress /\
                     memaccess_inbounds e2
                      [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                       word_sub stackpointer (word 384),384; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [st,800; word_sub stackpointer (word 384),384]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 384),384)])`;;

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e st m0 m1 m2 m3 mlen pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (st,800))
            [(word_sub stackpointer (word 384),384); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 384),384)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa_shake256x4_absorb_once) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [st; m0; m1; m2; m3; word mlen] s /\
                  (read DF s <=> false) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events m0 m1 m2 m3 st mlen pc
                            (word_sub stackpointer (word 384)) returnaddress /\
                     memaccess_inbounds e2
                      [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                       word_sub stackpointer (word 384),384; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [st,800; word_sub stackpointer (word 384),384]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 384),384)])`;;

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
