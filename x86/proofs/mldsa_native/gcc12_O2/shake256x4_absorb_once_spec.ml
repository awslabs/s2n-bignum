(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing four messages of the same length into four SHAKE256 states: the *)
(* statement. This is the code for mldsa_shake256x4_absorb_once from         *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which zeroes the 800 bytes of the context with a *)
(* memset that gcc inlines with REP STOSQ, so the direction flag must be     *)
(* clear, as the ABI requires on entry, and then calls                       *)
(* mld_keccak_absorb_once_x4 with the rate 136 of SHAKE256, passing the      *)
(* length of the messages, its seventh argument, on the stack. It is         *)
(* verified in the whole image (see libmldsa.ml), using the theorems for     *)
(* mld_keccak_absorb_once_x4 in the image. The stack is the 24 bytes of the  *)
(* function, the return address of the call and the 384 bytes used by        *)
(* mld_keccak_absorb_once_x4 below it. It is also shown to be constant time  *)
(* and memory safe.                                                          *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/keccak_absorb_once_x4_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_shake256x4_absorb_once:
       +0x0  sub     rsp, 0x10
       +0x4  mov     r10, rdi
       +0x7  mov     QWORD PTR [rdi], 0x0
       +0xe  xor     eax, eax
      +0x10  mov     QWORD PTR [rdi+0x318], 0x0
      +0x1b  lea     rdi, [rdi+0x8]
      +0x1f  mov     r11, rcx
      +0x22  mov     rcx, r10
      +0x25  and     rdi, 0xfffffffffffffff8
      +0x29  sub     rcx, rdi
      +0x2c  add     ecx, 0x320
      +0x32  shr     ecx, 0x3
      +0x35  rep stos QWORD PTR es:[rdi], rax
      +0x38  push    r9
      +0x3a  mov     rcx, rdx
      +0x3d  mov     r9, r8
      +0x40  mov     rdx, rsi
      +0x43  mov     r8, r11
      +0x46  mov     esi, 0x88
      +0x4b  mov     rdi, r10
      +0x4e  call    mld_keccak_absorb_once_x4
     after_mld_keccak_absorb_once_x4:
      +0x53  add     rsp, 0x18
     ret:
      +0x57  ret
 ***)

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_shake256x4_absorb_once"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!st m0 m1 m2 m3 mlen M0 M1 M2 M3 pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (st,800))
            [(word_sub stackpointer (word 416),416); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 416),416)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
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
                memory :> bytes(word_sub stackpointer (word 416),416)])`;;

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, and constant time  *)
(* and memory safety alone. The events depend on the addresses and the       *)
(* length of the messages only.                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e st m0 m1 m2 m3 mlen M0 M1 M2 M3 pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (st,800))
            [(word_sub stackpointer (word 416),416); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 416),416)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
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
                            (word_sub stackpointer (word 416)) returnaddress /\
                     memaccess_inbounds e2
                      [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                       word_sub stackpointer (word 416),416; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [st,800; word_sub stackpointer (word 416),416]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 416),416)])`;;

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e st m0 m1 m2 m3 mlen pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (st,800))
            [(word_sub stackpointer (word 416),416); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 416),416)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
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
                            (word_sub stackpointer (word 416)) returnaddress /\
                     memaccess_inbounds e2
                      [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                       word_sub stackpointer (word 416),416; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [st,800; word_sub stackpointer (word 416),416]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 416),416)])`;;

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
