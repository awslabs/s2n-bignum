(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing four messages of the same length into four SHAKE128 states.     *)
(* This is the code for mlkem_shake128x4_absorb_once from mlkem-native's     *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which zeroes the 800 bytes of the context with   *)
(* an inline memset, as mlkem_shake128_release does for one state, and then  *)
(* calls mlk_keccak_absorb_once_x4 with the rate 168 of SHAKE128, passing    *)
(* the length of the messages on the stack. It is verified in the whole      *)
(* image (see libmlkem.ml), using the theorems for mlk_keccak_absorb_once_x4 *)
(* in the image. The memset uses REP STOSQ, so the specifications assume     *)
(* that the direction flag DF is clear, as the ABI requires on entry.        *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/keccak_absorb_once_x4_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_shake128x4_absorb_once:
       +0x0: sub    rsp,0x10
       +0x4: mov    r10,rdi
       +0x7: mov    QWORD PTR [rdi],0x0
       +0xe: xor    eax,eax
      +0x10: mov    QWORD PTR [rdi+0x318],0x0
      +0x1b: lea    rdi,[rdi+0x8]
      +0x1f: mov    r11,rcx
      +0x22: mov    rcx,r10
      +0x25: and    rdi,0xfffffffffffffff8
      +0x29: sub    rcx,rdi
      +0x2c: add    ecx,0x320
      +0x32: shr    ecx,0x3
      +0x35: rep    stos QWORD PTR es:[rdi],rax
      +0x38: push   r9
      +0x3a: mov    rcx,rdx
      +0x3d: mov    r9,r8
      +0x40: mov    rdx,rsi
      +0x43: mov    r8,r11
      +0x46: mov    esi,0xa8
      +0x4b: mov    rdi,r10
      +0x4e: call   <mlk_keccak_absorb_once_x4.constprop.0>
      +0x53: add    rsp,0x18
      +0x57: ret
 ***)

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_shake128x4_absorb_once"];;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using that   *)
(* of mlk_keccak_absorb_once_x4. The result is as for that function on each  *)
(* message, with r = 168 and p = 0x1F as in shake128 in                      *)
(* common/fips202/fips202.ml, the states being the four consecutive 200-byte *)
(* parts of the context.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e st m0 m1 m2 m3 mlen M0 M1 M2 M3 pc stackpointer
            returnaddress.
       aligned 16 (word pc:int64) /\
       nonoverlapping (st,800) (word_sub stackpointer (word 416),424) /\
       ALLPAIRS nonoverlapping
        [st,800; word_sub stackpointer (word 416),424]
        [m0,mlen; m1,mlen; m2,mlen; m3,mlen; word pc,libmlkem_size]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + mlkem_shake128x4_absorb_once) /\
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
                  (keccak_absorb 168
                    (M0 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 168 0x1F mlen))
                    (mlen DIV 168))
                  (word((M0 + 2 EXP (8 * mlen) *
                         num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                        2 EXP (8 * 168 * mlen DIV 168) MOD
                        2 EXP (8 * 168))) /\
                 read (memory :> wbytes (word_add st (word 200))) s =
                 word_xor
                  (keccak_absorb 168
                    (M1 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 168 0x1F mlen))
                    (mlen DIV 168))
                  (word((M1 + 2 EXP (8 * mlen) *
                         num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                        2 EXP (8 * 168 * mlen DIV 168) MOD
                        2 EXP (8 * 168))) /\
                 read (memory :> wbytes (word_add st (word 400))) s =
                 word_xor
                  (keccak_absorb 168
                    (M2 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 168 0x1F mlen))
                    (mlen DIV 168))
                  (word((M2 + 2 EXP (8 * mlen) *
                         num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                        2 EXP (8 * 168 * mlen DIV 168) MOD
                        2 EXP (8 * 168))) /\
                 read (memory :> wbytes (word_add st (word 600))) s =
                 word_xor
                  (keccak_absorb 168
                    (M3 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 168 0x1F mlen))
                    (mlen DIV 168))
                  (word((M3 + 2 EXP (8 * mlen) *
                         num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                        2 EXP (8 * 168 * mlen DIV 168) MOD
                        2 EXP (8 * 168))) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m0 m1 m2 m3 st mlen pc
                           (word_sub stackpointer (word 416)) returnaddress /\
                    memaccess_inbounds e2
                     [m0,mlen; m1,mlen; m2,mlen; m3,mlen; st,800;
                      word_sub stackpointer (word 416),424;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,800; word_sub stackpointer (word 416),416]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 416),416)])`;;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* The correctness and safety theorems alone, from the combined one.         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!st m0 m1 m2 m3 mlen M0 M1 M2 M3 pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        nonoverlapping (st,800) (word_sub stackpointer (word 416),424) /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 416),424)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen); (word pc,libmlkem_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem_shake128x4_absorb_once) /\
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
                   (keccak_absorb 168
                     (M0 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 168 0x1F mlen))
                     (mlen DIV 168))
                   (word((M0 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                         2 EXP (8 * 168 * mlen DIV 168) MOD
                         2 EXP (8 * 168))) /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  word_xor
                   (keccak_absorb 168
                     (M1 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 168 0x1F mlen))
                     (mlen DIV 168))
                   (word((M1 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                         2 EXP (8 * 168 * mlen DIV 168) MOD
                         2 EXP (8 * 168))) /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  word_xor
                   (keccak_absorb 168
                     (M2 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 168 0x1F mlen))
                     (mlen DIV 168))
                   (word((M2 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                         2 EXP (8 * 168 * mlen DIV 168) MOD
                         2 EXP (8 * 168))) /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  word_xor
                   (keccak_absorb 168
                     (M3 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 168 0x1F mlen))
                     (mlen DIV 168))
                   (word((M3 + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                         2 EXP (8 * 168 * mlen DIV 168) MOD
                         2 EXP (8 * 168))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 416),416)])`;;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e st m0 m1 m2 m3 mlen pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       nonoverlapping (st,800) (word_sub stackpointer (word 416),424) /\
       ALLPAIRS nonoverlapping
        [st,800; word_sub stackpointer (word 416),424]
        [m0,mlen; m1,mlen; m2,mlen; m3,mlen; word pc,libmlkem_size]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + mlkem_shake128x4_absorb_once) /\
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
                      word_sub stackpointer (word 416),424;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,800; word_sub stackpointer (word 416),416]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 416),416)])`;;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
