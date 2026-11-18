(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing a whole message into a SHAKE128 state. This is the code for     *)
(* mlkem_shake128_absorb_once from mlkem-native's portable C implementation  *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which calls     *)
(* mlk_keccak_absorb_once with the rate 168 of SHAKE128 and the first byte   *)
(* 0x1F of its padding, as a tail call. It is verified in the whole image    *)
(* (see libmlkem.ml), using the theorems for mlk_keccak_absorb_once in the   *)
(* image.                                                                    *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/keccak_absorb_once_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_shake128_absorb_once:
       +0x0: mov    rcx,rdx
       +0x3: mov    r8d,0x1f
       +0x9: mov    rdx,rsi
       +0xc: mov    esi,0xa8
      +0x11: jmp    <mlk_keccak_absorb_once>
 ***)

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_shake128_absorb_once"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The result is as for mlk_keccak_absorb_once, with      *)
(* r = 168 and p = 0x1F as in shake128 in common/fips202/fips202.ml. The     *)
(* state is the first 200 bytes of the context.                              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!st m mlen M pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        PAIRWISE nonoverlapping
         [(st,200); (m,mlen); (word_sub stackpointer (word 320),328)] /\
        ALL (nonoverlapping (word pc,libmlkem_size))
         [(st,200); (word_sub stackpointer (word 320),328)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem_shake128_absorb_once) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [st; m; word mlen] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(m,mlen)) s = M)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb 168
                     (M + 2 EXP (8 * mlen) *
                          num_of_bytelist(keccak_pad 168 0x1F mlen))
                     (mlen DIV 168))
                   (word((M + 2 EXP (8 * mlen) *
                              num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                         2 EXP (8 * 168 * mlen DIV 168) MOD 2 EXP (8 * 168))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(st,200);
                memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e st m mlen pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       PAIRWISE nonoverlapping
        [st,200; m,mlen; word_sub stackpointer (word 320),328] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [st,200; word_sub stackpointer (word 320),328]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + mlkem_shake128_absorb_once) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [st; m; word mlen] s /\
                 (read DF s <=> false) /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m st mlen pc
                           (word_sub stackpointer (word 320)) returnaddress /\
                    memaccess_inbounds e2
                     [m,mlen; st,200; word_sub stackpointer (word 320),328;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,200; word_sub stackpointer (word 320),320]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using that   *)
(* of mlk_keccak_absorb_once.                                                *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e st m mlen M pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       PAIRWISE nonoverlapping
        [st,200; m,mlen; word_sub stackpointer (word 320),328] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [st,200; word_sub stackpointer (word 320),328]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + mlkem_shake128_absorb_once) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [st; m; word mlen] s /\
                 (read DF s <=> false) /\
                 read (memory :> bytes(m,mlen)) s = M /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 read (memory :> wbytes st) s =
                 word_xor
                  (keccak_absorb 168
                    (M + 2 EXP (8 * mlen) *
                         num_of_bytelist(keccak_pad 168 0x1F mlen))
                    (mlen DIV 168))
                  (word((M + 2 EXP (8 * mlen) *
                             num_of_bytelist(keccak_pad 168 0x1F mlen)) DIV
                        2 EXP (8 * 168 * mlen DIV 168) MOD 2 EXP (8 * 168))) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m st mlen pc
                           (word_sub stackpointer (word 320)) returnaddress /\
                    memaccess_inbounds e2
                     [m,mlen; st,200; word_sub stackpointer (word 320),328;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [st,200; word_sub stackpointer (word 320),320]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(st,200);
               memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
