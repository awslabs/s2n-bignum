(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f1600 permutation of four consecutive states. This is the code for *)
(* mldsa_keccakf1600x4_permute from mldsa-native's portable C implementation *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which calls     *)
(* mldsa_keccakf1600_permute for each of the four states, the last time as a *)
(* tail call. It is verified in the whole image (see libmldsa.ml), using the *)
(* theorems for mldsa_keccakf1600_permute in the image. The specification is *)
(* the same as for sha3_keccak4_f1600, except that the table of round        *)
(* constants is not an argument, since it is part of the image. It is also   *)
(* shown to be constant time and memory safe.                                *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/keccakf1600_permute_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_keccakf1600x4_permute:
       +0x0  push    rbx
       +0x1  mov     rbx, rdi
       +0x4  call    mldsa_keccakf1600_permute
     after_mldsa_keccakf1600_permute_1:
       +0x9  lea     rdi, [rbx+0xc8]
      +0x10  call    mldsa_keccakf1600_permute
     after_mldsa_keccakf1600_permute_2:
      +0x15  lea     rdi, [rbx+0x190]
      +0x1c  call    mldsa_keccakf1600_permute
     after_mldsa_keccakf1600_permute_3:
      +0x21  lea     rdi, [rbx+0x258]
      +0x28  pop     rbx
      +0x29  jmp     mldsa_keccakf1600_permute
 ***)

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_keccakf1600x4_permute"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The function saves RBX below the return address, and each    *)
(* call of mldsa_keccakf1600_permute but the last, which is a tail call,     *)
(* puts its return address below that, with the 256 bytes of the stack that  *)
(* mldsa_keccakf1600_permute uses below it.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a A1 A2 A3 A4 pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (a,800))
            [(word_sub stackpointer (word 272),272); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,800); (word_sub stackpointer (word 272),272)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_keccakf1600x4_permute) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  wordlist_from_memory(a,25) s = A1 /\
                  wordlist_from_memory(word_add a (word 200),25) s = A2 /\
                  wordlist_from_memory(word_add a (word 400),25) s = A3 /\
                  wordlist_from_memory(word_add a (word 600),25) s = A4)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  wordlist_from_memory(a,25) s = keccak 24 A1 /\
                  wordlist_from_memory(word_add a (word 200),25) s =
                  keccak 24 A2 /\
                  wordlist_from_memory(word_add a (word 400),25) s =
                  keccak 24 A3 /\
                  wordlist_from_memory(word_add a (word 600),25) s =
                  keccak 24 A4)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,800);
                memory :> bytes(word_sub stackpointer (word 272),272)])`;;

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same for the states as 1600-bit words, read by wbytes, with the       *)
(* permutation keccak_f1600 of common/fips202.ml (see                        *)
(* utils/keccak_fips202.ml).                                                 *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600_STMT
 =
 `!a (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
    pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (a,800))
            [(word_sub stackpointer (word 272),272); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,800); (word_sub stackpointer (word 272),272)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_keccakf1600x4_permute) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read (memory :> wbytes a) s = S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s = S3)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes a) s = keccak_f1600 S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s =
                  keccak_f1600 S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s =
                  keccak_f1600 S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s =
                  keccak_f1600 S3)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,800);
                memory :> bytes(word_sub stackpointer (word 272),272)])`;;

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600 =
  assume_spec
 MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600_STMT
  ;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, for the states as  *)
(* 1600-bit words, using the FULL theorem of mldsa_keccakf1600_permute: the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* states, the stack frame, the slot of the return address and the table of  *)
(* round constants, and the writes within the states and the stack frame.    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600_STMT =
 `exists f_events.
     forall e a (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
            pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (a,800))
            [(word_sub stackpointer (word 272),272); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,800); (word_sub stackpointer (word 272),272)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_keccakf1600x4_permute) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read (memory :> wbytes a) s = S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s = S3 /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes a) s = keccak_f1600 S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s =
                  keccak_f1600 S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s =
                  keccak_f1600 S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s =
                  keccak_f1600 S3 /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc (word_sub stackpointer (word 272))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [a,800; word_sub stackpointer (word 272),272;
                       stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [a,800; word_sub stackpointer (word 272),272]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,800);
                memory :> bytes(word_sub stackpointer (word 272),272)])`;;

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600 =
  assume_spec
 MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (a,800))
            [(word_sub stackpointer (word 272),272); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,800); (word_sub stackpointer (word 272),272)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_keccakf1600x4_permute) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc (word_sub stackpointer (word 272))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [a,800; word_sub stackpointer (word 272),272;
                       stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [a,800; word_sub stackpointer (word 272),272]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,800);
                memory :> bytes(word_sub stackpointer (word 272),272)])`;;

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
