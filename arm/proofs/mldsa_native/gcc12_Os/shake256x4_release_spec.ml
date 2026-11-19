(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Release of a context of four SHAKE256 states. This is the code for        *)
(* mldsa_shake256x4_release from mldsa-native's portable C implementation    *)
(* compiled by gcc 12 with -Os (see mldsa_native/README.md), which is a tail *)
(* call of mldsa_shake128x4_release: the context has the same layout for     *)
(* both. It is verified in the whole image (see libmldsa.ml), using the      *)
(* theorems for mldsa_shake128x4_release in the image and assuming the       *)
(* contracts for memset in utils/mlkem_native_libc.ml. It is also shown to   *)
(* be constant time and memory safe.                                         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake128x4_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa_shake256x4_release:
       +0x0: b       <mldsa_shake128x4_release>
 ***)

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa_shake256x4_release"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!st mf ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (st,800) (word_sub stackpointer (word 16),16) /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 16),16)]
         [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_shake256x4_release) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st] s /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(st,800)) s = 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with the combined  *)
(* contract of memset of utils/mlkem_native_libc_full.ml, and constant time  *)
(* and memory safety alone. The correctness theorem above keeps the weaker   *)
(* contract memset_contract and has its own proof.                           *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/utils/mlkem_native_libc_full.ml";;

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e st pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (st,800) (word_sub stackpointer (word 16),16) /\
           ALLPAIRS nonoverlapping
            [st,800; word_sub stackpointer (word 16),16]
            [word pc,libmldsa_size; word(pc + got_memset),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mldsa_native_libmldsa_gcc12_Os_mc /\
                     read PC s = word (pc + mldsa_shake256x4_release) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [st] s /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     read (memory :> bytes(st,800)) s = 0 /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events st mf pc
                               (word_sub stackpointer (word 16))
                               returnaddress /\
                        memaccess_inbounds e2
                         [st,800; word_sub stackpointer (word 16),16;
                          word(pc + got_memset),8; ea,el]
                         [st,800; word_sub stackpointer (word 16),16]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(st,800);
                   memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e st pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (st,800) (word_sub stackpointer (word 16),16) /\
           ALLPAIRS nonoverlapping
            [st,800; word_sub stackpointer (word 16),16]
            [word pc,libmldsa_size; word(pc + got_memset),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mldsa_native_libmldsa_gcc12_Os_mc /\
                     read PC s = word (pc + mldsa_shake256x4_release) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [st] s /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events st mf pc
                               (word_sub stackpointer (word 16))
                               returnaddress /\
                        memaccess_inbounds e2
                         [st,800; word_sub stackpointer (word 16),16;
                          word(pc + got_memset),8; ea,el]
                         [st,800; word_sub stackpointer (word 16),16]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(st,800);
                   memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
