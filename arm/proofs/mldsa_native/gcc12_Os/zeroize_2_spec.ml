(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Zeroing of a buffer. This is the code for mld_zeroize_2 from              *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -Os      *)
(* (see mldsa_native/README.md), which zeroes the n bytes at ptr with memset *)
(* from the C library, called through the PLT of the image. With -Os the     *)
(* functions that zeroize a local buffer call it instead of zeroing inline.  *)
(* The image has six copies of it, mld_zeroize_1 to mld_zeroize_6, one for   *)
(* each translation unit, which differ only in the offset of the branch to   *)
(* the PLT; each has its own spec and proof file. It is verified in the      *)
(* whole image (see libmldsa.ml), assuming the contracts for memset in       *)
(* utils/mlkem_native_libc.ml. It is also shown to be constant time and      *)
(* memory safe.                                                              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mld_zeroize_2:
       +0x0: stp     x19, x30, [sp, #-16]!
       +0x4: mov     x2, x1
       +0x8: mov     x19, x0
       +0xc: mov     w1, #0x0
      +0x10: bl      <memset@plt>
      +0x14: ldp     x19, x30, [sp], #16
      +0x18: ret
    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_ZEROIZE_2_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mld_zeroize_2"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_ZEROIZE_2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ptr n mf ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\
        n < 2 EXP 64 /\
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (ptr,n) (word_sub stackpointer (word 16),16) /\
        ALLPAIRS nonoverlapping
         [(ptr,n); (word_sub stackpointer (word 16),16)]
         [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mld_zeroize_2) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ptr; word n] s /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(ptr,n)) s = 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ptr,n);
                memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_ZEROIZE_2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_ZEROIZE_2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with the combined  *)
(* contract of memset of utils/mlkem_native_libc_full.ml, and constant time  *)
(* and memory safety alone. The correctness theorem above keeps the weaker   *)
(* contract memset_contract and has its own proof.                           *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/utils/mlkem_native_libc_full.ml";;

let MLDSA_NATIVE_ZEROIZE_2_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e ptr n pc stackpointer returnaddress.
           n < 2 EXP 64 /\
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (ptr,n) (word_sub stackpointer (word 16),16) /\
           ALLPAIRS nonoverlapping
            [ptr,n; word_sub stackpointer (word 16),16]
            [word pc,libmldsa_size; word(pc + got_memset),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mldsa_native_libmldsa_gcc12_Os_mc /\
                     read PC s = word (pc + mld_zeroize_2) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [ptr; word n] s /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     read (memory :> bytes(ptr,n)) s = 0 /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events ptr n mf pc
                               (word_sub stackpointer (word 16))
                               returnaddress /\
                        memaccess_inbounds e2
                         [ptr,n; word_sub stackpointer (word 16),16;
                          word(pc + got_memset),8; ea,el]
                         [ptr,n; word_sub stackpointer (word 16),16]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(ptr,n);
                   memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_ZEROIZE_2_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_ZEROIZE_2_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

let MLDSA_NATIVE_ZEROIZE_2_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e ptr n pc stackpointer returnaddress.
           n < 2 EXP 64 /\
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (ptr,n) (word_sub stackpointer (word 16),16) /\
           ALLPAIRS nonoverlapping
            [ptr,n; word_sub stackpointer (word 16),16]
            [word pc,libmldsa_size; word(pc + got_memset),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mldsa_native_libmldsa_gcc12_Os_mc /\
                     read PC s = word (pc + mld_zeroize_2) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [ptr; word n] s /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events ptr n mf pc
                               (word_sub stackpointer (word 16))
                               returnaddress /\
                        memaccess_inbounds e2
                         [ptr,n; word_sub stackpointer (word 16),16;
                          word(pc + got_memset),8; ea,el]
                         [ptr,n; word_sub stackpointer (word 16),16]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(ptr,n);
                   memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_ZEROIZE_2_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_ZEROIZE_2_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
