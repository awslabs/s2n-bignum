(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Release of a context of four SHAKE128 states. This is the code for        *)
(* mlkem_shake128x4_release from mlkem-native's portable C implementation    *)
(* compiled by gcc 12 with -Os (see mlkem_native/README.md), which zeroes    *)
(* the 800 bytes of the context by a tail call of mlk_zeroize_3, which in    *)
(* turn calls memset from the C library through the PLT of the image. It is  *)
(* verified in the whole image (see libmlkem.ml), using the theorems for     *)
(* mlk_zeroize_3 in the image and assuming the contracts for memset in       *)
(* utils/mlkem_native_libc.ml.                                               *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/zeroize_3_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlkem_shake128x4_release:
       +0x0: mov     x1, #0x320
       +0x4: b       <mlk_zeroize_3>
 ***)

let MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_shake128x4_release"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset at the address mf in  *)
(* the GOT entry, with its code and data in the region (ea,el), which must   *)
(* not overlap the context or the stack. The stack is the 16 bytes of        *)
(* mlk_zeroize_3.                                                            *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!st mf ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (st,800) (word_sub stackpointer (word 16),16) /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 16),16)]
         [(word pc,libmlkem_size); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlkem_shake128x4_release) /\
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

let MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contract for memset. As for mlkem_poly_compress_d4, it is stated          *)
(* directly, since the events depend on the GOT entry, the address of        *)
(* memset, as well as on the events of memset given by its contract.         *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_safety_contract mf ea el ev
     ==> exists f_events.
          forall e st pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (st,800) (word_sub stackpointer (word 16),16) /\
           ALLPAIRS nonoverlapping
            [st,800; word_sub stackpointer (word 16),16]
            [word pc,libmlkem_size; word(pc + got_memset),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_gcc12_Os_mc /\
                     read PC s = word (pc + mlkem_shake128x4_release) /\
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

let MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
