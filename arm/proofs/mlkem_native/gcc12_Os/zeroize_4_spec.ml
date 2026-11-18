(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Zeroing of a buffer. This is the code for mlk_zeroize_4 from              *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -Os      *)
(* (see mlkem_native/README.md), which zeroes the n bytes at ptr with        *)
(* memset from the C library, called through the PLT of the image. With -Os  *)
(* the functions of the API call it instead of zeroing inline. The image has *)
(* eight copies of it, mlk_zeroize_1 to mlk_zeroize_8, one for each          *)
(* translation unit of the library, which differ only in the offset of the   *)
(* branch to the PLT; each has its own spec and proof file. It is verified   *)
(* in the whole image (see libmlkem.ml), assuming the contracts for memset   *)
(* in utils/mlkem_native_libc.ml.                                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image, and the PLT stub for memset:

    mlk_zeroize_4:
       +0x0: stp     x19, x30, [sp, #-16]!
       +0x4: mov     x2, x1
       +0x8: mov     x19, x0
       +0xc: mov     w1, #0x0
      +0x10: bl      <memset@plt>
      +0x14: ldp     x19, x30, [sp], #16
      +0x18: ret

    memset@plt:
      +0x0: adrp    x16, <page>
      +0x4: ldr     x17, [x16, #4072]  // got_memset
      +0x8: add     x16, x16, #0xfe8  // got_memset
      +0xc: br      x17
 ***)

let MLKEM_NATIVE_ZEROIZE_4_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlk_zeroize_4"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset at the address mf in  *)
(* the GOT entry, with its code and data in the region (ea,el), which must   *)
(* not overlap the buffer or the stack.                                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_ZEROIZE_4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!ptr n mf ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\
        n < 2 EXP 64 /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (ptr,n) (word_sub stackpointer (word 16),16) /\
        ALLPAIRS nonoverlapping
         [(ptr,n); (word_sub stackpointer (word 16),16)]
         [(word pc,libmlkem_size); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlk_zeroize_4) /\
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

let MLKEM_NATIVE_ZEROIZE_4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_ZEROIZE_4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contract for memset. As for mlkem_shake128x4_release, it is stated        *)
(* directly, since the events depend on the GOT entry, the address of        *)
(* memset, as well as on the events of memset given by its contract.         *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_ZEROIZE_4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_safety_contract mf ea el ev
     ==> exists f_events.
          forall e ptr n pc stackpointer returnaddress.
           n < 2 EXP 64 /\
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (ptr,n) (word_sub stackpointer (word 16),16) /\
           ALLPAIRS nonoverlapping
            [ptr,n; word_sub stackpointer (word 16),16]
            [word pc,libmlkem_size; word(pc + got_memset),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mlkem_native_libmlkem_gcc12_Os_mc /\
                     read PC s = word (pc + mlk_zeroize_4) /\
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

let MLKEM_NATIVE_ZEROIZE_4_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_ZEROIZE_4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
