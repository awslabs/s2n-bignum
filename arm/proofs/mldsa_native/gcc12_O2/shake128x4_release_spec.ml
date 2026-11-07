(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Zeroing a context of four SHAKE128 states. This is the code for           *)
(* mldsa_shake128x4_release from mldsa-native's portable C implementation    *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which zeroes    *)
(* the 800 bytes of the context with memset from the C library, called       *)
(* through the PLT of the image. It is verified in the whole image (see      *)
(* libmldsa.ml), assuming the contracts for memset in                        *)
(* utils/mlkem_native_libc.ml.                                               *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa_shake128x4_release:
       +0x0: stp     x19, x30, [sp, #-16]!
       +0x4: mov     x2, #0x320
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

let MLDSA_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_shake128x4_release"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
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
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_shake128x4_release) /\
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

let MLDSA_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
