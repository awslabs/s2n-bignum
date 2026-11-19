(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Initialization of a SHAKE128 context. This is the code for                *)
(* mldsa_shake128_init (mld_shake128_init in fips202.c) from mldsa-native's  *)
(* portable C implementation compiled by gcc 12 with -Os (see                *)
(* mldsa_native/README.md), which sets the Keccak state, the first 200 bytes *)
(* of the context, to zero with memset from the C library, called through    *)
(* the PLT of the image, and the position, the 32-bit word after it, to      *)
(* zero. It is verified in the whole image (see libmldsa.ml), assuming the   *)
(* contracts for memset in utils/mlkem_native_libc.ml. It is also shown to   *)
(* be constant time and memory safe.                                         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa_shake128_init:
       +0x0: stp     x19, x30, [sp, #-16]!
       +0x4: mov     x19, x0
       +0x8: mov     x2, #0xc8
       +0xc: mov     w1, #0x0
      +0x10: bl      <memset@plt>
      +0x14: str     wzr, [x19, #200]
      +0x18: ldp     x19, x30, [sp], #16
      +0x1c: ret

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_SHAKE128_INIT_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa_shake128_init"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_INIT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ctx mf ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (ctx,204) (word_sub stackpointer (word 16),16) /\
        ALLPAIRS nonoverlapping
         [(ctx,204); (word_sub stackpointer (word 16),16)]
         [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_shake128_init) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ctx] s /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes ctx) s = (word 0:1600 word) /\
                  read (memory :> bytes32(word_add ctx (word 200))) s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ctx,204);
                memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_SHAKE128_INIT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SHAKE128_INIT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with the combined  *)
(* contract of memset of utils/mlkem_native_libc_full.ml, and constant time  *)
(* and memory safety alone. The correctness theorem above keeps the weaker   *)
(* contract memset_contract and has its own proof.                           *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/utils/mlkem_native_libc_full.ml";;

let MLDSA_NATIVE_SHAKE128_INIT_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e ctx pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (ctx,204) (word_sub stackpointer (word 16),16) /\
           ALLPAIRS nonoverlapping
            [ctx,204; word_sub stackpointer (word 16),16]
            [word pc,libmldsa_size; word(pc + got_memset),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mldsa_native_libmldsa_gcc12_Os_mc /\
                     read PC s = word (pc + mldsa_shake128_init) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [ctx] s /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     read (memory :> wbytes ctx) s = (word 0:1600 word) /\
                     read (memory :> bytes32(word_add ctx (word 200))) s =
                     word 0 /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events ctx mf pc
                               (word_sub stackpointer (word 16))
                               returnaddress /\
                        memaccess_inbounds e2
                         [ctx,204; word_sub stackpointer (word 16),16;
                          word(pc + got_memset),8; ea,el]
                         [ctx,204; word_sub stackpointer (word 16),16]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(ctx,204);
                   memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_SHAKE128_INIT_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SHAKE128_INIT_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

let MLDSA_NATIVE_SHAKE128_INIT_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e ctx pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (ctx,204) (word_sub stackpointer (word 16),16) /\
           ALLPAIRS nonoverlapping
            [ctx,204; word_sub stackpointer (word 16),16]
            [word pc,libmldsa_size; word(pc + got_memset),8; ea,el]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mldsa_native_libmldsa_gcc12_Os_mc /\
                     read PC s = word (pc + mldsa_shake128_init) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [ctx] s /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events ctx mf pc
                               (word_sub stackpointer (word 16))
                               returnaddress /\
                        memaccess_inbounds e2
                         [ctx,204; word_sub stackpointer (word 16),16;
                          word(pc + got_memset),8; ea,el]
                         [ctx,204; word_sub stackpointer (word 16),16]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(ctx,204);
                   memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_SHAKE128_INIT_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SHAKE128_INIT_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
