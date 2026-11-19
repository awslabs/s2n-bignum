(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking the hints of a polynomial of a signature: the statement. This   *)
(* is the code for mldsa44_sig_unpack_hints (mld_sig_unpack_hints in         *)
(* packing.c) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -Os (see mldsa_native/README.md): for polynomial i of the 4, it   *)
(* checks the counts of the hints in the 84 bytes of the hints (at offset    *)
(* 2336 of the signature), zeroes the polynomial with memset from the C      *)
(* library, called through the PLT of the image, sets the coefficients at    *)
(* the indices of its hints to 1, checking that they are increasing, and for *)
(* the last polynomial checks that the unused index bytes are zero,          *)
(* returning -1 if a check fails and 0 otherwise. It is verified in the      *)
(* whole image (see libmldsa.ml) against mld_unpack_hints and                *)
(* mld_unpack_hints_ret of common/mldsa_native_hints.ml, assuming the        *)
(* contract for memset memset_ret_full_contract of                           *)
(* utils/mldsa_native_libc.ml, which gives its return value, and shown to    *)
(* be constant time and memory safe with events depending on the bytes of    *)
(* the hints and on i, which are public.                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_hints.ml";;
needs "arm/proofs/utils/mldsa_native_hints.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa44_sig_unpack_hints:
       +0x0: stp     x19, x20, [sp, #-48]!
       +0x4: mov     x3, x0
       +0x8: mov     x20, x1
       +0xc: stp     x21, x22, [sp, #16]
      +0x10: mov     w21, w2
      +0x14: stp     x23, x30, [sp, #32]
      +0x18: add     x23, x1, #0x920
      +0x1c: cbz     w2, <mldsa44_sig_unpack_hints+0x50>
      +0x20: add     w0, w2, #0x4f
      +0x24: ldrb    w22, [x23, x0]
      +0x28: add     w0, w21, #0x50
      +0x2c: ldrb    w19, [x23, x0]
      +0x30: cmp     w19, #0x50
      +0x34: ccmp    w22, w19, #0x2, ls
      +0x38: b.ls    <mldsa44_sig_unpack_hints+0x58>
      +0x3c: mov     w0, #0xffffffff
      +0x40: ldp     x21, x22, [sp, #16]
      +0x44: ldp     x23, x30, [sp, #32]
      +0x48: ldp     x19, x20, [sp], #48
      +0x4c: ret
      +0x50: mov     w22, #0x0
      +0x54: b       <mldsa44_sig_unpack_hints+0x28>
      +0x58: mov     x0, x3
      +0x5c: mov     x2, #0x400
      +0x60: mov     w1, #0x0
      +0x64: bl      <memset@plt>
      +0x68: add     x2, x20, w22, uxtb
      +0x6c: mov     x3, x0
      +0x70: mov     w1, w22
      +0x74: mov     w4, #0x1
      +0x78: cmp     w1, w19
      +0x7c: b.cc    <mldsa44_sig_unpack_hints+0x9c>
      +0x80: cmp     w21, #0x3
      +0x84: b.ne    <mldsa44_sig_unpack_hints+0x94>
      +0x88: add     x20, x20, #0x91f
      +0x8c: cmp     w19, #0x50
      +0x90: b.ne    <mldsa44_sig_unpack_hints+0xcc>
      +0x94: mov     w0, #0x0
      +0x98: b       <mldsa44_sig_unpack_hints+0x40>
      +0x9c: cmp     w1, w22
      +0xa0: b.ls    <mldsa44_sig_unpack_hints+0xb8>
      +0xa4: sub     w0, w1, #0x1
      +0xa8: ldrb    w5, [x2, #2336]
      +0xac: ldrb    w0, [x23, x0]
      +0xb0: cmp     w5, w0
      +0xb4: b.ls    <mldsa44_sig_unpack_hints+0x3c>
      +0xb8: ldrb    w0, [x2, #2336]
      +0xbc: add     w1, w1, #0x1
      +0xc0: add     x2, x2, #0x1
      +0xc4: str     w4, [x3, x0, lsl #2]
      +0xc8: b       <mldsa44_sig_unpack_hints+0x78>
      +0xcc: add     x19, x19, #0x1
      +0xd0: ldrb    w0, [x20, x19]
      +0xd4: cbz     w0, <mldsa44_sig_unpack_hints+0x8c>
      +0xd8: b       <mldsa44_sig_unpack_hints+0x3c>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa44_sig_unpack_hints"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, with the combined contract for memset (the theorem follows   *)
(* from the next one). The polynomial h is distinct from the stack frame,    *)
(* the code, the hints, the GOT entry of memset and the memory (ea,el) that  *)
(* memset needs unchanged. The return value is that of mld_unpack_hints_ret, *)
(* and if it is 0, the coefficients are those of mld_unpack_hints.           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> !h sig b i pc stackpointer returnaddress.
          i < 4 /\
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          nonoverlapping (h,1024) (word_sub stackpointer (word 48),48) /\
          ALLPAIRS nonoverlapping
           [(h,1024); (word_sub stackpointer (word 48),48)]
           [(word pc,libmldsa_size); (word_add sig (word 2336),84);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_sig_unpack_hints) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [h; sig; word i] s /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 84
                         ==> read(memory :> bytes8
                               (word_add sig (word(2336 + j)))) s =
                             b j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word_zx(mld_unpack_hints_ret 80 4 b i) /\
                    (mld_unpack_hints_ret 80 4 b i = word 0
                     ==> !p. p < 256
                             ==> read(memory :> bytes32
                                   (word_add h (word(4 * p)))) s =
                                 mld_unpack_hints 80 b i p))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(h,1024);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
    MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the bytes of the hints, i and the addresses,     *)
(* with all accesses within the hints, h, the stack frame, the GOT entry and *)
(* (ea,el), and the writes within h and the stack frame.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> exists f_events.
          forall e h sig b i pc stackpointer returnaddress.
           i < 4 /\
           aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (h,1024) (word_sub stackpointer (word 48),48) /\
           ALLPAIRS nonoverlapping
            [(h,1024); (word_sub stackpointer (word 48),48)]
            [(word pc,libmldsa_size); (word_add sig (word 2336),84);
             (word(pc + got_memset),8); (ea,el)]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mldsa_native_libmldsa_gcc12_Os_mc /\
                     read PC s = word (pc + mldsa44_sig_unpack_hints) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [h; sig; word i] s /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     (!j. j < 84
                          ==> read(memory :> bytes8
                                (word_add sig (word(2336 + j)))) s =
                              b j) /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     C_RETURN s = word_zx(mld_unpack_hints_ret 80 4 b i) /\
                     (mld_unpack_hints_ret 80 4 b i = word 0
                      ==> !p. p < 256
                              ==> read(memory :> bytes32
                                    (word_add h (word(4 * p)))) s =
                                  mld_unpack_hints 80 b i p) /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events b i h sig mf pc
                               (word_sub stackpointer (word 48))
                               returnaddress /\
                        memaccess_inbounds e2
                         [word_add sig (word 2336),84; h,1024;
                          word_sub stackpointer (word 48),48;
                          word(pc + got_memset),8; ea,el]
                         [h,1024; word_sub stackpointer (word 48),48]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(h,1024);
                   memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec
    MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* hints and i as above.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> exists f_events.
          forall e h sig b i pc stackpointer returnaddress.
           i < 4 /\
           aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (h,1024) (word_sub stackpointer (word 48),48) /\
           ALLPAIRS nonoverlapping
            [(h,1024); (word_sub stackpointer (word 48),48)]
            [(word pc,libmldsa_size); (word_add sig (word 2336),84);
             (word(pc + got_memset),8); (ea,el)]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mldsa_native_libmldsa_gcc12_Os_mc /\
                     read PC s = word (pc + mldsa44_sig_unpack_hints) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [h; sig; word i] s /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     (!j. j < 84
                          ==> read(memory :> bytes8
                                (word_add sig (word(2336 + j)))) s =
                              b j) /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events b i h sig mf pc
                               (word_sub stackpointer (word 48))
                               returnaddress /\
                        memaccess_inbounds e2
                         [word_add sig (word 2336),84; h,1024;
                          word_sub stackpointer (word 48),48;
                          word(pc + got_memset),8; ea,el]
                         [h,1024; word_sub stackpointer (word 48),48]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(h,1024);
                   memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec
    MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
