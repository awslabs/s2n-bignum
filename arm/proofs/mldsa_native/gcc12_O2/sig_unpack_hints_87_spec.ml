(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking the hints of a polynomial of a signature: the statement. This   *)
(* is the code for mldsa87_sig_unpack_hints (mld_sig_unpack_hints in         *)
(* packing.c) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -O2 (see mldsa_native/README.md): for polynomial i of the 8, it   *)
(* checks the counts of the hints in the 83 bytes of the hints (at offset    *)
(* 4544 of the signature), zeroes the polynomial with memset from the C      *)
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
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa87_sig_unpack_hints:
       +0x0: stp     x19, x20, [sp, #-48]!
       +0x4: mov     x3, #0x11c0
       +0x8: mov     x19, x1
       +0xc: stp     x21, x22, [sp, #16]
      +0x10: mov     x6, x0
      +0x14: add     x22, x1, x3
      +0x18: stp     x23, x30, [sp, #32]
      +0x1c: mov     w21, #0x0
      +0x20: mov     w23, w2
      +0x24: cbz     w2, <mldsa87_sig_unpack_hints+0x30>
      +0x28: add     w0, w2, #0x4a
      +0x2c: ldrb    w21, [x22, w0, uxtw]
      +0x30: add     w0, w23, #0x4b
      +0x34: ldrb    w20, [x22, w0, uxtw]
      +0x38: cmp     w20, #0x4b
      +0x3c: ccmp    w21, w20, #0x2, ls
      +0x40: b.hi    <mldsa87_sig_unpack_hints+0xa4>
      +0x44: mov     x0, x6
      +0x48: mov     x2, #0x400
      +0x4c: mov     w1, #0x0
      +0x50: bl      <memset>
      +0x54: mov     x6, x0
      +0x58: cmp     w21, w20
      +0x5c: b.cs    <mldsa87_sig_unpack_hints+0xb8>
      +0x60: mov     w0, #0x11c0
      +0x64: add     w0, w21, w0
      +0x68: mov     w3, w21
      +0x6c: add     x1, x19, x0
      +0x70: mov     w7, #0x1
      +0x74: ldrb    w4, [x1], #1
      +0x78: mov     w5, w3
      +0x7c: add     w3, w3, #0x1
      +0x80: str     w7, [x6, x4, lsl #2]
      +0x84: cmp     w20, w3
      +0x88: b.ls    <mldsa87_sig_unpack_hints+0xb8>
      +0x8c: cmp     w21, w3
      +0x90: b.cs    <mldsa87_sig_unpack_hints+0x74>
      +0x94: ldrb    w0, [x22, w5, uxtw]
      +0x98: ldrb    w4, [x1]
      +0x9c: cmp     w4, w0
      +0xa0: b.hi    <mldsa87_sig_unpack_hints+0x74>
      +0xa4: mov     w0, #0xffffffff
      +0xa8: ldp     x21, x22, [sp, #16]
      +0xac: ldp     x23, x30, [sp, #32]
      +0xb0: ldp     x19, x20, [sp], #48
      +0xb4: ret
      +0xb8: cmp     w23, #0x7
      +0xbc: b.eq    <mldsa87_sig_unpack_hints+0xd4>
      +0xc0: mov     w0, #0x0
      +0xc4: ldp     x21, x22, [sp, #16]
      +0xc8: ldp     x23, x30, [sp, #32]
      +0xcc: ldp     x19, x20, [sp], #48
      +0xd0: ret
      +0xd4: cmp     w20, #0x4b
      +0xd8: b.eq    <mldsa87_sig_unpack_hints+0xc0>
      +0xdc: ldrb    w0, [x22, x20]
      +0xe0: add     x20, x20, #0x1
      +0xe4: cbnz    w0, <mldsa87_sig_unpack_hints+0xa4>
      +0xe8: nop
      +0xec: cmp     w20, #0x4b
      +0xf0: b.eq    <mldsa87_sig_unpack_hints+0xc4>
      +0xf4: ldrb    w0, [x22, x20]
      +0xf8: add     x20, x20, #0x1
      +0xfc: cbz     w0, <mldsa87_sig_unpack_hints+0xec>
     +0x100: mov     w0, #0xffffffff
     +0x104: b       <mldsa87_sig_unpack_hints+0xa8>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_sig_unpack_hints"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, with the combined contract for memset (the theorem follows   *)
(* from the next one). The polynomial h is distinct from the stack frame,    *)
(* the code, the hints, the GOT entry of memset and the memory (ea,el) that  *)
(* memset needs unchanged. The return value is that of mld_unpack_hints_ret, *)
(* and if it is 0, the coefficients are those of mld_unpack_hints.           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> !h sig b i pc stackpointer returnaddress.
          i < 8 /\
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          nonoverlapping (h,1024) (word_sub stackpointer (word 48),48) /\
          ALLPAIRS nonoverlapping
           [(h,1024); (word_sub stackpointer (word 48),48)]
           [(word pc,libmldsa_size); (word_add sig (word 4544),83);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_sig_unpack_hints) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [h; sig; word i] s /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 83
                         ==> read(memory :> bytes8
                               (word_add sig (word(4544 + j)))) s =
                             b j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word_zx(mld_unpack_hints_ret 75 8 b i) /\
                    (mld_unpack_hints_ret 75 8 b i = word 0
                     ==> !p. p < 256
                             ==> read(memory :> bytes32
                                   (word_add h (word(4 * p)))) s =
                                 mld_unpack_hints 75 b i p))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(h,1024);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
    MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the bytes of the hints, i and the addresses,     *)
(* with all accesses within the hints, h, the stack frame, the GOT entry and *)
(* (ea,el), and the writes within h and the stack frame.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> exists f_events.
          forall e h sig b i pc stackpointer returnaddress.
           i < 8 /\
           aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (h,1024) (word_sub stackpointer (word 48),48) /\
           ALLPAIRS nonoverlapping
            [(h,1024); (word_sub stackpointer (word 48),48)]
            [(word pc,libmldsa_size); (word_add sig (word 4544),83);
             (word(pc + got_memset),8); (ea,el)]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mldsa_native_libmldsa_gcc12_O2_mc /\
                     read PC s = word (pc + mldsa87_sig_unpack_hints) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [h; sig; word i] s /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     (!j. j < 83
                          ==> read(memory :> bytes8
                                (word_add sig (word(4544 + j)))) s =
                              b j) /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     C_RETURN s = word_zx(mld_unpack_hints_ret 75 8 b i) /\
                     (mld_unpack_hints_ret 75 8 b i = word 0
                      ==> !p. p < 256
                              ==> read(memory :> bytes32
                                    (word_add h (word(4 * p)))) s =
                                  mld_unpack_hints 75 b i p) /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events b i h sig mf pc
                               (word_sub stackpointer (word 48))
                               returnaddress /\
                        memaccess_inbounds e2
                         [word_add sig (word 4544),83; h,1024;
                          word_sub stackpointer (word 48),48;
                          word(pc + got_memset),8; ea,el]
                         [h,1024; word_sub stackpointer (word 48),48]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(h,1024);
                   memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
    MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* hints and i as above.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> exists f_events.
          forall e h sig b i pc stackpointer returnaddress.
           i < 8 /\
           aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (h,1024) (word_sub stackpointer (word 48),48) /\
           ALLPAIRS nonoverlapping
            [(h,1024); (word_sub stackpointer (word 48),48)]
            [(word pc,libmldsa_size); (word_add sig (word 4544),83);
             (word(pc + got_memset),8); (ea,el)]
           ==> ensures arm
                (\s. aligned_bytes_loaded s (word pc)
                       mldsa_native_libmldsa_gcc12_O2_mc /\
                     read PC s = word (pc + mldsa87_sig_unpack_hints) /\
                     read SP s = stackpointer /\
                     read X30 s = returnaddress /\
                     C_ARGUMENTS [h; sig; word i] s /\
                     read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                     read (memory :> bytes(ea,el)) s = ev /\
                     (!j. j < 83
                          ==> read(memory :> bytes8
                                (word_add sig (word(4544 + j)))) s =
                              b j) /\
                     read events s = e)
                (\s. read PC s = returnaddress /\
                     (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events b i h sig mf pc
                               (word_sub stackpointer (word 48))
                               returnaddress /\
                        memaccess_inbounds e2
                         [word_add sig (word 4544),83; h,1024;
                          word_sub stackpointer (word 48),48;
                          word(pc + got_memset),8; ea,el]
                         [h,1024; word_sub stackpointer (word 48),48]))
                (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                 MAYCHANGE [X18] ,,
                 MAYCHANGE
                  [memory :> bytes(h,1024);
                   memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
    MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
