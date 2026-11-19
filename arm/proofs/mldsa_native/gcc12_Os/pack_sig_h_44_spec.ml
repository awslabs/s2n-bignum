(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing the hints of a signature: the statement. This is the code for     *)
(* mldsa44_pack_sig_h (mld_pack_sig_h in packing.c) from mldsa-native's      *)
(* portable C implementation compiled by gcc 12 with -Os (see                *)
(* mldsa_native/README.md): for each of the 4 polynomials it unpacks w1 into *)
(* the scratch polynomial with mldsa_polyw1_unpack_88 and records the        *)
(* coefficients with a hint, from w0 and w1, in the 84 bytes of the hints    *)
(* (at offset 2336 of the signature), returning -1 if there are more than 80 *)
(* hints and 0 otherwise. It is verified in the whole image (see             *)
(* libmldsa.ml) against mld_pack_hints and mld_pack_hints_ret of             *)
(* common/mldsa_native_hints.ml, using the theorems for                      *)
(* mldsa_polyw1_unpack_88, and shown to be constant time and memory safe     *)
(* with events depending on w0 and w1, which the caller declassifies. The    *)
(* code zeroes the hints with memset from the C library, called through the  *)
(* PLT of the image, so the statements assume the combined contract          *)
(* memset_full_contract of utils/mlkem_native_libc_full.ml, with the GOT     *)
(* entry of memset and the memory (ea,el) that memset reads and keeps.       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_hints.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyw1_unpack_88_spec.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa44_pack_sig_h:
       +0x0: stp     x19, x20, [sp, #-96]!
       +0x4: mov     x19, #0x0
       +0x8: mov     w20, #0x0
       +0xc: stp     x25, x26, [sp, #48]
      +0x10: add     x25, x0, #0x920
      +0x14: mov     x26, #0xc0
      +0x18: stp     x27, x28, [sp, #64]
      +0x1c: mov     w27, #0x7400
      +0x20: mov     w28, #0xe800
      +0x24: movk    w27, #0x1, lsl #16
      +0x28: movk    w28, #0x2, lsl #16
      +0x2c: stp     x21, x22, [sp, #16]
      +0x30: mov     x21, x0
      +0x34: mov     x22, x3
      +0x38: mov     x0, x25
      +0x3c: stp     x23, x24, [sp, #32]
      +0x40: mov     x23, x1
      +0x44: mov     x24, x2
      +0x48: mov     w1, #0x0
      +0x4c: mov     x2, #0x54
      +0x50: str     x30, [sp, #80]
      +0x54: bl      <memset@plt>
      +0x58: madd    x1, x19, x26, x24
      +0x5c: mov     x0, x22
      +0x60: bl      <mldsa_polyw1_unpack_88>
      +0x64: mov     w2, #0x8c00
      +0x68: add     x1, x23, x19, lsl #10
      +0x6c: mov     x4, #0x0
      +0x70: movk    w2, #0xfffe, lsl #16
      +0x74: ldr     w0, [x1, x4, lsl #2]
      +0x78: ldr     w3, [x22, x4, lsl #2]
      +0x7c: add     w5, w0, w27
      +0x80: cmp     w5, w28
      +0x84: b.hi    <mldsa44_pack_sig_h+0x94>
      +0x88: cmp     w3, #0x0
      +0x8c: ccmp    w0, w2, #0x0, ne
      +0x90: b.ne    <mldsa44_pack_sig_h+0xa4>
      +0x94: cmp     w20, #0x50
      +0x98: b.eq    <mldsa44_pack_sig_h+0xe4>
      +0x9c: strb    w4, [x25, w20, uxtw]
      +0xa0: add     w20, w20, #0x1
      +0xa4: add     x4, x4, #0x1
      +0xa8: cmp     x4, #0x100
      +0xac: b.ne    <mldsa44_pack_sig_h+0x74>
      +0xb0: add     x0, x21, #0x970
      +0xb4: strb    w20, [x0, x19]
      +0xb8: add     x19, x19, #0x1
      +0xbc: cmp     x19, #0x4
      +0xc0: b.ne    <mldsa44_pack_sig_h+0x58>
      +0xc4: mov     w0, #0x0
      +0xc8: ldp     x21, x22, [sp, #16]
      +0xcc: ldp     x23, x24, [sp, #32]
      +0xd0: ldp     x25, x26, [sp, #48]
      +0xd4: ldp     x27, x28, [sp, #64]
      +0xd8: ldr     x30, [sp, #80]
      +0xdc: ldp     x19, x20, [sp], #96
      +0xe0: ret
      +0xe4: mov     w0, #0xffffffff
      +0xe8: b       <mldsa44_pack_sig_h+0xc8>


    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa44_pack_sig_h"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vector x of w0 at w0 and the 768 bytes b of w1 at w1p    *)
(* may overlap each other but not the 84 bytes of the hints in the signature *)
(* at sig, the scratch polynomial or the stack frame. The return value is    *)
(* that of mld_pack_hints_ret, and if it is 0, the hints are those of        *)
(* mld_pack_hints.                                                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !sig w0 w1p scratch x b pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(word_add sig (word 2336),84); (scratch,1024);
            (word_sub stackpointer (word 96),96)] /\
          ALLPAIRS nonoverlapping
           [(word_add sig (word 2336),84); (scratch,1024);
            (word_sub stackpointer (word 96),96)]
           [(word pc,libmldsa_size); (w0,4096); (w1p,768);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_pack_sig_h) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; w0; w1p; scratch] s /\
                    read (memory :> bytes64(word(pc + got_memset)))
                         s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!i. i < 1024
                         ==> read(memory :> bytes32(word_add w0 (word(4 * i))))
                               s = x i) /\
                    (!j. j < 768
                         ==> read(memory :> bytes8(word_add w1p (word j))) s =
                             b j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                      word_zx(mld_pack_hints_ret 80 4
                               (mld_polyvec_make_hint_88 x b)) /\
                    (mld_pack_hints_ret 80 4 (mld_polyvec_make_hint_88 x b) =
                     word 0
                     ==> !t. t < 84
                             ==> read(memory :> bytes8
                                   (word_add sig (word(2336 + t)))) s =
                                 mld_pack_hints 80 4
                                   (mld_polyvec_make_hint_88 x b) t))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_add sig (word 2336),84);
                  memory :> bytes(scratch,1024);
                  memory :> bytes(word_sub stackpointer (word 96),96)])`;;

let MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of w0 and w1 (x and b) and the addresses, with all  *)
(* accesses within the inputs, the scratch polynomial, the stack frame and   *)
(* the hints, which the code only writes but memset may read according to    *)
(* its contract, and the writes within the outputs.                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig w0 w1p scratch x b pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(word_add sig (word 2336),84); (scratch,1024);
            (word_sub stackpointer (word 96),96)] /\
          ALLPAIRS nonoverlapping
           [(word_add sig (word 2336),84); (scratch,1024);
            (word_sub stackpointer (word 96),96)]
           [(word pc,libmldsa_size); (w0,4096); (w1p,768);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_pack_sig_h) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; w0; w1p; scratch] s /\
                    read (memory :> bytes64(word(pc + got_memset)))
                         s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!i. i < 1024
                         ==> read(memory :> bytes32(word_add w0 (word(4 * i))))
                               s = x i) /\
                    (!j. j < 768
                         ==> read(memory :> bytes8(word_add w1p (word j))) s =
                             b j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                      word_zx(mld_pack_hints_ret 80 4
                               (mld_polyvec_make_hint_88 x b)) /\
                    (mld_pack_hints_ret 80 4 (mld_polyvec_make_hint_88 x b) =
                     word 0
                     ==> !t. t < 84
                             ==> read(memory :> bytes8
                                   (word_add sig (word(2336 + t)))) s =
                                 mld_pack_hints 80 4
                                   (mld_polyvec_make_hint_88 x b) t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events x b sig w0 w1p scratch mf pc
                                   (word_sub stackpointer (word 96))
                                   returnaddress /\
                       memaccess_inbounds e2
                        [w0,4096; w1p,768; scratch,1024;
                         word_sub stackpointer (word 96),96;
                         word_add sig (word 2336),84;
                         word(pc + got_memset),8; ea,el]
                        [word_add sig (word 2336),84; scratch,1024;
                         word_sub stackpointer (word 96),96]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_add sig (word 2336),84);
                  memory :> bytes(scratch,1024);
                  memory :> bytes(word_sub stackpointer (word 96),96)])`;;

let MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on w0    *)
(* and w1 as above.                                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig w0 w1p scratch x b pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(word_add sig (word 2336),84); (scratch,1024);
            (word_sub stackpointer (word 96),96)] /\
          ALLPAIRS nonoverlapping
           [(word_add sig (word 2336),84); (scratch,1024);
            (word_sub stackpointer (word 96),96)]
           [(word pc,libmldsa_size); (w0,4096); (w1p,768);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_pack_sig_h) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; w0; w1p; scratch] s /\
                    read (memory :> bytes64(word(pc + got_memset)))
                         s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!i. i < 1024
                         ==> read(memory :> bytes32(word_add w0 (word(4 * i))))
                               s = x i) /\
                    (!j. j < 768
                         ==> read(memory :> bytes8(word_add w1p (word j))) s =
                             b j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events x b sig w0 w1p scratch mf pc
                                   (word_sub stackpointer (word 96))
                                   returnaddress /\
                       memaccess_inbounds e2
                        [w0,4096; w1p,768; scratch,1024;
                         word_sub stackpointer (word 96),96;
                         word_add sig (word 2336),84;
                         word(pc + got_memset),8; ea,el]
                        [word_add sig (word 2336),84; scratch,1024;
                         word_sub stackpointer (word 96),96]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_add sig (word 2336),84);
                  memory :> bytes(scratch,1024);
                  memory :> bytes(word_sub stackpointer (word 96),96)])`;;

let MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
