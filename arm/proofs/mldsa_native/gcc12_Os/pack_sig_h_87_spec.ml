(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing the hints of a signature: the statement. This is the code for     *)
(* mldsa87_pack_sig_h (mld_pack_sig_h in packing.c) from mldsa-native's      *)
(* portable C implementation compiled by gcc 12 with -Os (see                *)
(* mldsa_native/README.md): for each of the 8 polynomials it unpacks w1 into *)
(* the scratch polynomial with mldsa_polyw1_unpack_32 and records the        *)
(* coefficients with a hint, from w0 and w1, in the 83 bytes of the hints    *)
(* (at offset 4544 of the signature), returning -1 if there are more than 75 *)
(* hints and 0 otherwise. It is verified in the whole image (see             *)
(* libmldsa.ml) against mld_pack_hints and mld_pack_hints_ret of             *)
(* common/mldsa_native_hints.ml, using the theorems for                      *)
(* mldsa_polyw1_unpack_32, and shown to be constant time and memory safe     *)
(* with events depending on w0 and w1, which the caller declassifies. The    *)
(* code zeroes the hints with memset from the C library, called through the  *)
(* PLT of the image, so the statements assume the combined contract          *)
(* memset_full_contract of utils/mlkem_native_libc_full.ml, with the GOT     *)
(* entry of memset and the memory (ea,el) that memset reads and keeps.       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_hints.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyw1_unpack_32_spec.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa87_pack_sig_h:
       +0x0: stp     x19, x20, [sp, #-96]!
       +0x4: mov     x19, #0x0
       +0x8: mov     w20, #0x0
       +0xc: stp     x23, x24, [sp, #32]
      +0x10: mov     x23, x1
      +0x14: mov     x1, #0x11c0
      +0x18: stp     x25, x26, [sp, #48]
      +0x1c: add     x25, x0, x1
      +0x20: mov     x24, x2
      +0x24: stp     x27, x28, [sp, #64]
      +0x28: mov     w28, #0x100
      +0x2c: mov     x2, #0x53
      +0x30: mov     w1, #0x0
      +0x34: mov     w26, #0x3ff00
      +0x38: mov     w27, #0x7fe00
      +0x3c: movk    w28, #0xfffc, lsl #16
      +0x40: stp     x21, x22, [sp, #16]
      +0x44: mov     x21, x0
      +0x48: mov     x22, x3
      +0x4c: mov     x0, x25
      +0x50: str     x30, [sp, #80]
      +0x54: bl      <memset@plt>
      +0x58: add     x1, x24, x19, lsl #7
      +0x5c: mov     x0, x22
      +0x60: bl      <mldsa_polyw1_unpack_32>
      +0x64: add     x1, x23, x19, lsl #10
      +0x68: mov     x4, #0x0
      +0x6c: ldr     w0, [x1, x4, lsl #2]
      +0x70: ldr     w2, [x22, x4, lsl #2]
      +0x74: add     w3, w0, w26
      +0x78: cmp     w3, w27
      +0x7c: b.hi    <mldsa87_pack_sig_h+0x8c>
      +0x80: cmp     w2, #0x0
      +0x84: ccmp    w0, w28, #0x0, ne
      +0x88: b.ne    <mldsa87_pack_sig_h+0x9c>
      +0x8c: cmp     w20, #0x4b
      +0x90: b.eq    <mldsa87_pack_sig_h+0xe0>
      +0x94: strb    w4, [x25, w20, uxtw]
      +0x98: add     w20, w20, #0x1
      +0x9c: add     x4, x4, #0x1
      +0xa0: cmp     x4, #0x100
      +0xa4: b.ne    <mldsa87_pack_sig_h+0x6c>
      +0xa8: mov     x0, #0x120b
      +0xac: add     x0, x21, x0
      +0xb0: strb    w20, [x0, x19]
      +0xb4: add     x19, x19, #0x1
      +0xb8: cmp     x19, #0x8
      +0xbc: b.ne    <mldsa87_pack_sig_h+0x58>
      +0xc0: mov     w0, #0x0
      +0xc4: ldp     x21, x22, [sp, #16]
      +0xc8: ldp     x23, x24, [sp, #32]
      +0xcc: ldp     x25, x26, [sp, #48]
      +0xd0: ldp     x27, x28, [sp, #64]
      +0xd4: ldr     x30, [sp, #80]
      +0xd8: ldp     x19, x20, [sp], #96
      +0xdc: ret
      +0xe0: mov     w0, #0xffffffff
      +0xe4: b       <mldsa87_pack_sig_h+0xc4>


    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa87_pack_sig_h"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vector x of w0 at w0 and the 1024 bytes b of w1 at w1p   *)
(* may overlap each other but not the 83 bytes of the hints in the signature *)
(* at sig, the scratch polynomial or the stack frame. The return value is    *)
(* that of mld_pack_hints_ret, and if it is 0, the hints are those of        *)
(* mld_pack_hints.                                                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !sig w0 w1p scratch x b pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(word_add sig (word 4544),83); (scratch,1024);
            (word_sub stackpointer (word 96),96)] /\
          ALLPAIRS nonoverlapping
           [(word_add sig (word 4544),83); (scratch,1024);
            (word_sub stackpointer (word 96),96)]
           [(word pc,libmldsa_size); (w0,8192); (w1p,1024);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa87_pack_sig_h) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; w0; w1p; scratch] s /\
                    read (memory :> bytes64(word(pc + got_memset)))
                         s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!i. i < 2048
                         ==> read(memory :> bytes32(word_add w0 (word(4 * i))))
                               s = x i) /\
                    (!j. j < 1024
                         ==> read(memory :> bytes8(word_add w1p (word j))) s =
                             b j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                      word_zx(mld_pack_hints_ret 75 8
                               (mld_polyvec_make_hint_32 x b)) /\
                    (mld_pack_hints_ret 75 8 (mld_polyvec_make_hint_32 x b) =
                     word 0
                     ==> !t. t < 83
                             ==> read(memory :> bytes8
                                   (word_add sig (word(4544 + t)))) s =
                                 mld_pack_hints 75 8
                                   (mld_polyvec_make_hint_32 x b) t))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_add sig (word 4544),83);
                  memory :> bytes(scratch,1024);
                  memory :> bytes(word_sub stackpointer (word 96),96)])`;;

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_PACK_SIG_H_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of w0 and w1 (x and b) and the addresses, with all  *)
(* accesses within the inputs, the scratch polynomial, the stack frame and   *)
(* the hints, which the code only writes but memset may read according to    *)
(* its contract, and the writes within the outputs.                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig w0 w1p scratch x b pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(word_add sig (word 4544),83); (scratch,1024);
            (word_sub stackpointer (word 96),96)] /\
          ALLPAIRS nonoverlapping
           [(word_add sig (word 4544),83); (scratch,1024);
            (word_sub stackpointer (word 96),96)]
           [(word pc,libmldsa_size); (w0,8192); (w1p,1024);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa87_pack_sig_h) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; w0; w1p; scratch] s /\
                    read (memory :> bytes64(word(pc + got_memset)))
                         s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!i. i < 2048
                         ==> read(memory :> bytes32(word_add w0 (word(4 * i))))
                               s = x i) /\
                    (!j. j < 1024
                         ==> read(memory :> bytes8(word_add w1p (word j))) s =
                             b j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                      word_zx(mld_pack_hints_ret 75 8
                               (mld_polyvec_make_hint_32 x b)) /\
                    (mld_pack_hints_ret 75 8 (mld_polyvec_make_hint_32 x b) =
                     word 0
                     ==> !t. t < 83
                             ==> read(memory :> bytes8
                                   (word_add sig (word(4544 + t)))) s =
                                 mld_pack_hints 75 8
                                   (mld_polyvec_make_hint_32 x b) t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events x b sig w0 w1p scratch mf pc
                                   (word_sub stackpointer (word 96))
                                   returnaddress /\
                       memaccess_inbounds e2
                        [w0,8192; w1p,1024; scratch,1024;
                         word_sub stackpointer (word 96),96;
                         word_add sig (word 4544),83;
                         word(pc + got_memset),8; ea,el]
                        [word_add sig (word 4544),83; scratch,1024;
                         word_sub stackpointer (word 96),96]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_add sig (word 4544),83);
                  memory :> bytes(scratch,1024);
                  memory :> bytes(word_sub stackpointer (word 96),96)])`;;

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PACK_SIG_H_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on w0    *)
(* and w1 as above.                                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig w0 w1p scratch x b pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(word_add sig (word 4544),83); (scratch,1024);
            (word_sub stackpointer (word 96),96)] /\
          ALLPAIRS nonoverlapping
           [(word_add sig (word 4544),83); (scratch,1024);
            (word_sub stackpointer (word 96),96)]
           [(word pc,libmldsa_size); (w0,8192); (w1p,1024);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa87_pack_sig_h) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; w0; w1p; scratch] s /\
                    read (memory :> bytes64(word(pc + got_memset)))
                         s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!i. i < 2048
                         ==> read(memory :> bytes32(word_add w0 (word(4 * i))))
                               s = x i) /\
                    (!j. j < 1024
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
                        [w0,8192; w1p,1024; scratch,1024;
                         word_sub stackpointer (word 96),96;
                         word_add sig (word 4544),83;
                         word(pc + got_memset),8; ea,el]
                        [word_add sig (word 4544),83; scratch,1024;
                         word_sub stackpointer (word 96),96]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_add sig (word 4544),83);
                  memory :> bytes(scratch,1024);
                  memory :> bytes(word_sub stackpointer (word 96),96)])`;;

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PACK_SIG_H_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
