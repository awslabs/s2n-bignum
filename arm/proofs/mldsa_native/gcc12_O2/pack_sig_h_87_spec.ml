(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing the hints of a signature: the statement. This is the code for     *)
(* mldsa87_pack_sig_h (mld_pack_sig_h in packing.c) from mldsa-native's      *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mldsa_native/README.md): for each of the 8 polynomials it unpacks w1 into *)
(* the scratch polynomial with mldsa_polyw1_unpack_32 and records the        *)
(* coefficients with a hint, from w0 and w1, in the 83 bytes of the hints    *)
(* (at offset 4544 of the signature), returning -1 if there are more than 75 *)
(* hints and 0 otherwise. It is verified in the whole image (see             *)
(* libmldsa.ml) against mld_pack_hints and mld_pack_hints_ret of             *)
(* common/mldsa_native_hints.ml, using the theorems for                      *)
(* mldsa_polyw1_unpack_32, and shown to be constant time and memory safe     *)
(* with events depending on w0 and w1, which the caller declassifies.        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_hints.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyw1_unpack_32_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa87_pack_sig_h:
       +0x0: movi    v0.4s, #0x0
       +0x4: stp     x19, x20, [sp, #-96]!
       +0x8: mov     x20, x3
       +0xc: stp     x25, x26, [sp, #48]
      +0x10: mov     x3, #0x120b
      +0x14: mov     w19, #0x0
      +0x18: stp     x27, x28, [sp, #64]
      +0x1c: mov     x28, x2
      +0x20: mov     x2, #0x11c0
      +0x24: add     x26, x0, x2
      +0x28: stp     x21, x22, [sp, #16]
      +0x2c: mov     w27, #0x100
      +0x30: stp     x23, x24, [sp, #32]
      +0x34: mov     x21, x1
      +0x38: add     x23, x0, x3
      +0x3c: str     x30, [sp, #80]
      +0x40: add     x24, x28, #0x400
      +0x44: mov     w25, #0x3ff00
      +0x48: mov     w22, #0x7fe00
      +0x4c: str     q0, [x26, #64]
      +0x50: movk    w27, #0xfffc, lsl #16
      +0x54: stur    wzr, [x26, #79]
      +0x58: stp     q0, q0, [x26]
      +0x5c: stp     q0, q0, [x26, #32]
      +0x60: mov     x1, x28
      +0x64: mov     x0, x20
      +0x68: bl      <mldsa_polyw1_unpack_32>
      +0x6c: mov     x4, #0x0
      +0x70: b       <mldsa87_pack_sig_h+0x8c>
      +0x74: cmp     w7, #0x0
      +0x78: ccmp    w5, w27, #0x0, ne
      +0x7c: b.eq    <mldsa87_pack_sig_h+0xa0>
      +0x80: add     x4, x4, #0x1
      +0x84: cmp     x4, #0x100
      +0x88: b.eq    <mldsa87_pack_sig_h+0xbc>
      +0x8c: ldr     w5, [x21, x4, lsl #2]
      +0x90: ldr     w7, [x20, x4, lsl #2]
      +0x94: add     w6, w5, w25
      +0x98: cmp     w6, w22
      +0x9c: b.ls    <mldsa87_pack_sig_h+0x74>
      +0xa0: cmp     w19, #0x4b
      +0xa4: b.eq    <mldsa87_pack_sig_h+0xd8>
      +0xa8: strb    w4, [x26, w19, uxtw]
      +0xac: add     x4, x4, #0x1
      +0xb0: add     w19, w19, #0x1
      +0xb4: cmp     x4, #0x100
      +0xb8: b.ne    <mldsa87_pack_sig_h+0x8c>
      +0xbc: add     x28, x28, #0x80
      +0xc0: strb    w19, [x23], #1
      +0xc4: add     x21, x21, #0x400
      +0xc8: cmp     x28, x24
      +0xcc: b.ne    <mldsa87_pack_sig_h+0x60>
      +0xd0: mov     w0, #0x0
      +0xd4: b       <mldsa87_pack_sig_h+0xdc>
      +0xd8: mov     w0, #0xffffffff
      +0xdc: ldp     x21, x22, [sp, #16]
      +0xe0: ldp     x23, x24, [sp, #32]
      +0xe4: ldp     x25, x26, [sp, #48]
      +0xe8: ldp     x27, x28, [sp, #64]
      +0xec: ldr     x30, [sp, #80]
      +0xf0: ldp     x19, x20, [sp], #96
      +0xf4: ret
 ***)

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_pack_sig_h"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vector x of w0 at w0 and the 1024 bytes b of w1 at w1p   *)
(* may overlap each other but not the 83 bytes of the hints in the signature *)
(* at sig, the scratch polynomial or the stack frame. The return value is    *)
(* that of mld_pack_hints_ret, and if it is 0, the hints are those of        *)
(* mld_pack_hints.                                                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!sig w0 w1p scratch x b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(word_add sig (word 4544),83); (scratch,1024);
          (word_sub stackpointer (word 96),96)] /\
        ALLPAIRS nonoverlapping
         [(word_add sig (word 4544),83); (scratch,1024);
          (word_sub stackpointer (word 96),96)]
         [(word pc,libmldsa_size); (w0,8192); (w1p,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa87_pack_sig_h) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [sig; w0; w1p; scratch] s /\
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
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_add sig (word 4544),83);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 96),96)])`;;

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of w0 and w1 (x and b) and the addresses, with all  *)
(* accesses within the inputs, the scratch polynomial and the stack frame,   *)
(* and the writes within the outputs (the hints are only written).           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e sig w0 w1p scratch x b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(word_add sig (word 4544),83); (scratch,1024);
          (word_sub stackpointer (word 96),96)] /\
        ALLPAIRS nonoverlapping
         [(word_add sig (word 4544),83); (scratch,1024);
          (word_sub stackpointer (word 96),96)]
         [(word pc,libmldsa_size); (w0,8192); (w1p,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa87_pack_sig_h) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [sig; w0; w1p; scratch] s /\
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
                     e2 = f_events x b sig w0 w1p scratch pc
                                 (word_sub stackpointer (word 96))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [w0,8192; w1p,1024; scratch,1024;
                       word_sub stackpointer (word 96),96]
                      [word_add sig (word 4544),83; scratch,1024;
                       word_sub stackpointer (word 96),96]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_add sig (word 4544),83);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 96),96)])`;;

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on w0    *)
(* and w1 as above.                                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e sig w0 w1p scratch x b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(word_add sig (word 4544),83); (scratch,1024);
          (word_sub stackpointer (word 96),96)] /\
        ALLPAIRS nonoverlapping
         [(word_add sig (word 4544),83); (scratch,1024);
          (word_sub stackpointer (word 96),96)]
         [(word pc,libmldsa_size); (w0,8192); (w1p,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa87_pack_sig_h) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [sig; w0; w1p; scratch] s /\
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
                     e2 = f_events x b sig w0 w1p scratch pc
                                 (word_sub stackpointer (word 96))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [w0,8192; w1p,1024; scratch,1024;
                       word_sub stackpointer (word 96),96]
                      [word_add sig (word 4544),83; scratch,1024;
                       word_sub stackpointer (word 96),96]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_add sig (word 4544),83);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 96),96)])`;;

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
