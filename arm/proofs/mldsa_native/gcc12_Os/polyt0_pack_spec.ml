(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 13 bits per coefficient, of 2^12 - a: the    *)
(* statement. This is the code for mldsa_polyt0_pack (mld_polyt0_pack in     *)
(* poly.c) from mldsa-native's portable C implementation compiled by gcc 12  *)
(* with -Os (see mldsa_native/README.md), which writes 13 bytes for each 8   *)
(* coefficients, with a stack protector: the code saves the return address   *)
(* and the stack guard in a frame of 64 bytes, zeroes the part of the frame  *)
(* that held the last values, and checks the guard before it returns. It is  *)
(* verified in the whole image (see libmldsa.ml) against mld_polyt0_pack of  *)
(* common/mldsa_native_packing.ml, byte by byte, with the address of the     *)
(* stack guard in the global offset table. It is also shown to be constant   *)
(* time and memory safe.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyt0_pack:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]
       +0x8: str     x30, [sp, #-64]!
       +0xc: add     x11, x0, #0x1a0
      +0x10: ldr     x3, [x2]
      +0x14: str     x3, [sp, #56]
      +0x18: mov     x3, #0x0
      +0x1c: mov     w2, #0x1000
      +0x20: ldp     w10, w6, [x1]
      +0x24: add     x0, x0, #0xd
      +0x28: ldp     w9, w5, [x1, #8]
      +0x2c: sub     w6, w2, w6
      +0x30: sub     w10, w2, w10
      +0x34: ubfiz   w12, w6, #5, #3
      +0x38: sub     w9, w2, w9
      +0x3c: ldp     w4, w8, [x1, #16]
      +0x40: sub     w5, w2, w5
      +0x44: ldp     w3, w7, [x1, #24]
      +0x48: sturb   w10, [x0, #-13]
      +0x4c: orr     w10, w12, w10, lsr #8
      +0x50: sturb   w10, [x0, #-12]
      +0x54: lsr     w10, w6, #3
      +0x58: sturb   w10, [x0, #-11]
      +0x5c: ubfiz   w10, w9, #2, #6
      +0x60: sub     w4, w2, w4
      +0x64: orr     w6, w10, w6, lsr #11
      +0x68: sturb   w6, [x0, #-10]
      +0x6c: ubfiz   w6, w5, #7, #1
      +0x70: sub     w8, w2, w8
      +0x74: orr     w9, w6, w9, lsr #6
      +0x78: lsr     w6, w5, #1
      +0x7c: sturb   w6, [x0, #-8]
      +0x80: ubfiz   w6, w4, #4, #4
      +0x84: orr     w5, w6, w5, lsr #9
      +0x88: sturb   w5, [x0, #-7]
      +0x8c: lsr     w5, w4, #4
      +0x90: sub     w3, w2, w3
      +0x94: sturb   w5, [x0, #-6]
      +0x98: ubfiz   w5, w8, #1, #7
      +0x9c: orr     w4, w5, w4, lsr #12
      +0xa0: sub     w7, w2, w7
      +0xa4: sturb   w4, [x0, #-5]
      +0xa8: ubfiz   w4, w3, #6, #2
      +0xac: orr     w8, w4, w8, lsr #7
      +0xb0: lsr     w4, w3, #2
      +0xb4: sturb   w4, [x0, #-3]
      +0xb8: ubfiz   w4, w7, #3, #5
      +0xbc: orr     w3, w4, w3, lsr #10
      +0xc0: lsr     w7, w7, #5
      +0xc4: sturb   w9, [x0, #-9]
      +0xc8: add     x1, x1, #0x20
      +0xcc: sturb   w8, [x0, #-4]
      +0xd0: sturb   w3, [x0, #-2]
      +0xd4: sturb   w7, [x0, #-1]
      +0xd8: cmp     x11, x0
      +0xdc: b.ne    <mldsa_polyt0_pack+0x20>
      +0xe0: add     x0, sp, #0x18
      +0xe4: stp     xzr, xzr, [sp, #24]
      +0xe8: stp     xzr, xzr, [sp, #40]
      +0xec: adrp    x0, <page>
      +0xf0: ldr     x0, [x0, #4088]
      +0xf4: ldr     x2, [sp, #56]
      +0xf8: ldr     x1, [x0]
      +0xfc: subs    x2, x2, x1
     +0x100: mov     x1, #0x0
     +0x104: b.eq    <mldsa_polyt0_pack+0x10c>
     +0x108: bl      <stack_chk_fail>
     +0x10c: ldr     x30, [sp], #64
     +0x110: ret
 ***)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa_polyt0_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,416); (word_sub stackpointer (word 64),64)] /\
        ALLPAIRS nonoverlapping
         [(r,416); (word_sub stackpointer (word 64),64)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_polyt0_pack) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !j. j < 416
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyt0_pack x j)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,416);
                memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* input, the output, the stack frame, the GOT entry of the stack guard and  *)
(* the guard, and the writes within the output and the stack frame.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,416); (word_sub stackpointer (word 64),64)] /\
        ALLPAIRS nonoverlapping
         [(r,416); (word_sub stackpointer (word 64),64)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_polyt0_pack) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!j. j < 416
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyt0_pack x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a guard pc
                            (word_sub stackpointer (word 64)) returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; r,416; word_sub stackpointer (word 64),64;
                       word(pc + got_stack_chk_guard),8; guard,8]
                      [r,416; word_sub stackpointer (word 64),64]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,416);
                memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,416); (word_sub stackpointer (word 64),64)] /\
        ALLPAIRS nonoverlapping
         [(r,416); (word_sub stackpointer (word 64),64)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_polyt0_pack) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a guard pc
                            (word_sub stackpointer (word 64)) returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; r,416; word_sub stackpointer (word 64),64;
                       word(pc + got_stack_chk_guard),8; guard,8]
                      [r,416; word_sub stackpointer (word 64),64]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,416);
                memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
