(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 13 bits per coefficient, of 2^12 - a: the    *)
(* statement. This is the code for mldsa_polyt0_pack (mld_polyt0_pack in     *)
(* poly.c) from mldsa-native's portable C implementation compiled by gcc 12  *)
(* with -O2 (see mldsa_native/README.md), which writes 13 bytes for each 8   *)
(* coefficients, 8 of them as one 64-bit word assembled in a vector          *)
(* register, with a stack protector: the code saves the return address and   *)
(* the stack guard in a frame of 64 bytes, zeroes the 32 bytes of the        *)
(* temporary array in the frame with two stores of two zero registers, and   *)
(* checks the guard before it returns. It is verified in the whole image     *)
(* (see libmldsa.ml) against mld_polyt0_pack of                              *)
(* common/mldsa_native_packing.ml, byte by byte, with the address of the     *)
(* stack guard in the global offset table. It is also shown to be constant   *)
(* time and memory safe.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyt0_pack:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]
       +0x8: str     x30, [sp, #-64]!
       +0xc: add     x10, x0, #0x1a0
      +0x10: ldr     x3, [x2]
      +0x14: str     x3, [sp, #56]
      +0x18: mov     x3, #0x0
      +0x1c: mov     w3, #0x1000
      +0x20: nop
      +0x24: ldp     w9, w6, [x1]
      +0x28: add     x0, x0, #0xd
      +0x2c: ldp     w7, w4, [x1, #8]
      +0x30: sub     w6, w3, w6
      +0x34: sub     w9, w3, w9
      +0x38: fmov    s0, w6
      +0x3c: ubfiz   w2, w6, #5, #3
      +0x40: sub     w7, w3, w7
      +0x44: ushr    v1.2s, v0.2s, #3
      +0x48: orr     w2, w2, w9, lsr #8
      +0x4c: fmov    d0, x9
      +0x50: ubfiz   w11, w7, #2, #6
      +0x54: orr     w6, w11, w6, lsr #11
      +0x58: sub     w4, w3, w4
      +0x5c: mov     v0.b[1], w2
      +0x60: fmov    s2, w4
      +0x64: ubfiz   w2, w4, #7, #1
      +0x68: orr     w9, w2, w7, lsr #6
      +0x6c: ushr    v2.2s, v2.2s, #1
      +0x70: ldp     w5, w8, [x1, #16]
      +0x74: mov     v0.b[2], v1.b[0]
      +0x78: sub     w5, w3, w5
      +0x7c: fmov    s1, w5
      +0x80: sub     w8, w3, w8
      +0x84: mov     v0.b[3], w6
      +0x88: ubfiz   w7, w5, #4, #4
      +0x8c: orr     w4, w7, w4, lsr #9
      +0x90: ushr    v1.2s, v1.2s, #4
      +0x94: ldp     w2, w7, [x1, #24]
      +0x98: ubfiz   w12, w8, #1, #7
      +0x9c: mov     v0.b[4], w9
      +0xa0: orr     w5, w12, w5, lsr #12
      +0xa4: sub     w2, w3, w2
      +0xa8: sub     w6, w3, w7
      +0xac: sturb   w5, [x0, #-5]
      +0xb0: add     x1, x1, #0x20
      +0xb4: ubfiz   w11, w2, #6, #2
      +0xb8: ubfiz   w7, w6, #3, #5
      +0xbc: mov     v0.b[5], v2.b[0]
      +0xc0: orr     w7, w7, w2, lsr #10
      +0xc4: orr     w8, w11, w8, lsr #7
      +0xc8: lsr     w2, w2, #2
      +0xcc: lsr     w6, w6, #5
      +0xd0: sturb   w8, [x0, #-4]
      +0xd4: sturb   w2, [x0, #-3]
      +0xd8: mov     v0.b[6], w4
      +0xdc: sturb   w7, [x0, #-2]
      +0xe0: sturb   w6, [x0, #-1]
      +0xe4: mov     v0.b[7], v1.b[0]
      +0xe8: stur    d0, [x0, #-13]
      +0xec: cmp     x0, x10
      +0xf0: b.ne    <mldsa_polyt0_pack+0x24>
      +0xf4: add     x0, sp, #0x18
      +0xf8: stp     xzr, xzr, [sp, #24]
      +0xfc: stp     xzr, xzr, [sp, #40]
     +0x100: adrp    x0, <page>
     +0x104: ldr     x0, [x0, #4088]
     +0x108: ldr     x2, [sp, #56]
     +0x10c: ldr     x1, [x0]
     +0x110: subs    x2, x2, x1
     +0x114: mov     x1, #0x0
     +0x118: b.ne    <mldsa_polyt0_pack+0x124>
     +0x11c: ldr     x30, [sp], #64
     +0x120: ret
     +0x124: bl      <stack_chk_fail>
 ***)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_polyt0_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
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
                    mldsa_native_libmldsa_gcc12_O2_mc /\
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

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* input, the output, the stack frame, the GOT entry of the stack guard and  *)
(* the guard, and the writes within the output and the stack frame.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
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
                    mldsa_native_libmldsa_gcc12_O2_mc /\
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

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
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
                    mldsa_native_libmldsa_gcc12_O2_mc /\
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

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
