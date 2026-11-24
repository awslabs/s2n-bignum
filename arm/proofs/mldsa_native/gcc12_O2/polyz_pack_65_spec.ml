(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 20 bits per coefficient, of 2^19 - a: the    *)
(* statement. This is the code for mldsa65_polyz_pack (mld_polyz_pack in     *)
(* poly_kl.c with MLDSA_GAMMA1 = 2^19, for ML-DSA-65) from mldsa-native's    *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mldsa_native/README.md), which writes 5 bytes for each 2 coefficients,    *)
(* with a stack protector. Its stack frame of 48 bytes holds the return      *)
(* address, the 16 bytes of a temporary array, which the code zeroes with    *)
(* one store of two zero registers, and the canary, which it checks against  *)
(* the stack guard before it returns. It is verified in the whole image (see *)
(* libmldsa.ml) against mld_polyz_pack_19 of common/mldsa_native_packing.ml, *)
(* byte by byte, with the address of the stack guard in the global offset    *)
(* table. It is also shown to be constant time and memory safe.              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyz_pack:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]
       +0x8: str     x30, [sp, #-48]!
       +0xc: add     x7, x0, #0x280
      +0x10: mov     w5, #0x80000
      +0x14: ldr     x3, [x2]
      +0x18: str     x3, [sp, #40]
      +0x1c: mov     x3, #0x0
      +0x20: ldp     w3, w2, [x1]
      +0x24: add     x0, x0, #0x5
      +0x28: add     x1, x1, #0x8
      +0x2c: sub     w2, w5, w2
      +0x30: sub     w3, w5, w3
      +0x34: sturb   w3, [x0, #-5]
      +0x38: ubfiz   w4, w2, #4, #4
      +0x3c: lsr     w6, w2, #4
      +0x40: orr     w4, w4, w3, lsr #16
      +0x44: lsr     w2, w2, #12
      +0x48: lsr     w3, w3, #8
      +0x4c: sturb   w3, [x0, #-4]
      +0x50: sturb   w4, [x0, #-3]
      +0x54: sturb   w6, [x0, #-2]
      +0x58: sturb   w2, [x0, #-1]
      +0x5c: cmp     x7, x0
      +0x60: b.ne    <mldsa65_polyz_pack+0x20>
      +0x64: add     x0, sp, #0x18
      +0x68: stp     xzr, xzr, [sp, #24]
      +0x6c: adrp    x0, <page>
      +0x70: ldr     x0, [x0, #4088]
      +0x74: ldr     x2, [sp, #40]
      +0x78: ldr     x1, [x0]
      +0x7c: subs    x2, x2, x1
      +0x80: mov     x1, #0x0
      +0x84: b.ne    <mldsa65_polyz_pack+0x90>
      +0x88: ldr     x30, [sp], #48
      +0x8c: ret
      +0x90: bl      <stack_chk_fail>
 ***)

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_polyz_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The stack frame of 48 bytes, below the stack pointer, is     *)
(* the only memory besides the output that the code writes.                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,640); (word_sub stackpointer (word 48),48)] /\
        ALLPAIRS nonoverlapping
         [(r,640); (word_sub stackpointer (word 48),48)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa65_polyz_pack) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  (!j. j < 640
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyz_pack_19 x j))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,640);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* input, the output, the stack frame, the GOT entry of the stack guard and  *)
(* the guard, and the writes within the output and the stack frame.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,640); (word_sub stackpointer (word 48),48)] /\
        ALLPAIRS nonoverlapping
         [(r,640); (word_sub stackpointer (word 48),48)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa65_polyz_pack) /\
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
                  (!j. j < 640
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyz_pack_19 x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a guard pc
                            (word_sub stackpointer (word 48))
                            returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; r,640; word_sub stackpointer (word 48),48;
                       word(pc + got_stack_chk_guard),8; guard,8]
                      [r,640; word_sub stackpointer (word 48),48]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,640);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,640); (word_sub stackpointer (word 48),48)] /\
        ALLPAIRS nonoverlapping
         [(r,640); (word_sub stackpointer (word 48),48)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa65_polyz_pack) /\
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
                            (word_sub stackpointer (word 48))
                            returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; r,640; word_sub stackpointer (word 48),48;
                       word(pc + got_stack_chk_guard),8; guard,8]
                      [r,640; word_sub stackpointer (word 48),48]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,640);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
