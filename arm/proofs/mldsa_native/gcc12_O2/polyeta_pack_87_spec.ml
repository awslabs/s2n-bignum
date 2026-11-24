(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 3 bits per coefficient, of 2 - a: the        *)
(* statement. This is the code for mldsa87_polyeta_pack (mld_polyeta_pack in *)
(* poly_kl.c with MLDSA_ETA = 2, for ML-DSA-87) from mldsa-native's portable *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mldsa_native/README.md), which writes 3 bytes for each 8 coefficients,    *)
(* with a stack protector. It has a stack frame of 32 bytes for x30, the     *)
(* temporary array of 8 bytes and the stack guard, zeroes the array with a   *)
(* single store, and checks the stack guard before it returns. It is         *)
(* verified in the whole image (see libmldsa.ml) against mld_polyeta_pack_2  *)
(* of common/mldsa_native_packing.ml, byte by byte, with the address of the  *)
(* stack guard in the global offset table. It is also shown to be constant   *)
(* time and memory safe.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa87_polyeta_pack:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]
       +0x8: str     x30, [sp, #-32]!
       +0xc: add     x10, x1, #0x400
      +0x10: mov     w5, #0x2
      +0x14: ldr     x3, [x2]
      +0x18: str     x3, [sp, #24]
      +0x1c: mov     x3, #0x0
      +0x20: ldp     w4, w2, [x1, #4]
      +0x24: add     x0, x0, #0x3
      +0x28: ldp     w6, w9, [x1, #12]
      +0x2c: sub     w2, w5, w2
      +0x30: ldp     w7, w3, [x1, #20]
      +0x34: sub     w4, w5, w4
      +0x38: ldr     w8, [x1, #28]
      +0x3c: sub     w6, w5, w6
      +0x40: sub     w7, w5, w7
      +0x44: sub     w9, w5, w9
      +0x48: sub     w3, w5, w3
      +0x4c: sub     w8, w5, w8
      +0x50: ldr     w11, [x1], #32
      +0x54: ubfiz   w13, w2, #6, #8
      +0x58: ubfiz   w8, w8, #5, #8
      +0x5c: ubfiz   w12, w7, #7, #8
      +0x60: ubfx    x2, x2, #2, #6
      +0x64: ubfiz   w4, w4, #3, #8
      +0x68: ubfiz   w6, w6, #1, #8
      +0x6c: ubfiz   w9, w9, #4, #8
      +0x70: ubfiz   w3, w3, #2, #8
      +0x74: orr     w4, w4, w13
      +0x78: orr     w3, w3, w8
      +0x7c: orr     w6, w6, w9
      +0x80: sub     w8, w5, w11
      +0x84: orr     w2, w2, w12
      +0x88: ubfx    x7, x7, #1, #7
      +0x8c: orr     w4, w4, w8
      +0x90: orr     w2, w2, w6
      +0x94: orr     w3, w3, w7
      +0x98: sturb   w4, [x0, #-3]
      +0x9c: sturb   w2, [x0, #-2]
      +0xa0: sturb   w3, [x0, #-1]
      +0xa4: cmp     x10, x1
      +0xa8: b.ne    <mldsa87_polyeta_pack+0x20>
      +0xac: add     x0, sp, #0x10
      +0xb0: str     xzr, [sp, #16]
      +0xb4: adrp    x0, <page>
      +0xb8: ldr     x0, [x0, #4088]
      +0xbc: ldr     x2, [sp, #24]
      +0xc0: ldr     x1, [x0]
      +0xc4: subs    x2, x2, x1
      +0xc8: mov     x1, #0x0
      +0xcc: b.ne    <mldsa87_polyeta_pack+0xd8>
      +0xd0: ldr     x30, [sp], #32
      +0xd4: ret
      +0xd8: bl      <stack_chk_fail>
 ***)

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_polyeta_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The stack frame is the 32 bytes below the stack pointer: x30 *)
(* at the bottom, the 8 bytes of the temporary array and the stack guard.    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,96); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
         [(r,96); (word_sub stackpointer (word 32),32)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa87_polyeta_pack) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                       s = guard /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !j. j < 96
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyeta_pack_2 x j)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,96);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* input, the output, the stack frame, the GOT entry of the stack guard and  *)
(* the guard, and the writes within the output and the stack frame.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,96); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
         [(r,96); (word_sub stackpointer (word 32),32)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa87_polyeta_pack) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                       s = guard /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!j. j < 96
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyeta_pack_2 x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a guard pc
                            (word_sub stackpointer (word 32))
                            returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; r,96; word_sub stackpointer (word 32),32;
                       word(pc + got_stack_chk_guard),8; guard,8]
                      [r,96; word_sub stackpointer (word 32),32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,96);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,96); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
         [(r,96); (word_sub stackpointer (word 32),32)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa87_polyeta_pack) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                       s = guard /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a guard pc
                            (word_sub stackpointer (word 32))
                            returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; r,96; word_sub stackpointer (word 32),32;
                       word(pc + got_stack_chk_guard),8; guard,8]
                      [r,96; word_sub stackpointer (word 32),32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,96);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
