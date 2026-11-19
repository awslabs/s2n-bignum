(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 13 bits per coefficient, of 2^12 - a: the  *)
(* statement. This is the code for mldsa_polyt0_unpack (mld_polyt0_unpack in *)
(* poly.c) from mldsa-native's portable C implementation compiled by gcc 12  *)
(* with -Os (see mldsa_native/README.md), which reads 13 bytes for each 8    *)
(* coefficients and, as the C code does, stores the partial results before   *)
(* the final ones. It is verified in the whole image (see libmldsa.ml)       *)
(* against mld_polyt0_unpack of common/mldsa_native_packing.ml. It is also   *)
(* shown to be constant time and memory safe.                                *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyt0_unpack:
       +0x0: add     x12, x0, #0x400
       +0x4: mov     w2, #0x1000
       +0x8: ldrb    w3, [x1]
       +0xc: add     x1, x1, #0xd
      +0x10: str     w3, [x0]
      +0x14: ldurb   w9, [x1, #-12]
      +0x18: orr     w9, w3, w9, lsl #8
      +0x1c: and     w9, w9, #0x1fff
      +0x20: str     w9, [x0]
      +0x24: sub     w9, w2, w9
      +0x28: ldurb   w4, [x1, #-12]
      +0x2c: lsr     w4, w4, #5
      +0x30: str     w4, [x0, #4]
      +0x34: ldurb   w3, [x1, #-11]
      +0x38: orr     w3, w4, w3, lsl #3
      +0x3c: str     w3, [x0, #4]
      +0x40: ldurb   w8, [x1, #-10]
      +0x44: orr     w8, w3, w8, lsl #11
      +0x48: and     w8, w8, #0x1fff
      +0x4c: str     w8, [x0, #4]
      +0x50: sub     w8, w2, w8
      +0x54: ldurb   w3, [x1, #-10]
      +0x58: lsr     w3, w3, #2
      +0x5c: str     w3, [x0, #8]
      +0x60: ldurb   w7, [x1, #-9]
      +0x64: orr     w7, w3, w7, lsl #6
      +0x68: and     w7, w7, #0x1fff
      +0x6c: str     w7, [x0, #8]
      +0x70: sub     w7, w2, w7
      +0x74: ldurb   w4, [x1, #-9]
      +0x78: lsr     w4, w4, #7
      +0x7c: str     w4, [x0, #12]
      +0x80: ldurb   w3, [x1, #-8]
      +0x84: orr     w3, w4, w3, lsl #1
      +0x88: str     w3, [x0, #12]
      +0x8c: ldurb   w6, [x1, #-7]
      +0x90: orr     w6, w3, w6, lsl #9
      +0x94: and     w6, w6, #0x1fff
      +0x98: str     w6, [x0, #12]
      +0x9c: sub     w6, w2, w6
      +0xa0: ldurb   w4, [x1, #-7]
      +0xa4: lsr     w4, w4, #4
      +0xa8: str     w4, [x0, #16]
      +0xac: ldurb   w3, [x1, #-6]
      +0xb0: orr     w3, w4, w3, lsl #4
      +0xb4: str     w3, [x0, #16]
      +0xb8: ldurb   w5, [x1, #-5]
      +0xbc: orr     w5, w3, w5, lsl #12
      +0xc0: and     w5, w5, #0x1fff
      +0xc4: str     w5, [x0, #16]
      +0xc8: sub     w5, w2, w5
      +0xcc: ldurb   w3, [x1, #-5]
      +0xd0: lsr     w3, w3, #1
      +0xd4: str     w3, [x0, #20]
      +0xd8: ldurb   w4, [x1, #-4]
      +0xdc: orr     w4, w3, w4, lsl #7
      +0xe0: and     w4, w4, #0x1fff
      +0xe4: str     w4, [x0, #20]
      +0xe8: sub     w4, w2, w4
      +0xec: ldurb   w3, [x1, #-4]
      +0xf0: lsr     w3, w3, #6
      +0xf4: str     w3, [x0, #24]
      +0xf8: ldurb   w10, [x1, #-3]
      +0xfc: orr     w10, w3, w10, lsl #2
     +0x100: str     w10, [x0, #24]
     +0x104: ldurb   w3, [x1, #-2]
     +0x108: orr     w3, w10, w3, lsl #10
     +0x10c: and     w3, w3, #0x1fff
     +0x110: str     w3, [x0, #24]
     +0x114: sub     w3, w2, w3
     +0x118: ldurb   w11, [x1, #-2]
     +0x11c: lsr     w11, w11, #3
     +0x120: str     w11, [x0, #28]
     +0x124: ldurb   w10, [x1, #-1]
     +0x128: stp     w9, w8, [x0]
     +0x12c: stp     w7, w6, [x0, #8]
     +0x130: orr     w10, w11, w10, lsl #5
     +0x134: stp     w5, w4, [x0, #16]
     +0x138: add     x0, x0, #0x20
     +0x13c: stur    w3, [x0, #-8]
     +0x140: sub     w3, w2, w10
     +0x144: stur    w3, [x0, #-4]
     +0x148: cmp     x0, x12
     +0x14c: b.ne    <mldsa_polyt0_unpack+0x8>
     +0x150: ret
 ***)

let MLDSA_NATIVE_POLYT0_UNPACK_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa_polyt0_unpack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_UNPACK_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,416)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_polyt0_unpack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 416
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_polyt0_unpack b i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYT0_UNPACK_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYT0_UNPACK_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_UNPACK_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,416)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_polyt0_unpack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 416
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = mld_polyt0_unpack b i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc returnaddress /\
                     memaccess_inbounds e2 [a,416; r,1024] [r,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYT0_UNPACK_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYT0_UNPACK_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_UNPACK_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,416)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_polyt0_unpack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc returnaddress /\
                     memaccess_inbounds e2 [a,416; r,1024] [r,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYT0_UNPACK_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYT0_UNPACK_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
