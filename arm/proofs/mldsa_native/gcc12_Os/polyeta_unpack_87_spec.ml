(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 3 bits per coefficient, of 2 - a: the      *)
(* statement. This is the code for mldsa87_polyeta_unpack                    *)
(* (mld_polyeta_unpack in poly_kl.c with MLDSA_ETA = 2, for ML-DSA-87) from  *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -Os (see *)
(* mldsa_native/README.md), which reads 3 bytes for each 8 coefficients and, *)
(* as the C code does, stores the masked fields before 2 - a over them. It   *)
(* is verified in the whole image (see libmldsa.ml) against                  *)
(* mld_polyeta_unpack_2 of common/mldsa_native_packing.ml. It is also shown  *)
(* to be constant time and memory safe.                                      *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa87_polyeta_unpack:
       +0x0: add     x11, x0, #0x400
       +0x4: mov     w2, #0x2
       +0x8: ldrb    w9, [x1]
       +0xc: add     x1, x1, #0x3
      +0x10: and     w9, w9, #0x7
      +0x14: str     w9, [x0]
      +0x18: sub     w9, w2, w9
      +0x1c: ldurb   w8, [x1, #-3]
      +0x20: ubfx    x8, x8, #3, #3
      +0x24: str     w8, [x0, #4]
      +0x28: sub     w8, w2, w8
      +0x2c: ldurb   w3, [x1, #-2]
      +0x30: ldurb   w4, [x1, #-3]
      +0x34: lsl     w3, w3, #2
      +0x38: orr     w4, w3, w4, lsr #6
      +0x3c: and     w4, w4, #0x7
      +0x40: str     w4, [x0, #8]
      +0x44: sub     w4, w2, w4
      +0x48: ldurb   w7, [x1, #-2]
      +0x4c: ubfx    x7, x7, #1, #3
      +0x50: str     w7, [x0, #12]
      +0x54: sub     w7, w2, w7
      +0x58: ldurb   w6, [x1, #-2]
      +0x5c: ubfx    x6, x6, #4, #3
      +0x60: str     w6, [x0, #16]
      +0x64: sub     w6, w2, w6
      +0x68: ldurb   w5, [x1, #-1]
      +0x6c: ldurb   w3, [x1, #-2]
      +0x70: lsl     w5, w5, #1
      +0x74: orr     w3, w5, w3, lsr #7
      +0x78: and     w3, w3, #0x7
      +0x7c: str     w3, [x0, #20]
      +0x80: sub     w3, w2, w3
      +0x84: ldurb   w5, [x1, #-1]
      +0x88: ubfx    x5, x5, #2, #3
      +0x8c: str     w5, [x0, #24]
      +0x90: sub     w5, w2, w5
      +0x94: ldurb   w10, [x1, #-1]
      +0x98: stp     w9, w8, [x0]
      +0x9c: stp     w4, w7, [x0, #8]
      +0xa0: stp     w6, w3, [x0, #16]
      +0xa4: sub     w3, w2, w10, lsr #5
      +0xa8: add     x0, x0, #0x20
      +0xac: stur    w5, [x0, #-8]
      +0xb0: stur    w3, [x0, #-4]
      +0xb4: cmp     x0, x11
      +0xb8: b.ne    <mldsa87_polyeta_unpack+0x8>
      +0xbc: ret
 ***)

let MLDSA_NATIVE_POLYETA_UNPACK_87_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa87_polyeta_unpack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,96)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa87_polyeta_unpack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 96
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_polyeta_unpack_2 b i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYETA_UNPACK_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYETA_UNPACK_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,96)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa87_polyeta_unpack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 96
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = mld_polyeta_unpack_2 b i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc returnaddress /\
                     memaccess_inbounds e2 [a,96; r,1024] [r,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYETA_UNPACK_87_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYETA_UNPACK_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,96)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa87_polyeta_unpack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc returnaddress /\
                     memaccess_inbounds e2 [a,96; r,1024] [r,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYETA_UNPACK_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYETA_UNPACK_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
