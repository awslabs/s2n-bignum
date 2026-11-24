(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 18 bits per coefficient, of 2^17 - a: the  *)
(* statement. This is the code for mldsa44_polyz_unpack (mld_polyz_unpack_c  *)
(* in poly_kl.c with MLDSA_GAMMA1 = 2^17, for ML-DSA-44, which the build     *)
(* calls as mld_polyz_unpack) from mldsa-native's portable C implementation  *)
(* compiled by gcc 12 with -O2 and MLD_CONFIG_REDUCE_RAM (see                *)
(* mldsa_native/README.md), which reads 9 bytes for each 4 coefficients and, *)
(* as the C code does, stores the partial results before the final ones. It  *)
(* is verified in the whole image (see libmldsa.ml) against                  *)
(* mld_polyz_unpack_17 of common/mldsa_native_packing.ml. It is also shown   *)
(* to be constant time and memory safe.                                      *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyz_unpack:
       +0x0: add     x8, x1, #0x240
       +0x4: mov     w7, #0x20000
       +0x8: nop
       +0xc: ldrb    w2, [x1]
      +0x10: add     x1, x1, #0x9
      +0x14: str     w2, [x0]
      +0x18: ldurb   w3, [x1, #-8]
      +0x1c: orr     w3, w2, w3, lsl #8
      +0x20: str     w3, [x0]
      +0x24: ldurb   w2, [x1, #-7]
      +0x28: orr     w2, w3, w2, lsl #16
      +0x2c: and     w2, w2, #0x3ffff
      +0x30: str     w2, [x0]
      +0x34: sub     w4, w7, w2
      +0x38: ldurb   w2, [x1, #-7]
      +0x3c: lsr     w2, w2, #2
      +0x40: str     w2, [x0, #4]
      +0x44: ldurb   w3, [x1, #-6]
      +0x48: orr     w3, w2, w3, lsl #6
      +0x4c: str     w3, [x0, #4]
      +0x50: ldurb   w2, [x1, #-5]
      +0x54: orr     w2, w3, w2, lsl #14
      +0x58: and     w2, w2, #0x3ffff
      +0x5c: str     w2, [x0, #4]
      +0x60: sub     w3, w7, w2
      +0x64: ldurb   w2, [x1, #-5]
      +0x68: lsr     w2, w2, #4
      +0x6c: str     w2, [x0, #8]
      +0x70: ldurb   w5, [x1, #-4]
      +0x74: orr     w5, w2, w5, lsl #4
      +0x78: str     w5, [x0, #8]
      +0x7c: ldurb   w2, [x1, #-3]
      +0x80: orr     w2, w5, w2, lsl #12
      +0x84: and     w2, w2, #0x3ffff
      +0x88: str     w2, [x0, #8]
      +0x8c: sub     w2, w7, w2
      +0x90: ldurb   w5, [x1, #-3]
      +0x94: lsr     w5, w5, #6
      +0x98: str     w5, [x0, #12]
      +0x9c: ldurb   w6, [x1, #-2]
      +0xa0: orr     w6, w5, w6, lsl #2
      +0xa4: str     w6, [x0, #12]
      +0xa8: ldurb   w5, [x1, #-1]
      +0xac: stp     w4, w3, [x0]
      +0xb0: add     x0, x0, #0x10
      +0xb4: stur    w2, [x0, #-8]
      +0xb8: orr     w3, w6, w5, lsl #10
      +0xbc: sub     w2, w7, w3
      +0xc0: stur    w2, [x0, #-4]
      +0xc4: cmp     x8, x1
      +0xc8: b.ne    <mldsa44_polyz_unpack+0xc>
      +0xcc: ret
 ***)

let MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa44_polyz_unpack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,576)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read PC s = word (pc + mldsa44_polyz_unpack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 576
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_polyz_unpack_17 b i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,576)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read PC s = word (pc + mldsa44_polyz_unpack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 576
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = mld_polyz_unpack_17 b i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc returnaddress /\
                     memaccess_inbounds e2 [a,576; r,1024] [r,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,576)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read PC s = word (pc + mldsa44_polyz_unpack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc returnaddress /\
                     memaccess_inbounds e2 [a,576; r,1024] [r,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
