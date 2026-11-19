(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 4 bits per coefficient: the statement. This  *)
(* is the code for mldsa_polyw1_pack_32 (mld_polyw1_pack_32 in poly.c, for   *)
(* ML-DSA-65 and ML-DSA-87) from mldsa-native's portable C implementation    *)
(* compiled by gcc 12 with -Os (see mldsa_native/README.md), which writes a  *)
(* byte for each 2 coefficients. It is verified in the whole image (see      *)
(* libmldsa.ml) against mld_polyw1_pack_32 of                                *)
(* common/mldsa_native_packing.ml, byte by byte. It is also shown to be      *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyw1_pack_32:
       +0x0: mov     x2, #0x0
       +0x4: ldr     w3, [x1, #4]
       +0x8: ldr     w4, [x1], #8
       +0xc: orr     w3, w4, w3, lsl #4
      +0x10: strb    w3, [x0, x2]
      +0x14: add     x2, x2, #0x1
      +0x18: cmp     x2, #0x80
      +0x1c: b.ne    <mldsa_polyw1_pack_32+0x4>
      +0x20: ret
 ***)

let MLDSA_NATIVE_POLYW1_PACK_32_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa_polyw1_pack_32"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYW1_PACK_32_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,128)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_polyw1_pack_32) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !j. j < 128
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyw1_pack_32 x j)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,128)])`;;

let MLDSA_NATIVE_POLYW1_PACK_32_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYW1_PACK_32_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYW1_PACK_32_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,128)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_polyw1_pack_32) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!j. j < 128
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyw1_pack_32 x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc returnaddress /\
                     memaccess_inbounds e2 [a,1024; r,128] [r,128]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,128)])`;;

let MLDSA_NATIVE_POLYW1_PACK_32_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYW1_PACK_32_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYW1_PACK_32_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,128)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_polyw1_pack_32) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc returnaddress /\
                     memaccess_inbounds e2 [a,1024; r,128] [r,128]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,128)])`;;

let MLDSA_NATIVE_POLYW1_PACK_32_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYW1_PACK_32_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
