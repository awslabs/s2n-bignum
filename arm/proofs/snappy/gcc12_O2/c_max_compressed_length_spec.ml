(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy_max_compressed_length(size_t source_length) of the C interface     *)
(* (snappy-c.cc), which returns snappy::MaxCompressedLength(source_length):  *)
(* gcc 12 with -O2 compiles it to a tail call. Verified in the whole image   *)
(* (see libsnappy.ml) relative to the contract of MaxCompressedLength.       *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/max_compressed_length_spec.ml";;

(*** The code in the image:

    c_snappy_max_compressed_length:
      +0x0   b       MaxCompressedLength
 ***)

let SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "c_snappy_max_compressed_length"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + c_snappy_max_compressed_length) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [n] s)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  word(snappy_max_compressed_length_gcc12_O2_result (val n)))
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`;;

let SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
    SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* Memory safety with correctness: the events are jumps only.               *)

let SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!e n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + c_snappy_max_compressed_length) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [n] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  word(snappy_max_compressed_length_gcc12_O2_result (val n)) /\
                  ?e2. read events s = APPEND e2 e /\ memaccess_inset e2 {} {})
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`;;

let SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
    SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
