(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::MaxCompressedLength(size_t source_bytes), the largest size of the *)
(* compressed form of source_bytes bytes: 32 + n + n / 6, or SIZE_MAX if     *)
(* n > (SIZE_MAX - 32) / 7 * 6, as in snappy.cc. This is the code compiled   *)
(* by gcc 12 with -O2 (see arm/snappy/README.md), verified in the whole      *)
(* image (see libsnappy.ml).                                                 *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "common/footprint.ml";;

(*** The code in the image (see the listing in layout.ml):

    MaxCompressedLength:
      +0x0   mov     x1, #0xdb4e                0xdb6db6db6db6db4e
      +0x4   movk    x1, #0x6db6, lsl #16       = (2^64 - 1 - 32) DIV 7 * 6
      +0x8   movk    x1, #0xb6db, lsl #32
      +0xc   movk    x1, #0xdb6d, lsl #48
      +0x10  cmp     x0, x1
      +0x14  b.hi    +0x30
      +0x18  mov     x2, #0xaaaaaaaaaaaaaaaa
      +0x1c  add     x1, x0, #0x20
      +0x20  movk    x2, #0xaaab
      +0x24  umulh   x0, x0, x2                 n DIV 6 is umulh(n,..ab) >> 2
      +0x28  add     x0, x1, x0, lsr #2
      +0x2c  ret
      +0x30  mov     x0, #0xffffffffffffffff
      +0x34  ret
 ***)

let SNAPPY_MAX_COMPRESSED_LENGTH_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "MaxCompressedLength"];;

(* ------------------------------------------------------------------------- *)
(* The result as a function of n, as in snappy.cc.                           *)
(* ------------------------------------------------------------------------- *)

let snappy_max_compressed_length_gcc12_O2_result = new_definition
 `snappy_max_compressed_length_gcc12_O2_result (n:num) =
    if n > (2 EXP 64 - 1 - 32) DIV 7 * 6 then 2 EXP 64 - 1
    else 32 + n + n DIV 6`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + MaxCompressedLength) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [n] s)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  word(snappy_max_compressed_length_gcc12_O2_result (val n)))
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`;;

let SNAPPY_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety: the same, and the function makes no memory *)
(* access.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!e n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + MaxCompressedLength) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [n] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  word(snappy_max_compressed_length_gcc12_O2_result (val n)) /\
                  ?e2. read events s = APPEND e2 e /\ memaccess_inset e2 {} {})
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`;;

let SNAPPY_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* The result below the overflow bound, e.g. for the fragments of the        *)
(* compressor (at most 65536 bytes).                                         *)

let SNAPPY_MAX_COMPRESSED_LENGTH_GCC12_O2_RESULT_SMALL = prove
 (`!n. n < 2 EXP 32
       ==> snappy_max_compressed_length_gcc12_O2_result n = 32 + n + n DIV 6`,
  REWRITE_TAC[snappy_max_compressed_length_gcc12_O2_result; GT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;
