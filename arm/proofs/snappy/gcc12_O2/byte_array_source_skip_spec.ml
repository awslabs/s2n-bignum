(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::ByteArraySource::Skip(size_t n): ptr_ += n, left_ -= n (the     *)
(* fields at this + 8 and this + 16; no check, the caller skips at most     *)
(* left_ bytes). The method of the vtable slot vtable + 32 of a             *)
(* ByteArraySource (arm/proofs/snappy/decompressor_objects.ml).             *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "common/footprint.ml";;

(*** The code in the image (see the listing in layout.ml):

    ByteArraySource_Skip:
     +0x0  ldp     x3, x2, [x0, #8]
     +0x4  add     x3, x3, x1
     +0x8  sub     x1, x2, x1
     +0xc  stp     x3, x1, [x0, #8]
    +0x10  ret
 ***)

let SNAPPY_BYTE_ARRAY_SOURCE_SKIP_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "ByteArraySource_Skip"];;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety.                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_BYTE_ARRAY_SOURCE_SKIP_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e src n p l pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
     nonoverlapping (word_add src (word 8),16) (word pc,libsnappy_size)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + ByteArraySource_Skip) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [src; n] s /\
           read (memory :> bytes64 (word_add src (word 8))) s = p /\
           read (memory :> bytes64 (word_add src (word 16))) s = l /\
           read events s = e)
      (\s. read PC s = returnaddress /\
           read (memory :> bytes64 (word_add src (word 8))) s = word_add p n /\
           read (memory :> bytes64 (word_add src (word 16))) s = word_sub l n /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2 (memrange(word_add src (word 8),16)) (memrange(word_add src (word 8),16)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(word_add src (word 8),16)])`;;

let SNAPPY_BYTE_ARRAY_SOURCE_SKIP_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_BYTE_ARRAY_SOURCE_SKIP_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness alone.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_BYTE_ARRAY_SOURCE_SKIP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!src n p l pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
     nonoverlapping (word_add src (word 8),16) (word pc,libsnappy_size)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + ByteArraySource_Skip) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [src; n] s /\
           read (memory :> bytes64 (word_add src (word 8))) s = p /\
           read (memory :> bytes64 (word_add src (word 16))) s = l)
      (\s. read PC s = returnaddress /\
           read (memory :> bytes64 (word_add src (word 8))) s = word_add p n /\
           read (memory :> bytes64 (word_add src (word 16))) s = word_sub l n)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(word_add src (word 8),16)])`;;

let SNAPPY_BYTE_ARRAY_SOURCE_SKIP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_BYTE_ARRAY_SOURCE_SKIP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
