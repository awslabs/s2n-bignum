(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::ByteArraySource::Available() const: the number of unread bytes,  *)
(* left_ (at this + 16). The method of the vtable slot vtable + 16 of a     *)
(* ByteArraySource (arm/proofs/snappy/decompressor_objects.ml). It reads    *)
(* only that field and writes no memory.                                     *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "common/footprint.ml";;

(*** The code in the image (see the listing in layout.ml):

    ByteArraySource_Available:
     +0x0  ldr     x0, [x0, #16]
     +0x4  ret
 ***)

let SNAPPY_BYTE_ARRAY_SOURCE_AVAILABLE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "ByteArraySource_Available"];;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety.                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_BYTE_ARRAY_SOURCE_AVAILABLE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e src l pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + ByteArraySource_Available) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [src] s /\
           read (memory :> bytes64 (word_add src (word 16))) s = l /\
           read events s = e)
      (\s. read PC s = returnaddress /\
           C_RETURN s = l /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2 (memrange(word_add src (word 16),8)) ({}))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`;;

let SNAPPY_BYTE_ARRAY_SOURCE_AVAILABLE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_BYTE_ARRAY_SOURCE_AVAILABLE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness alone.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_BYTE_ARRAY_SOURCE_AVAILABLE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!src l pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + ByteArraySource_Available) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [src] s /\
           read (memory :> bytes64 (word_add src (word 16))) s = l)
      (\s. read PC s = returnaddress /\
           C_RETURN s = l)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`;;

let SNAPPY_BYTE_ARRAY_SOURCE_AVAILABLE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_BYTE_ARRAY_SOURCE_AVAILABLE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
