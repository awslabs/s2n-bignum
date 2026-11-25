(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::ByteArraySource::Peek(size_t* len): returns ptr_ (at this + 8)   *)
(* and stores left_ (at this + 16) at len. The method of the vtable slot    *)
(* vtable + 24 of a ByteArraySource (arm/proofs/snappy/                      *)
(* decompressor_objects.ml). It reads the two fields and writes only *len. *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "common/footprint.ml";;

(*** The code in the image (see the listing in layout.ml):

    ByteArraySource_Peek:
     +0x0  ldp     x0, x2, [x0, #8]
     +0x4  str     x2, [x1]
     +0x8  ret
 ***)

let SNAPPY_BYTE_ARRAY_SOURCE_PEEK_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "ByteArraySource_Peek"];;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety.                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_BYTE_ARRAY_SOURCE_PEEK_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e src np p l pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
     nonoverlapping (np,8) (word pc,libsnappy_size)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + ByteArraySource_Peek) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [src; np] s /\
           read (memory :> bytes64 (word_add src (word 8))) s = p /\
           read (memory :> bytes64 (word_add src (word 16))) s = l /\
           read events s = e)
      (\s. read PC s = returnaddress /\
           C_RETURN s = p /\
           read (memory :> bytes64 np) s = l /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2 (memrange(word_add src (word 8),16)) (memrange(np,8)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(np,8)])`;;

let SNAPPY_BYTE_ARRAY_SOURCE_PEEK_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_BYTE_ARRAY_SOURCE_PEEK_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness alone.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_BYTE_ARRAY_SOURCE_PEEK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!src np p l pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
     nonoverlapping (np,8) (word pc,libsnappy_size)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + ByteArraySource_Peek) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [src; np] s /\
           read (memory :> bytes64 (word_add src (word 8))) s = p /\
           read (memory :> bytes64 (word_add src (word 16))) s = l)
      (\s. read PC s = returnaddress /\
           C_RETURN s = p /\
           read (memory :> bytes64 np) s = l)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(np,8)])`;;

let SNAPPY_BYTE_ARRAY_SOURCE_PEEK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_BYTE_ARRAY_SOURCE_PEEK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
