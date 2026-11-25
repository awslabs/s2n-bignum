(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::CompressionContext::CompressionContext(CompressionContext&&       *)
(* other), the move constructor: the new context at cc gets the pointer wm   *)
(* and the flag byte b of other, and other's pointer becomes nullptr, so the *)
(* ownership of the WorkingMemory (and of its heap blocks, if any) moves to  *)
(* cc and other's destructor frees nothing. No heap, no stack.               *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "common/footprint.ml";;

(*** The code in the image (see the listing in layout.ml):

    CompressionContext_ctor__CompressionContextrr:
     +0x0  ldr     x2, [x1]
     +0x4  str     x2, [x0]
     +0x8  ldrb    w2, [x1, #8]
     +0xc  str     xzr, [x1]
    +0x10  strb    w2, [x0, #8]
    +0x14  ret
 ***)

let SNAPPY_COMPRESSION_CONTEXT_CTOR_MOVE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "CompressionContext_ctor__CompressionContextrr"];;

let SNAPPY_COMPRESSION_CONTEXT_CTOR_MOVE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e cc other wm b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        nonoverlapping (cc,16) (other,16) /\
        ALL (nonoverlapping (word pc,libsnappy_size)) [(cc,16); (other,16)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_ctor__CompressionContextrr) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [cc; other] s /\
                  read (memory :> bytes64 other) s = wm /\
                  read (memory :> bytes8 (word_add other (word 8))) s = b /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes64 cc) s = wm /\
                  read (memory :> bytes8 (word_add cc (word 8))) s = b /\
                  read (memory :> bytes64 other) s = word 0 /\
                  ?e2. read events s = APPEND e2 e /\
                       memaccess_inset e2
                        (memrange(other,16)) (memrange(cc,16) UNION memrange(other,16)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(cc,16)] ,,
              MAYCHANGE [memory :> bytes(other,8)])`;;

let SNAPPY_COMPRESSION_CONTEXT_CTOR_MOVE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_CTOR_MOVE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

let SNAPPY_COMPRESSION_CONTEXT_CTOR_MOVE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!cc other wm b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        nonoverlapping (cc,16) (other,16) /\
        ALL (nonoverlapping (word pc,libsnappy_size)) [(cc,16); (other,16)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_ctor__CompressionContextrr) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [cc; other] s /\
                  read (memory :> bytes64 other) s = wm /\
                  read (memory :> bytes8 (word_add other (word 8))) s = b)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes64 cc) s = wm /\
                  read (memory :> bytes8 (word_add cc (word 8))) s = b /\
                  read (memory :> bytes64 other) s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(cc,16)] ,,
              MAYCHANGE [memory :> bytes(other,8)])`;;

let SNAPPY_COMPRESSION_CONTEXT_CTOR_MOVE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_CTOR_MOVE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
