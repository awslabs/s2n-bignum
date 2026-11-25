(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::CompressionContext::operator=(CompressionContext&& other): if     *)
(* this is not other, Reset() this, then take other's pointer and flag and   *)
(* make other's pointer nullptr; return this. Two cases are stated:         *)
(*                                                                           *)
(*  - SELF: cc = other; nothing changes but the frame.                       *)
(*  - NULL: cc <> other and cc is empty (working_memory_ = nullptr, as after *)
(*    a move or Reset), so Reset frees nothing, and the ownership of other's *)
(*    WorkingMemory (and of its blocks, if any) moves to cc. No heap.        *)
(*                                                                           *)
(* (The assignment to an owning context frees its blocks first, as          *)
(* RESET_OWNED; that case is not stated here.)                              *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/compression_context_reset_spec.ml";;

(*** The code in the image (see the listing in layout.ml):

    CompressionContext_operator_assign:
     +0x0  stp     x29, x30, [sp, #-32]!
     +0x4  mov     x29, sp
     +0x8  stp     x19, x20, [sp, #16]
     +0xc  mov     x19, x0
    +0x10  cmp     x0, x1
    +0x14  b.eq    join1                      this == &other
    +0x18  mov     x20, x1
    +0x1c  bl      CompressionContext_Reset
    +0x20  ldr     x1, [x20]
    +0x24  ldrb    w0, [x20, #8]
    +0x28  str     x1, [x19]
    +0x2c  strb    w0, [x19, #8]
    +0x30  str     xzr, [x20]
  join1:
    +0x34  mov     x0, x19
    +0x38  ldp     x19, x20, [sp, #16]
    +0x3c  ldp     x29, x30, [sp], #32
    +0x40  ret
 ***)

let SNAPPY_COMPRESSION_CONTEXT_OPERATOR_ASSIGN_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "CompressionContext_operator_assign"];;

(* ------------------------------------------------------------------------- *)
(* The assignment to itself.                                                 *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_COMPRESSION_CONTEXT_OPERATOR_ASSIGN_SELF_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e cc pc sp returnaddress x19 x20 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\
        nonoverlapping (word pc,libsnappy_size) (word_sub sp (word 32),32)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_operator_assign) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_ARGUMENTS [cc; cc] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_RETURN s = cc /\
                  ?e2. read events s = APPEND e2 e /\
                       memaccess_inset e2
                        (memrange(word_sub sp (word 32),32))
                        (memrange(word_sub sp (word 32),32)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)])`;;

let SNAPPY_COMPRESSION_CONTEXT_OPERATOR_ASSIGN_SELF_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_OPERATOR_ASSIGN_SELF_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

let SNAPPY_COMPRESSION_CONTEXT_OPERATOR_ASSIGN_SELF_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!cc pc sp returnaddress x19 x20 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\
        nonoverlapping (word pc,libsnappy_size) (word_sub sp (word 32),32)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_operator_assign) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_ARGUMENTS [cc; cc] s)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_RETURN s = cc)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)])`;;

let SNAPPY_COMPRESSION_CONTEXT_OPERATOR_ASSIGN_SELF_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_OPERATOR_ASSIGN_SELF_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The assignment to an empty context.                                       *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_COMPRESSION_CONTEXT_OPERATOR_ASSIGN_NULL_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e cc other wm b pc sp returnaddress x19 x20 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\ ~(cc = other) /\
        nonoverlapping (cc,16) (other,16) /\
        ALLPAIRS nonoverlapping
         [(cc,16); (other,16); (word_sub sp (word 64),64)]
         [(word pc,libsnappy_size)] /\
        ALL (nonoverlapping (word_sub sp (word 64),64)) [(cc,16); (other,16)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_operator_assign) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_ARGUMENTS [cc; other] s /\
                  read (memory :> bytes64 cc) s = word 0 /\
                  read (memory :> bytes64 other) s = wm /\
                  read (memory :> bytes8 (word_add other (word 8))) s = b /\
                  read events s = e)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_RETURN s = cc /\
                  read (memory :> bytes64 cc) s = wm /\
                  read (memory :> bytes8 (word_add cc (word 8))) s = b /\
                  read (memory :> bytes64 other) s = word 0 /\
                  ?e2. read events s = APPEND e2 e /\
                       memaccess_inset e2
                        (memrange(cc,16) UNION memrange(other,16) UNION
                         memrange(word_sub sp (word 64),64))
                        (memrange(cc,16) UNION memrange(other,16) UNION
                         memrange(word_sub sp (word 64),64)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 64),32)] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
              MAYCHANGE [memory :> bytes(cc,16)] ,,
              MAYCHANGE [memory :> bytes(other,8)])`;;

let SNAPPY_COMPRESSION_CONTEXT_OPERATOR_ASSIGN_NULL_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_OPERATOR_ASSIGN_NULL_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

let SNAPPY_COMPRESSION_CONTEXT_OPERATOR_ASSIGN_NULL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!cc other wm b pc sp returnaddress x19 x20 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\ ~(cc = other) /\
        nonoverlapping (cc,16) (other,16) /\
        ALLPAIRS nonoverlapping
         [(cc,16); (other,16); (word_sub sp (word 64),64)]
         [(word pc,libsnappy_size)] /\
        ALL (nonoverlapping (word_sub sp (word 64),64)) [(cc,16); (other,16)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_operator_assign) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_ARGUMENTS [cc; other] s /\
                  read (memory :> bytes64 cc) s = word 0 /\
                  read (memory :> bytes64 other) s = wm /\
                  read (memory :> bytes8 (word_add other (word 8))) s = b)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_RETURN s = cc /\
                  read (memory :> bytes64 cc) s = wm /\
                  read (memory :> bytes8 (word_add cc (word 8))) s = b /\
                  read (memory :> bytes64 other) s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 64),32)] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
              MAYCHANGE [memory :> bytes(cc,16)] ,,
              MAYCHANGE [memory :> bytes(other,8)])`;;

let SNAPPY_COMPRESSION_CONTEXT_OPERATOR_ASSIGN_NULL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_OPERATOR_ASSIGN_NULL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

