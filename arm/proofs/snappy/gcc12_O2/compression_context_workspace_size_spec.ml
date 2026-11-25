(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::CompressionContext::WorkspaceSize(), the size of the workspace   *)
(* that CompressionContext(void*, size_t) needs: sizeof(WorkingMemory) +     *)
(* RequiredSize(kBlockSize) = 48 + snappy_working_memory_size 65536. It     *)
(* calls RequiredSize below a frame of 16 bytes.                             *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/working_memory_required_size_spec.ml";;

(*** The code in the image (see the listing in layout.ml):

    CompressionContext_WorkspaceSize:
     +0x0  stp     x29, x30, [sp, #-16]!
     +0x4  mov     x0, #0x10000
     +0x8  mov     x29, sp
     +0xc  bl      WorkingMemory_RequiredSize
    +0x10  add     x0, x0, #0x30
    +0x14  ldp     x29, x30, [sp], #16
    +0x18  ret
 ***)

let SNAPPY_COMPRESSION_CONTEXT_WORKSPACE_SIZE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "CompressionContext_WorkspaceSize"];;

let SNAPPY_COMPRESSION_CONTEXT_WORKSPACE_SIZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e pc sp returnaddress x19 x20 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\
        nonoverlapping (word pc,libsnappy_size) (word_sub sp (word 48),48)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_WorkspaceSize) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  read events s = e)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_RETURN s = word(48 + snappy_working_memory_size 65536) /\
                  ?e2. read events s = APPEND e2 e /\
                       memaccess_inset e2
                        (memrange(word_sub sp (word 48),48))
                        (memrange(word_sub sp (word 48),48)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 48),32)] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 16),16)])`;;

let SNAPPY_COMPRESSION_CONTEXT_WORKSPACE_SIZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_WORKSPACE_SIZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

let SNAPPY_COMPRESSION_CONTEXT_WORKSPACE_SIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!pc sp returnaddress x19 x20 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\
        nonoverlapping (word pc,libsnappy_size) (word_sub sp (word 48),48)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_WorkspaceSize) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_RETURN s = word(48 + snappy_working_memory_size 65536))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 48),32)] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 16),16)])`;;

let SNAPPY_COMPRESSION_CONTEXT_WORKSPACE_SIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_WORKSPACE_SIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
