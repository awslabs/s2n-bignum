(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::CompressionContext::CompressionContext(void* workspace, size_t    *)
(* workspace_size), the context on a workspace of the caller: the            *)
(* WorkingMemory is constructed in place at ws = workspace, with its memory  *)
(* the rest of the workspace (WorkingMemory(kBlockSize, ws + 48)), and the   *)
(* context at cc points to it and does not own it:                          *)
(* snappy_compression_context cc ws F and snappy_working_memory ws (ws + 48) *)
(* 65536 F (arm/proofs/snappy/objects.ml). No heap. The code does not use   *)
(* workspace_size (the assertion workspace_size >= WorkspaceSize() is       *)
(* compiled out with NDEBUG); the compressor will use the                    *)
(* snappy_working_memory_size 65536 bytes from ws + 48, which the            *)
(* constructor does not access. Its frame is 32 bytes, that of              *)
(* WorkingMemory(size_t, char* ) 80 below it.                                *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/working_memory_ctor_ulong_charp_spec.ml";;

(*** The code in the image (see the listing in layout.ml):

    CompressionContext_ctor__voidp_ulong:
     +0x0  stp     x29, x30, [sp, #-32]!
     +0x4  add     x2, x1, #0x30              ws + sizeof(WorkingMemory)
     +0x8  mov     x29, sp
     +0xc  stp     x19, x20, [sp, #16]
    +0x10  mov     x20, x0                    this
    +0x14  mov     x19, x1                    ws
    +0x18  mov     x0, x1
    +0x1c  mov     x1, #0x10000               kBlockSize
    +0x20  strb    wzr, [x20, #8]             owns_working_memory_ = false
    +0x24  bl      WorkingMemory_ctor__ulong_charp
    +0x28  str     x19, [x20]                 working_memory_ = ws
    +0x2c  ldp     x19, x20, [sp, #16]
    +0x30  ldp     x29, x30, [sp], #32
    +0x34  ret
 ***)

let SNAPPY_COMPRESSION_CONTEXT_CTOR_VOIDP_ULONG_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "CompressionContext_ctor__voidp_ulong"];;

let SNAPPY_COMPRESSION_CONTEXT_CTOR_VOIDP_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e cc ws wsize pc sp returnaddress x19 x20 x21 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\
        ALLPAIRS nonoverlapping [(cc,16); (ws,48); (word_sub sp (word 112),112)]
                                [(word pc,libsnappy_size)] /\
        nonoverlapping (cc,16) (ws,48) /\
        ALL (nonoverlapping (word_sub sp (word 112),112)) [(cc,16); (ws,48)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_ctor__voidp_ulong) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
                  read X29 s = x29 /\
                  C_ARGUMENTS [cc; ws; wsize] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
                  read X29 s = x29 /\
                  snappy_compression_context cc ws F s /\
                  snappy_working_memory ws (word_add ws (word 48)) 65536 F s /\
                  ?e2. read events s = APPEND e2 e /\
                       memaccess_inset e2
                        (memrange(cc,16) UNION memrange(ws,48) UNION
                         memrange(word_sub sp (word 112),112))
                        (memrange(cc,16) UNION memrange(ws,48) UNION
                         memrange(word_sub sp (word 112),112)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X21; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 112),80)] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
              MAYCHANGE [memory :> bytes(cc,16)] ,,
              MAYCHANGE [memory :> bytes(ws,48)])`;;

let SNAPPY_COMPRESSION_CONTEXT_CTOR_VOIDP_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_CTOR_VOIDP_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

let SNAPPY_COMPRESSION_CONTEXT_CTOR_VOIDP_ULONG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!cc ws wsize pc sp returnaddress x19 x20 x21 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\
        ALLPAIRS nonoverlapping [(cc,16); (ws,48); (word_sub sp (word 112),112)]
                                [(word pc,libsnappy_size)] /\
        nonoverlapping (cc,16) (ws,48) /\
        ALL (nonoverlapping (word_sub sp (word 112),112)) [(cc,16); (ws,48)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_ctor__voidp_ulong) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
                  read X29 s = x29 /\
                  C_ARGUMENTS [cc; ws; wsize] s)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
                  read X29 s = x29 /\
                  snappy_compression_context cc ws F s /\
                  snappy_working_memory ws (word_add ws (word 48)) 65536 F s)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X21; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 112),80)] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
              MAYCHANGE [memory :> bytes(cc,16)] ,,
              MAYCHANGE [memory :> bytes(ws,48)])`;;

let SNAPPY_COMPRESSION_CONTEXT_CTOR_VOIDP_ULONG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_CTOR_VOIDP_ULONG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
