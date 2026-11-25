(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::CompressionContext::Reset(), which frees what the context owns    *)
(* and makes it empty (working_memory_ = nullptr), in its three cases:       *)
(*                                                                           *)
(*  - OWNED (made by CompressionContext()): the context at cc owns the       *)
(*    WorkingMemory at wm, a live block (wm,48), which owns its memory mem,  *)
(*    a live block (mem,m): delete wm runs ~WorkingMemory, which frees mem,  *)
(*    and then frees wm, so the heap after is                                *)
(*    heap_remove wm (heap_remove mem H): both blocks freed, no leak. With   *)
(*    H = (mem,m) :: (wm,48) :: H0 as CompressionContext() leaves it, that   *)
(*    is H0 (HEAP_REMOVE_CONS).                                              *)
(*  - BORROWED (made by CompressionContext(void*, size_t)): the WorkingMemory *)
(*    does not own its memory and the context does not own it: only the     *)
(*    destructor runs, which does nothing; no heap.                          *)
(*  - NULL: working_memory_ is nullptr (after Reset or a move); nothing.     *)
(*                                                                           *)
(* In the OWNED case the frame of the allocator is the footprint of H and    *)
(* the two blocks, heap_fp H UNION memrange(mem,m) UNION memrange(wm,48),    *)
(* which also holds the new footprint; the code reads the GOT slot of        *)
(* _ZdlPv, and calls ~WorkingMemory below its frame of 32 bytes (1024 bytes  *)
(* of stack for operator delete, stk <= 1024).                               *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/working_memory_dtor_spec.ml";;
needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/snappy/objects.ml";;

(*** The code in the image (see the listing in layout.ml):

    CompressionContext_Reset:
     +0x0  stp     x29, x30, [sp, #-32]!
     +0x4  mov     x29, sp
     +0x8  stp     x19, x20, [sp, #16]
     +0xc  ldr     x20, [x0]                  working_memory_
    +0x10  cbz     x20, join1                 NULL
    +0x14  mov     x19, x0
    +0x18  ldrb    w0, [x0, #8]               owns_working_memory_
    +0x1c  cbz     w0, +0x40                  BORROWED
    +0x20  mov     x0, x20
    +0x24  bl      WorkingMemory_dtor         OWNED: delete working_memory_
    +0x28  mov     x0, x20
    +0x2c  bl      operator_delete            through the PLT
    +0x30  str     xzr, [x19]
  join1:
    +0x34  ldp     x19, x20, [sp, #16]
    +0x38  ldp     x29, x30, [sp], #32
    +0x3c  ret
    +0x40  mov     x0, x20
    +0x44  bl      WorkingMemory_dtor         working_memory_->~WorkingMemory()
    +0x48  str     xzr, [x19]
    +0x4c  b       join1
 ***)

let SNAPPY_COMPRESSION_CONTEXT_RESET_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "CompressionContext_Reset"; layout_range "plt_operator_delete"];;

(* ------------------------------------------------------------------------- *)
(* The owning context.                                                       *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_COMPRESSION_CONTEXT_RESET_OWNED_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !e cc wm mem m pc rw H sp returnaddress x19 x20 x29.
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     MEM (wm,48) H /\ MEM (mem,m) H /\ ~(wm = mem) /\ stk <= 1024 /\
     DISJOINT (memrange(word pc,libsnappy_rw + libsnappy_rw_size))
              (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48)) /\
     DISJOINT (memrange(word_sub sp (word 1056),1056))
              (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48)) /\
     DISJOINT (memrange(cc,16))
              (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48)) /\
     ALLPAIRS nonoverlapping [(cc,16); (word_sub sp (word 1056),1056)]
                             [(word pc,libsnappy_rw + libsnappy_rw_size)] /\
     nonoverlapping (cc,16) (word_sub sp (word 1056),1056)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + CompressionContext_Reset) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
           C_ARGUMENTS [cc] s /\
           read (memory :> bytes64 cc) s = wm /\
           read (memory :> bytes8 (word_add cc (word 8))) s = word 1 /\
           read (memory :> bytes64 wm) s = mem /\
           read (memory :> bytes8 (word_add wm (word 16))) s = word 1 /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\
           read events s = e /\
           heap_ok H (read (memory :> footprint (heap_fp H)) s))
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
           read (memory :> bytes64 cc) s = word 0 /\
           heap_fp (heap_remove wm (heap_remove mem H)) SUBSET
           heap_fp H UNION memrange(mem,m) UNION memrange(wm,48) /\
           heap_ok (heap_remove wm (heap_remove mem H))
             (read (memory :> footprint
                     (heap_fp (heap_remove wm (heap_remove mem H)))) s) /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2
                 (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48) UNION
                  memrange(word_sub sp (word 1056),1056) UNION memrange(cc,16) UNION
                  memrange(word(pc + libsnappy_rw),libsnappy_rw_size))
                 (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48) UNION
                  memrange(word_sub sp (word 1056),1056) UNION memrange(cc,16)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 1056),1024)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
       MAYCHANGE [memory :> bytes(cc,8)] ,,
       MAYCHANGE [memory :> footprint
                   (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48))])`;;

let SNAPPY_COMPRESSION_CONTEXT_RESET_OWNED_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_RESET_OWNED_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

let SNAPPY_COMPRESSION_CONTEXT_RESET_OWNED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !cc wm mem m pc rw H sp returnaddress x19 x20 x29.
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     MEM (wm,48) H /\ MEM (mem,m) H /\ ~(wm = mem) /\ stk <= 1024 /\
     DISJOINT (memrange(word pc,libsnappy_rw + libsnappy_rw_size))
              (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48)) /\
     DISJOINT (memrange(word_sub sp (word 1056),1056))
              (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48)) /\
     DISJOINT (memrange(cc,16))
              (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48)) /\
     ALLPAIRS nonoverlapping [(cc,16); (word_sub sp (word 1056),1056)]
                             [(word pc,libsnappy_rw + libsnappy_rw_size)] /\
     nonoverlapping (cc,16) (word_sub sp (word 1056),1056)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + CompressionContext_Reset) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
           C_ARGUMENTS [cc] s /\
           read (memory :> bytes64 cc) s = wm /\
           read (memory :> bytes8 (word_add cc (word 8))) s = word 1 /\
           read (memory :> bytes64 wm) s = mem /\
           read (memory :> bytes8 (word_add wm (word 16))) s = word 1 /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\
           heap_ok H (read (memory :> footprint (heap_fp H)) s))
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
           read (memory :> bytes64 cc) s = word 0 /\
           heap_fp (heap_remove wm (heap_remove mem H)) SUBSET
           heap_fp H UNION memrange(mem,m) UNION memrange(wm,48) /\
           heap_ok (heap_remove wm (heap_remove mem H))
             (read (memory :> footprint
                     (heap_fp (heap_remove wm (heap_remove mem H)))) s))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 1056),1024)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
       MAYCHANGE [memory :> bytes(cc,8)] ,,
       MAYCHANGE [memory :> footprint
                   (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48))])`;;

let SNAPPY_COMPRESSION_CONTEXT_RESET_OWNED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_RESET_OWNED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The context on a workspace of the caller.                                 *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_COMPRESSION_CONTEXT_RESET_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e cc wm pc sp returnaddress x19 x20 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\ ~(wm = word 0) /\
        ALLPAIRS nonoverlapping [(cc,16); (wm,48); (word_sub sp (word 32),32)]
                                [(word pc,libsnappy_size)] /\
        ALL (nonoverlapping (word_sub sp (word 32),32)) [(cc,16); (wm,48)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_Reset) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_ARGUMENTS [cc] s /\
                  read (memory :> bytes64 cc) s = wm /\
                  read (memory :> bytes8 (word_add cc (word 8))) s = word 0 /\
                  read (memory :> bytes8 (word_add wm (word 16))) s = word 0 /\
                  read events s = e)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  read (memory :> bytes64 cc) s = word 0 /\
                  ?e2. read events s = APPEND e2 e /\
                       memaccess_inset e2
                        (memrange(cc,16) UNION memrange(wm,48) UNION
                         memrange(word_sub sp (word 32),32))
                        (memrange(cc,16) UNION memrange(word_sub sp (word 32),32)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
              MAYCHANGE [memory :> bytes(cc,8)])`;;

let SNAPPY_COMPRESSION_CONTEXT_RESET_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_RESET_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

let SNAPPY_COMPRESSION_CONTEXT_RESET_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!cc wm pc sp returnaddress x19 x20 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\ ~(wm = word 0) /\
        ALLPAIRS nonoverlapping [(cc,16); (wm,48); (word_sub sp (word 32),32)]
                                [(word pc,libsnappy_size)] /\
        ALL (nonoverlapping (word_sub sp (word 32),32)) [(cc,16); (wm,48)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_Reset) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_ARGUMENTS [cc] s /\
                  read (memory :> bytes64 cc) s = wm /\
                  read (memory :> bytes8 (word_add cc (word 8))) s = word 0 /\
                  read (memory :> bytes8 (word_add wm (word 16))) s = word 0 /\
                  read events s = e)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  read (memory :> bytes64 cc) s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
              MAYCHANGE [memory :> bytes(cc,8)])`;;

let SNAPPY_COMPRESSION_CONTEXT_RESET_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_RESET_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The empty context.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_COMPRESSION_CONTEXT_RESET_NULL_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e cc pc sp returnaddress x19 x20 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\
        ALLPAIRS nonoverlapping [(cc,16); (word_sub sp (word 32),32)]
                                [(word pc,libsnappy_size)] /\
        nonoverlapping (cc,16) (word_sub sp (word 32),32)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_Reset) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_ARGUMENTS [cc] s /\
                  read (memory :> bytes64 cc) s = word 0 /\
                  read events s = e)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  ?e2. read events s = APPEND e2 e /\
                       memaccess_inset e2
                        (memrange(cc,16) UNION memrange(word_sub sp (word 32),32))
                        (memrange(word_sub sp (word 32),32)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)])`;;

let SNAPPY_COMPRESSION_CONTEXT_RESET_NULL_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_RESET_NULL_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

let SNAPPY_COMPRESSION_CONTEXT_RESET_NULL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!cc pc sp returnaddress x19 x20 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\
        ALLPAIRS nonoverlapping [(cc,16); (word_sub sp (word 32),32)]
                                [(word pc,libsnappy_size)] /\
        nonoverlapping (cc,16) (word_sub sp (word 32),32)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_Reset) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_ARGUMENTS [cc] s /\
                  read (memory :> bytes64 cc) s = word 0 /\
                  read events s = e)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)])`;;

let SNAPPY_COMPRESSION_CONTEXT_RESET_NULL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_RESET_NULL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

