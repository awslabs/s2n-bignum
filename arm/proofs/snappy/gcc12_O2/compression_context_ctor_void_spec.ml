(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::CompressionContext::CompressionContext(), the context that owns   *)
(* its scratch memory: it allocates the 48-byte WorkingMemory object wm with *)
(* operator new(size_t) through the PLT, constructs it with                  *)
(* WorkingMemory(kBlockSize), which allocates its memory mem of             *)
(* snappy_working_memory_size 65536 bytes, and stores wm and the flag true   *)
(* in the context at cc. So the heap gets exactly two blocks,               *)
(* (mem, snappy_working_memory_size 65536) in front of (wm, 48) in front of  *)
(* H, and the context is snappy_compression_context cc wm T with             *)
(* snappy_working_memory wm mem 65536 T (arm/proofs/snappy/objects.ml);      *)
(* CompressionContext::Reset (and the destructor) frees both.               *)
(*                                                                           *)
(* The second allocation is made with (wm,48) live at an address that the  *)
(* theorem cannot name, so its room is stated for all addresses, as in       *)
(* arm/heap/heap_demo2.ml. The stack is the 32 bytes of the frame and the    *)
(* 1056 below them for WorkingMemory(size_t) and operator new (stk <= 1024). *)
(* Correctness and memory safety together, as the contracts of the heap.    *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/working_memory_ctor_ulong_spec.ml";;
needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/snappy/objects.ml";;

(*** The code in the image (see the listing in layout.ml):

    CompressionContext_ctor__void:
     +0x0  stp     x29, x30, [sp, #-32]!
     +0x4  mov     x29, sp
     +0x8  stp     x19, x20, [sp, #16]
     +0xc  mov     x19, x0                    this
    +0x10  mov     x0, #0x30                  sizeof(WorkingMemory)
    +0x14  bl      operator_new               through the PLT
    +0x18  mov     x20, x0
    +0x1c  mov     x1, #0x10000               kBlockSize
    +0x20  bl      WorkingMemory_ctor__ulong
    +0x24  mov     w0, #0x1
    +0x28  str     x20, [x19]                 working_memory_
    +0x2c  strb    w0, [x19, #8]              owns_working_memory_ = true
    +0x30  ldp     x19, x20, [sp, #16]
    +0x34  ldp     x29, x30, [sp], #32
    +0x38  ret
 ***)

let SNAPPY_COMPRESSION_CONTEXT_CTOR_VOID_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "CompressionContext_ctor__void"; layout_range "plt_operator_new"];;

let SNAPPY_COMPRESSION_CONTEXT_CTOR_VOID_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !e cc pc rw H sp returnaddress x19 x20 x21 x29.
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     heap_room H 48 /\
     (!p. heap_room (CONS (p,48) H) (snappy_working_memory_size 65536)) /\
     stk <= 1024 /\
     DISJOINT (memrange(word pc,libsnappy_rw + libsnappy_rw_size)) (heap_fp H) /\
     DISJOINT (memrange(word_sub sp (word 1088),1088)) (heap_fp H) /\
     DISJOINT (memrange(cc,16)) (heap_fp H) /\
     ALLPAIRS nonoverlapping [(cc,16); (word_sub sp (word 1088),1088)]
                             [(word pc,libsnappy_rw + libsnappy_rw_size)] /\
     nonoverlapping (cc,16) (word_sub sp (word 1088),1088)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + CompressionContext_ctor__void) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X29 s = x29 /\
           C_ARGUMENTS [cc] s /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\
           read events s = e /\
           heap_ok H (read (memory :> footprint (heap_fp H)) s))
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X29 s = x29 /\
           ?wm mem.
               ~(wm = mem) /\
               memrange(wm,48) SUBSET heap_fp H /\
               memrange(mem,snappy_working_memory_size 65536) SUBSET heap_fp H /\
               heap_fp (CONS (mem,snappy_working_memory_size 65536) (CONS (wm,48) H))
                 SUBSET heap_fp H /\
               heap_ok (CONS (mem,snappy_working_memory_size 65536) (CONS (wm,48) H))
                 (read (memory :> footprint
                    (heap_fp (CONS (mem,snappy_working_memory_size 65536)
                                   (CONS (wm,48) H)))) s) /\
               snappy_compression_context cc wm T s /\
               snappy_working_memory wm mem 65536 T s /\
               ?e2. read events s = APPEND e2 e /\
                    memaccess_inset e2
                     (heap_fp H UNION memrange(word_sub sp (word 1088),1088) UNION
                      memrange(cc,16) UNION
                      memrange(word(pc + libsnappy_rw),libsnappy_rw_size))
                     (heap_fp H UNION memrange(word_sub sp (word 1088),1088) UNION
                      memrange(cc,16)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 1088),1056)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
       MAYCHANGE [memory :> bytes(cc,16)] ,,
       MAYCHANGE [memory :> footprint (heap_fp H)])`;;

let SNAPPY_COMPRESSION_CONTEXT_CTOR_VOID_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_CTOR_VOID_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness alone.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_COMPRESSION_CONTEXT_CTOR_VOID_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !cc pc rw H sp returnaddress x19 x20 x21 x29.
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     heap_room H 48 /\
     (!p. heap_room (CONS (p,48) H) (snappy_working_memory_size 65536)) /\
     stk <= 1024 /\
     DISJOINT (memrange(word pc,libsnappy_rw + libsnappy_rw_size)) (heap_fp H) /\
     DISJOINT (memrange(word_sub sp (word 1088),1088)) (heap_fp H) /\
     DISJOINT (memrange(cc,16)) (heap_fp H) /\
     ALLPAIRS nonoverlapping [(cc,16); (word_sub sp (word 1088),1088)]
                             [(word pc,libsnappy_rw + libsnappy_rw_size)] /\
     nonoverlapping (cc,16) (word_sub sp (word 1088),1088)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + CompressionContext_ctor__void) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X29 s = x29 /\
           C_ARGUMENTS [cc] s /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\
           heap_ok H (read (memory :> footprint (heap_fp H)) s))
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X29 s = x29 /\
           ?wm mem.
               ~(wm = mem) /\
               memrange(wm,48) SUBSET heap_fp H /\
               memrange(mem,snappy_working_memory_size 65536) SUBSET heap_fp H /\
               heap_fp (CONS (mem,snappy_working_memory_size 65536) (CONS (wm,48) H))
                 SUBSET heap_fp H /\
               heap_ok (CONS (mem,snappy_working_memory_size 65536) (CONS (wm,48) H))
                 (read (memory :> footprint
                    (heap_fp (CONS (mem,snappy_working_memory_size 65536)
                                   (CONS (wm,48) H)))) s) /\
               snappy_compression_context cc wm T s /\
               snappy_working_memory wm mem 65536 T s)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 1088),1056)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
       MAYCHANGE [memory :> bytes(cc,16)] ,,
       MAYCHANGE [memory :> footprint (heap_fp H)])`;;

let SNAPPY_COMPRESSION_CONTEXT_CTOR_VOID_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_COMPRESSION_CONTEXT_CTOR_VOID_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
