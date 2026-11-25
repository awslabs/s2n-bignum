(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::internal::WorkingMemory::WorkingMemory(size_t input_size), the    *)
(* constructor that allocates the scratch memory of the compressor: it calls *)
(* RequiredSize(n), allocates that many bytes with operator new(size_t)      *)
(* through the PLT (std::allocator<char>::allocate), lays out the object at  *)
(* wm with WorkingMemory(n, mem) and sets owns_mem_. So the heap gets        *)
(* exactly one block (mem, RequiredSize(n)) in front of H, and the object is *)
(* snappy_working_memory wm mem n T (arm/proofs/snappy/objects.ml).          *)
(*                                                                           *)
(* allocate checks the size against PTRDIFF_MAX and calls                    *)
(* std::__throw_bad_alloc otherwise (the tbnz below). RequiredSize(n) is at  *)
(* most 207562 (SNAPPY_WORKING_MEMORY_SIZE_BOUND), so that call is never     *)
(* reached, for any n; the failure of operator new itself (bad_alloc) is     *)
(* excluded by heap_room (decision D3 of arm/snappy/README.md).              *)
(*                                                                           *)
(* The theorem is about any allocator that meets the model of                *)
(* arm/proofs/heap.ml at imp "_Znwm" and imp "_ZdlPv", the addresses in the *)
(* GOT, with stk <= 1024 bytes of stack. The footprint heap_fp H of the      *)
(* allocator is outside the library (image, gap and writable segment), the  *)
(* object and the stack (the 32 bytes of the frame and the 1024 below them  *)
(* for the callees: RequiredSize, operator new and WorkingMemory(n, mem)).   *)
(* The postcondition has the facts of the contract of new about the block.   *)
(* Correctness and memory safety together, as in the contract of new.        *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/working_memory_ctor_ulong_charp_spec.ml";;
needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/snappy/objects.ml";;

(*** The code in the image (see the listing in layout.ml):

    WorkingMemory_ctor__ulong:
     +0x0  stp     x29, x30, [sp, #-32]!
     +0x4  mov     x29, sp
     +0x8  stp     x19, x20, [sp, #16]
     +0xc  mov     x20, x0                            this
    +0x10  mov     x19, x1                            input_size
    +0x14  mov     x0, x1
    +0x18  bl      WorkingMemory_RequiredSize
    +0x1c  tbnz    x0, #63, +0x48                     > PTRDIFF_MAX
    +0x20  bl      operator_new                       through the PLT
    +0x24  mov     x2, x0
    +0x28  mov     x1, x19
    +0x2c  mov     x0, x20
    +0x30  bl      WorkingMemory_ctor__ulong_charp
    +0x34  mov     w0, #0x1
    +0x38  strb    w0, [x20, #16]                     owns_mem_ = true
    +0x3c  ldp     x19, x20, [sp, #16]
    +0x40  ldp     x29, x30, [sp], #32
    +0x44  ret
    +0x48  bl      throw_bad_alloc                    (not reached)
 ***)

let SNAPPY_WORKING_MEMORY_CTOR_ULONG_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "WorkingMemory_ctor__ulong"; layout_range "plt_operator_new"];;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety.                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_WORKING_MEMORY_CTOR_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !e wm n pc rw H sp returnaddress x19 x20 x21 x29.
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     heap_room H (snappy_working_memory_size (val n)) /\ stk <= 1024 /\
     DISJOINT (memrange(word pc,libsnappy_rw + libsnappy_rw_size)) (heap_fp H) /\
     DISJOINT (memrange(word_sub sp (word 1056),1056)) (heap_fp H) /\
     DISJOINT (memrange(wm,48)) (heap_fp H) /\
     ALLPAIRS nonoverlapping [(wm,48); (word_sub sp (word 1056),1056)]
                             [(word pc,libsnappy_rw + libsnappy_rw_size)] /\
     nonoverlapping (wm,48) (word_sub sp (word 1056),1056)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + WorkingMemory_ctor__ulong) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X29 s = x29 /\
           C_ARGUMENTS [wm; n] s /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\
           read events s = e /\
           heap_ok H (read (memory :> footprint (heap_fp H)) s))
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X29 s = x29 /\
           ?p. ~(p = word 0) /\ aligned 16 p /\
               val p + snappy_working_memory_size (val n) < 2 EXP 64 /\
               ~MEM p (MAP FST H) /\
               memrange(p,snappy_working_memory_size (val n)) SUBSET heap_fp H /\
               heap_fp (CONS (p,snappy_working_memory_size (val n)) H) SUBSET heap_fp H /\
               heap_ok (CONS (p,snappy_working_memory_size (val n)) H)
                 (read (memory :> footprint
                     (heap_fp (CONS (p,snappy_working_memory_size (val n)) H))) s) /\
               snappy_working_memory wm p (val n) T s /\
               ?e2. read events s = APPEND e2 e /\
                    memaccess_inset e2
                     (heap_fp H UNION memrange(word_sub sp (word 1056),1056) UNION
                      memrange(wm,48) UNION
                      memrange(word(pc + libsnappy_rw),libsnappy_rw_size))
                     (heap_fp H UNION memrange(word_sub sp (word 1056),1056) UNION
                      memrange(wm,48)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 1056),1024)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
       MAYCHANGE [memory :> bytes(wm,48)] ,,
       MAYCHANGE [memory :> footprint (heap_fp H)])`;;

let SNAPPY_WORKING_MEMORY_CTOR_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_WORKING_MEMORY_CTOR_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness alone.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_WORKING_MEMORY_CTOR_ULONG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !wm n pc rw H sp returnaddress x19 x20 x21 x29.
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     heap_room H (snappy_working_memory_size (val n)) /\ stk <= 1024 /\
     DISJOINT (memrange(word pc,libsnappy_rw + libsnappy_rw_size)) (heap_fp H) /\
     DISJOINT (memrange(word_sub sp (word 1056),1056)) (heap_fp H) /\
     DISJOINT (memrange(wm,48)) (heap_fp H) /\
     ALLPAIRS nonoverlapping [(wm,48); (word_sub sp (word 1056),1056)]
                             [(word pc,libsnappy_rw + libsnappy_rw_size)] /\
     nonoverlapping (wm,48) (word_sub sp (word 1056),1056)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + WorkingMemory_ctor__ulong) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X29 s = x29 /\
           C_ARGUMENTS [wm; n] s /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\
           heap_ok H (read (memory :> footprint (heap_fp H)) s))
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X29 s = x29 /\
           ?p. ~(p = word 0) /\ aligned 16 p /\
               val p + snappy_working_memory_size (val n) < 2 EXP 64 /\
               ~MEM p (MAP FST H) /\
               memrange(p,snappy_working_memory_size (val n)) SUBSET heap_fp H /\
               heap_fp (CONS (p,snappy_working_memory_size (val n)) H) SUBSET heap_fp H /\
               heap_ok (CONS (p,snappy_working_memory_size (val n)) H)
                 (read (memory :> footprint
                     (heap_fp (CONS (p,snappy_working_memory_size (val n)) H))) s) /\
               snappy_working_memory wm p (val n) T s)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 1056),1024)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
       MAYCHANGE [memory :> bytes(wm,48)] ,,
       MAYCHANGE [memory :> footprint (heap_fp H)])`;;

let SNAPPY_WORKING_MEMORY_CTOR_ULONG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_WORKING_MEMORY_CTOR_ULONG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
