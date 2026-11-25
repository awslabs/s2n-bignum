(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::internal::WorkingMemory::~WorkingMemory(): if owns_mem_, it frees *)
(* mem_ with operator delete(void* ) (std::allocator<char>::deallocate),     *)
(* reached through the PLT by a tail call; otherwise it does nothing.        *)
(*                                                                           *)
(*  - OWNED: the object at wm has owns_mem_ = true and mem_ = mem, a live    *)
(*    block (mem,m) of the heap H (as WorkingMemory(size_t) leaves it, with  *)
(*    m = RequiredSize): the heap after is heap_remove mem H, the block is   *)
(*    freed and nothing leaks. Its theorem is about any allocator that meets *)
(*    the model of arm/proofs/heap.ml at the addresses imp "_Znwm" and       *)
(*    imp "_ZdlPv" that the loader puts in the GOT; operator delete may use  *)
(*    stk <= 1024 bytes of stack below SP.                                   *)
(*                                                                           *)
(*  - BORROWED: owns_mem_ = false (WorkingMemory(size_t, char* )): it reads  *)
(*    the flag and returns; no heap.                                         *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/snappy/objects.ml";;

(*** The code in the image (see the listing in layout.ml):

    WorkingMemory_dtor:
     +0x0  ldrb    w1, [x0, #16]          owns_mem_
     +0x4  cbnz    w1, +0xc
     +0x8  ret
     +0xc  ldr     x0, [x0]               mem_
    +0x10  b       operator_delete        through the PLT
 ***)

let SNAPPY_WORKING_MEMORY_DTOR_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "WorkingMemory_dtor"; layout_range "plt_operator_delete"];;

(* ------------------------------------------------------------------------- *)
(* The owning object: correctness and memory safety together (the contract  *)
(* of delete has both). The accesses are within the allocator's footprint,  *)
(* the freed block, the stack below SP, the object and the slots.           *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_WORKING_MEMORY_DTOR_OWNED_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !e wm mem m pc rw H sp returnaddress.
        aligned 4096 (word pc:int64) /\
        pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
        elf_relocated_data (word(pc + libsnappy_rw)) rw
          (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
        MEM (mem,m) H /\ stk <= 1024 /\
        DISJOINT (memrange(word pc,libsnappy_rw + libsnappy_rw_size))
                 (heap_fp H) /\
        DISJOINT (memrange(word_sub sp (word 1024),1024))
                 (heap_fp H UNION memrange(mem,m))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + WorkingMemory_dtor) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  C_ARGUMENTS [wm] s /\
                  read (memory :> bytes64 wm) s = mem /\
                  read (memory :> bytes8 (word_add wm (word 16))) s = word 1 /\
                  read (memory :> bytes(word(pc + libsnappy_rw),
                                        libsnappy_rw_size)) s = rw /\
                  read events s = e /\
                  heap_ok H (read (memory :> footprint (heap_fp H)) s))
             (\s. read PC s = returnaddress /\
                  heap_fp (heap_remove mem H) SUBSET
                  heap_fp H UNION memrange(mem,m) /\
                  heap_ok (heap_remove mem H)
                    (read (memory :> footprint (heap_fp (heap_remove mem H)))
                          s) /\
                  ?e2. read events s = APPEND e2 e /\
                       memaccess_inset e2
                        (heap_fp H UNION memrange(mem,m) UNION
                         memrange(word_sub sp (word 1024),1024) UNION
                         memrange(wm,48) UNION
                         memrange(word(pc + libsnappy_rw),libsnappy_rw_size))
                        (heap_fp H UNION memrange(mem,m) UNION
                         memrange(word_sub sp (word 1024),1024)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 1024),1024)] ,,
              MAYCHANGE [memory :> footprint (heap_fp H)] ,,
              MAYCHANGE [memory :> bytes(mem,m)])`;;

let SNAPPY_WORKING_MEMORY_DTOR_OWNED_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_WORKING_MEMORY_DTOR_OWNED_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* Correctness alone, from the above.                                         *)

let SNAPPY_WORKING_MEMORY_DTOR_OWNED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !wm mem m pc rw H sp returnaddress.
        aligned 4096 (word pc:int64) /\
        pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
        elf_relocated_data (word(pc + libsnappy_rw)) rw
          (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
        MEM (mem,m) H /\ stk <= 1024 /\
        DISJOINT (memrange(word pc,libsnappy_rw + libsnappy_rw_size))
                 (heap_fp H) /\
        DISJOINT (memrange(word_sub sp (word 1024),1024))
                 (heap_fp H UNION memrange(mem,m))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + WorkingMemory_dtor) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  C_ARGUMENTS [wm] s /\
                  read (memory :> bytes64 wm) s = mem /\
                  read (memory :> bytes8 (word_add wm (word 16))) s = word 1 /\
                  read (memory :> bytes(word(pc + libsnappy_rw),
                                        libsnappy_rw_size)) s = rw /\
                  heap_ok H (read (memory :> footprint (heap_fp H)) s))
             (\s. read PC s = returnaddress /\
                  heap_fp (heap_remove mem H) SUBSET
                  heap_fp H UNION memrange(mem,m) /\
                  heap_ok (heap_remove mem H)
                    (read (memory :> footprint (heap_fp (heap_remove mem H)))
                          s))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 1024),1024)] ,,
              MAYCHANGE [memory :> footprint (heap_fp H)] ,,
              MAYCHANGE [memory :> bytes(mem,m)])`;;

let SNAPPY_WORKING_MEMORY_DTOR_OWNED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_WORKING_MEMORY_DTOR_OWNED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The object that does not own its memory.                                  *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_WORKING_MEMORY_DTOR_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!wm pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + WorkingMemory_dtor) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [wm] s /\
                  read (memory :> bytes8 (word_add wm (word 16))) s = word 0)
             (\s. read PC s = returnaddress)
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`;;

let SNAPPY_WORKING_MEMORY_DTOR_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_WORKING_MEMORY_DTOR_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

let SNAPPY_WORKING_MEMORY_DTOR_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e wm pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + WorkingMemory_dtor) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [wm] s /\
                  read (memory :> bytes8 (word_add wm (word 16))) s = word 0 /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  ?e2. read events s = APPEND e2 e /\
                       memaccess_inset e2 (memrange(wm,48)) {})
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`;;

let SNAPPY_WORKING_MEMORY_DTOR_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_WORKING_MEMORY_DTOR_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
