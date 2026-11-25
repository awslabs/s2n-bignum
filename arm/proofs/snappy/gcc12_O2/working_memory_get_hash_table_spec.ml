(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::internal::WorkingMemory::GetHashTable(size_t fragment_size,       *)
(* int* table_size) const: it clears the hash table of the object at this,   *)
(* the 2 * h bytes at table_ = t for h = CalculateTableSize(fragment_size),  *)
(* by memset through the PLT, stores h at table_size and returns t.          *)
(* CalculateTableSize takes a uint32_t, so h is snappy_table_size of the     *)
(* fragment size modulo 2^32 (the compressor's fragments are at most 65536   *)
(* bytes). Only table_ of the object is read.                                *)
(*                                                                           *)
(* The contract of memset (arm/proofs/libc.ml) is for the function at        *)
(* imp "memset", the address in its GOT slot, with its code and data in the  *)
(* region (ea,el) that holds ev; the table and the result must be outside    *)
(* it and outside the library. The frame is 48 bytes (X19-X21, X29, X30).   *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/working_memory_required_size_spec.ml";;
needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/snappy/objects.ml";;

(*** The code in the image (see the listing in layout.ml):

    WorkingMemory_GetHashTable:
     +0x0  stp     x29, x30, [sp, #-48]!
     +0x4  mov     x29, sp
     +0x8  stp     x19, x20, [sp, #16]
     +0xc  mov     x19, x0                    this
    +0x10  mov     x20, x2                    table_size
    +0x14  str     x21, [sp, #32]
    +0x18  cmp     w1, #0x8, lsl #12          (uint32_t) fragment_size > 32768
    +0x1c  b.hi    +0x68
    +0x20  cmp     w1, #0xff                  <= 255
    +0x24  b.ls    +0x74
    +0x28  sub     w1, w1, #0x1
    +0x2c  mov     w21, #0x2
    +0x30  clz     w1, w1
    +0x34  eor     w1, w1, #0x1f
    +0x38  lsl     w2, w21, w1
    +0x3c  lsl     x2, x2, #1                 bytes of the table
    +0x40  lsl     w21, w21, w1               entries
  join1:
    +0x44  ldr     x0, [x19, #24]             table_
    +0x48  mov     w1, #0x0
    +0x4c  bl      memset                     through the PLT
    +0x50  ldr     x0, [x19, #24]
    +0x54  str     w21, [x20]
    +0x58  ldp     x19, x20, [sp, #16]
    +0x5c  ldr     x21, [sp, #32]
    +0x60  ldp     x29, x30, [sp], #48
    +0x64  ret
    +0x68  mov     w21, #0x8000
    +0x6c  mov     x2, #0x10000
    +0x70  b       join1
    +0x74  mov     w21, #0x100
    +0x78  mov     x2, #0x200
    +0x7c  b       join1
 ***)

let SNAPPY_WORKING_MEMORY_GET_HASH_TABLE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "WorkingMemory_GetHashTable"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety.                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_WORKING_MEMORY_GET_HASH_TABLE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e this n tsp t pc rw sp returnaddress x19 x20 x21 x29 ea el ev.
     memset_correct_safe_contract (imp "memset") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     ALLPAIRS nonoverlapping
      [(t,2 * snappy_table_size (val n MOD 2 EXP 32)); (tsp,4);
       (word_sub sp (word 48),48)]
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el)] /\
     ALL (nonoverlapping (t,2 * snappy_table_size (val n MOD 2 EXP 32)))
      [(this,48); (tsp,4); (word_sub sp (word 48),48)] /\
     ALL (nonoverlapping (word_sub sp (word 48),48)) [(this,48); (tsp,4)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + WorkingMemory_GetHashTable) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X29 s = x29 /\
           C_ARGUMENTS [this; n; tsp] s /\
           read (memory :> bytes64 (word_add this (word 24))) s = t /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\
           read (memory :> bytes(ea,el)) s = ev /\
           read events s = e)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X29 s = x29 /\
           C_RETURN s = t /\
           read (memory :> bytes(t,2 * snappy_table_size (val n MOD 2 EXP 32))) s = 0 /\
           read (memory :> bytes32 tsp) s = word(snappy_table_size (val n MOD 2 EXP 32)) /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2
                 (memrange(this,48) UNION memrange(word_sub sp (word 48),48) UNION
                  memrange(t,2 * snappy_table_size (val n MOD 2 EXP 32)) UNION
                  memrange(word(pc + libsnappy_rw),libsnappy_rw_size) UNION
                  memrange(ea,el))
                 (memrange(word_sub sp (word 48),48) UNION
                  memrange(t,2 * snappy_table_size (val n MOD 2 EXP 32)) UNION
                  memrange(tsp,4)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 48),48)] ,,
       MAYCHANGE [memory :> bytes(t,2 * snappy_table_size (val n MOD 2 EXP 32))] ,,
       MAYCHANGE [memory :> bytes(tsp,4)])`;;

let SNAPPY_WORKING_MEMORY_GET_HASH_TABLE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_WORKING_MEMORY_GET_HASH_TABLE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness alone.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_WORKING_MEMORY_GET_HASH_TABLE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!this n tsp t pc rw sp returnaddress x19 x20 x21 x29 ea el ev.
     memset_correct_safe_contract (imp "memset") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     ALLPAIRS nonoverlapping
      [(t,2 * snappy_table_size (val n MOD 2 EXP 32)); (tsp,4);
       (word_sub sp (word 48),48)]
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el)] /\
     ALL (nonoverlapping (t,2 * snappy_table_size (val n MOD 2 EXP 32)))
      [(this,48); (tsp,4); (word_sub sp (word 48),48)] /\
     ALL (nonoverlapping (word_sub sp (word 48),48)) [(this,48); (tsp,4)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + WorkingMemory_GetHashTable) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X29 s = x29 /\
           C_ARGUMENTS [this; n; tsp] s /\
           read (memory :> bytes64 (word_add this (word 24))) s = t /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\
           read (memory :> bytes(ea,el)) s = ev)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X29 s = x29 /\
           C_RETURN s = t /\
           read (memory :> bytes(t,2 * snappy_table_size (val n MOD 2 EXP 32))) s = 0 /\
           read (memory :> bytes32 tsp) s = word(snappy_table_size (val n MOD 2 EXP 32)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 48),48)] ,,
       MAYCHANGE [memory :> bytes(t,2 * snappy_table_size (val n MOD 2 EXP 32))] ,,
       MAYCHANGE [memory :> bytes(tsp,4)])`;;

let SNAPPY_WORKING_MEMORY_GET_HASH_TABLE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_WORKING_MEMORY_GET_HASH_TABLE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
