(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::internal::WorkingMemory::WorkingMemory(size_t input_size,         *)
(* char* buffer), the constructor that lays out the scratch memory of the    *)
(* compressor in a buffer of the caller and does not own it: in the object   *)
(* at wm (48 bytes, see arm/proofs/snappy/objects.ml) it stores mem_ =       *)
(* buffer, size_ = RequiredSize(input_size), owns_mem_ = false and the       *)
(* pointers table_, input_ and output_ into the buffer, i.e.                 *)
(* snappy_working_memory wm buffer n F. It writes nothing else but its frame *)
(* (48 bytes, for X19-X21, X29 and X30) and that of RequiredSize below it,   *)
(* and it touches no heap. The buffer itself is not accessed. gcc 12 -O2     *)
(* inlines CalculateTableSize and calls RequiredSize, so this is proved      *)
(* relative to its contract.                                                 *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/working_memory_required_size_spec.ml";;
needs "arm/proofs/snappy/objects.ml";;

(*** The code in the image (see the listing in layout.ml):

    WorkingMemory_ctor__ulong_charp:
     +0x0  stp     x29, x30, [sp, #-48]!
     +0x4  mov     x29, sp
     +0x8  stp     x19, x20, [sp, #16]
     +0xc  mov     x19, x0                    this
    +0x10  mov     x0, x1                     input_size
    +0x14  str     x21, [sp, #32]
    +0x18  cmp     x1, #0x10, lsl #12
    +0x1c  b.hi    +0x80                      n > 65536
    +0x20  cmp     x1, #0x8, lsl #12
    +0x24  b.hi    +0x98                      n > 32768
    +0x28  cmp     w1, #0xff
    +0x2c  b.ls    +0x8c                      n <= 255
    +0x30  sub     w1, w1, #0x1
    +0x34  mov     w20, #0x2
    +0x38  clz     w1, w1
    +0x3c  mov     x21, x0
    +0x40  eor     w1, w1, #0x1f
    +0x44  lsl     w20, w20, w1               table size
    +0x48  lsl     x20, x20, #1               its bytes
  join1:
    +0x4c  str     x2, [x19]                  mem_
    +0x50  bl      WorkingMemory_RequiredSize
    +0x54  str     x0, [x19, #8]              size_
    +0x58  ldr     x1, [x19]
    +0x5c  strb    wzr, [x19, #16]            owns_mem_
    +0x60  str     x1, [x19, #24]             table_
    +0x64  add     x0, x1, x20
    +0x68  add     x21, x0, x21
    +0x6c  stp     x0, x21, [x19, #32]        input_, output_
    +0x70  ldp     x19, x20, [sp, #16]
    +0x74  ldr     x21, [sp, #32]
    +0x78  ldp     x29, x30, [sp], #48
    +0x7c  ret
    +0x80  mov     x20, #0x10000
    +0x84  mov     x21, x20
    +0x88  b       join1
    +0x8c  mov     x21, x1
    +0x90  mov     x20, #0x200
    +0x94  b       join1
    +0x98  mov     x21, x1
    +0x9c  mov     x20, #0x10000
    +0xa0  b       join1
 ***)

let SNAPPY_WORKING_MEMORY_CTOR_ULONG_CHARP_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "WorkingMemory_ctor__ulong_charp"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_WORKING_MEMORY_CTOR_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!wm n buffer pc sp returnaddress x19 x20 x21 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\
        ALLPAIRS nonoverlapping [(wm,48); (word_sub sp (word 80),80)]
                                [(word pc,libsnappy_size)] /\
        nonoverlapping (wm,48) (word_sub sp (word 80),80)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + WorkingMemory_ctor__ulong_charp) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
                  read X29 s = x29 /\
                  C_ARGUMENTS [wm; n; buffer] s)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
                  read X29 s = x29 /\
                  snappy_working_memory wm buffer (val n) F s)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X21; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 80),32)] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 48),48)] ,,
              MAYCHANGE [memory :> bytes(wm,48)])`;;

let SNAPPY_WORKING_MEMORY_CTOR_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_WORKING_MEMORY_CTOR_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety: the accesses are the object and the stack. *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_WORKING_MEMORY_CTOR_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!e wm n buffer pc sp returnaddress x19 x20 x21 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\
        ALLPAIRS nonoverlapping [(wm,48); (word_sub sp (word 80),80)]
                                [(word pc,libsnappy_size)] /\
        nonoverlapping (wm,48) (word_sub sp (word 80),80)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + WorkingMemory_ctor__ulong_charp) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
                  read X29 s = x29 /\
                  C_ARGUMENTS [wm; n; buffer] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
                  read X29 s = x29 /\
                  snappy_working_memory wm buffer (val n) F s /\
                  ?e2. read events s = APPEND e2 e /\
                       memaccess_inset e2
                        (memrange(wm,48) UNION
                         memrange(word_sub sp (word 80),80))
                        (memrange(wm,48) UNION
                         memrange(word_sub sp (word 80),80)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X21; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 80),32)] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 48),48)] ,,
              MAYCHANGE [memory :> bytes(wm,48)])`;;

let SNAPPY_WORKING_MEMORY_CTOR_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_WORKING_MEMORY_CTOR_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
