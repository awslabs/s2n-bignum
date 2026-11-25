(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::MemCopy64<64>(char* dst, const void* src, size_t size), as        *)
(* DecompressBranchless<char*> calls it: memmove(dst, src, 32) through the   *)
(* PLT and, if size > 32, the tail call memmove(dst + 32, src + 32, 32). So  *)
(* it always writes 32 or 64 bytes at dst, whatever size is ("slop" beyond   *)
(* dst + size), and reads 32 or 64 bytes at src.                             *)
(*                                                                           *)
(* For size <= 64 and the first size bytes at src and at dst disjoint (as    *)
(* the source asserts), the first size bytes at dst are those that were at   *)
(* src. The disjointness is what the second memmove needs: it reads the      *)
(* bytes at src + 32 after the first one has written dst..dst+31, and a byte *)
(* src + i (32 <= i < size) in that range would be a byte of both regions.   *)
(* The frame is the 64 bytes at dst in all cases, as two clauses of 32      *)
(* bytes, those of the two calls.                                           *)
(*                                                                           *)
(* The contract of memmove (arm/proofs/libc.ml) is for the function at       *)
(* imp "memmove" with its code and data in (ea,el) holding ev. The frame of *)
(* MemCopy64 itself is 48 bytes (X19-X21, X29, X30).                         *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/utils/compare_branch.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;

(*** The code in the image (see the listing in layout.ml):

    MemCopy64__charp_voidp_ulong:
     +0x0  stp     x29, x30, [sp, #-48]!
     +0x4  mov     x29, sp
     +0x8  stp     x19, x20, [sp, #16]
     +0xc  mov     x19, x2                    size
    +0x10  mov     x20, x0                    dst
    +0x14  mov     x2, #0x20
    +0x18  str     x21, [sp, #32]
    +0x1c  mov     x21, x1                    src
    +0x20  bl      memmove                    memmove(dst, src, 32)
    +0x24  cmp     x19, #0x20
    +0x28  b.hi    +0x3c
    +0x2c  ldp     x19, x20, [sp, #16]
    +0x30  ldr     x21, [sp, #32]
    +0x34  ldp     x29, x30, [sp], #48
    +0x38  ret
    +0x3c  add     x1, x21, #0x20
    +0x40  add     x0, x20, #0x20
    +0x44  ldp     x19, x20, [sp, #16]
    +0x48  mov     x2, #0x20
    +0x4c  ldr     x21, [sp, #32]
    +0x50  ldp     x29, x30, [sp], #48
    +0x54  b       memmove                    memmove(dst + 32, src + 32, 32)
 ***)

let SNAPPY_MEM_COPY64_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "MemCopy64__charp_voidp_ulong"; layout_range "plt_memmove"];;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety.                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_MEM_COPY64_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e dst src size x pc rw sp returnaddress x19 x20 x21 x29 ea el ev.
     memmove_correct_safe_contract (imp "memmove") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     val size <= 64 /\
     nonoverlapping (dst,val size) (src,val size) /\
     ALLPAIRS nonoverlapping
      [(dst,64); (word_sub sp (word 48),48)]
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el)] /\
     nonoverlapping (dst,64) (word_sub sp (word 48),48) /\
     nonoverlapping (src,val size) (word_sub sp (word 48),48)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + MemCopy64__charp_voidp_ulong) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X29 s = x29 /\
           C_ARGUMENTS [dst; src; size] s /\
           read (memory :> bytes(src,val size)) s = x /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\
           read (memory :> bytes(ea,el)) s = ev /\
           read events s = e)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X29 s = x29 /\
           read (memory :> bytes(dst,val size)) s = x /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2
                 (memrange(dst,64) UNION memrange(src,64) UNION
                  memrange(word_sub sp (word 48),48) UNION
                  memrange(word(pc + libsnappy_rw),libsnappy_rw_size) UNION
                  memrange(ea,el))
                 (memrange(word_sub sp (word 48),48) UNION memrange(dst,64)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 48),48)] ,,
       MAYCHANGE [memory :> bytes(dst,32)] ,,
       MAYCHANGE [memory :> bytes(word_add dst (word 32),32)])`;;

let SNAPPY_MEM_COPY64_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_MEM_COPY64_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness alone.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_MEM_COPY64_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!dst src size x pc rw sp returnaddress x19 x20 x21 x29 ea el ev.
     memmove_correct_safe_contract (imp "memmove") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     val size <= 64 /\
     nonoverlapping (dst,val size) (src,val size) /\
     ALLPAIRS nonoverlapping
      [(dst,64); (word_sub sp (word 48),48)]
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el)] /\
     nonoverlapping (dst,64) (word_sub sp (word 48),48) /\
     nonoverlapping (src,val size) (word_sub sp (word 48),48)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + MemCopy64__charp_voidp_ulong) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X29 s = x29 /\
           C_ARGUMENTS [dst; src; size] s /\
           read (memory :> bytes(src,val size)) s = x /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\
           read (memory :> bytes(ea,el)) s = ev)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X29 s = x29 /\
           read (memory :> bytes(dst,val size)) s = x)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 48),48)] ,,
       MAYCHANGE [memory :> bytes(dst,32)] ,,
       MAYCHANGE [memory :> bytes(word_add dst (word 32),32)])`;;

let SNAPPY_MEM_COPY64_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_MEM_COPY64_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
