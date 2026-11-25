(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::Compress(Source*, Sink*, CompressionOptions) (layout name         *)
(* Compress__Sourcep_Sinkp_CompressionOptions), compiled by gcc 12 with -O2, *)
(* the compressor without a caller workspace: it calls reader->Available()   *)
(* through the vtable, constructs WorkingMemory(Available()) on its stack    *)
(* (operator new through the PLT: one block (mem, snappy_working_memory_size *)
(* n) in front of the heap H), calls InternalCompress(reader, writer,        *)
(* options, &wm) and runs ~WorkingMemory, which frees the block (operator    *)
(* delete through the PLT): the heap is H again, nothing leaks.              *)
(*                                                                           *)
(* For the Source and Sink of RawCompress (in-image ByteArraySource and      *)
(* UncheckedByteArraySink, as in internal_compress_spec.ml) the result is    *)
(* snappy_compress level inp. The theorem is about any allocator that meets  *)
(* the model of arm/proofs/heap.ml at imp "_Znwm" and imp "_ZdlPv" (the GOT  *)
(* slots) with stk <= 1024 bytes of stack, and has room for the block        *)
(* (heap_room, decision D3). Its footprint heap_fp H is outside the library, *)
(* the stack (the frame of 96 bytes and the 1056 bytes below it for the      *)
(* callees: WorkingMemory(size_t) and operator new, InternalCompress,        *)
(* ~WorkingMemory and operator delete), the output, the input, the two       *)
(* objects and the region of memcpy and memset. The memory that changes is   *)
(* the output, the objects (the source's position, the sink's dest), the     *)
(* stack and the allocator's footprint (which contains the block). The frame *)
(* is two clauses, the saved registers at sp - 96 and the WorkingMemory      *)
(* object at sp - 48, so that the facts about the saved registers cross the *)
(* calls that write the object.                                              *)
(* The callee-saved registers and SP are preserved (standard frame).         *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/internal_compress_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/working_memory_ctor_ulong_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/working_memory_dtor_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/byte_array_source_available_spec.ml";;
needs "arm/proofs/heap_plt.ml";;

(*** The code in the image (see the listing in layout.ml):

    Compress__Sourcep_Sinkp_CompressionOptions:
     +0x0  stp     x29, x30, [sp, #-96]!
     +0x4  mov     x29, sp
     +0x8  stp     x21, x22, [sp, #32]
     +0xc  mov     x21, x1                    writer
    +0x10  mov     w22, w2                    options.level
    +0x14  ldr     x1, [x0]                   vptr
    +0x18  stp     x19, x20, [sp, #16]
    +0x1c  add     x19, sp, #0x30             &wm
    +0x20  mov     x20, x0                    reader
    +0x24  ldr     x1, [x1, #16]              Available
    +0x28  blr     x1
    +0x2c  mov     x1, x0
    +0x30  mov     x0, x19
    +0x34  bl      WorkingMemory_ctor__ulong
    +0x38  mov     x1, x21
    +0x3c  mov     x3, x19
    +0x40  mov     w2, w22
    +0x44  mov     x0, x20
    +0x48  bl      InternalCompress
    +0x4c  mov     x1, x0
    +0x50  mov     x0, x19
    +0x54  mov     x19, x1
    +0x58  bl      WorkingMemory_dtor
    +0x5c  ldp     x21, x22, [sp, #32]
    +0x60  mov     x0, x19
    +0x64  ldp     x19, x20, [sp, #16]
    +0x68  ldp     x29, x30, [sp], #96
    +0x6c  ret
 ***)

let SNAPPY_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !level inp src out so sk H pc ea el ev rw stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\
    pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
    memcpy_contract (imp "memcpy") ea el ev /\
    memset_correct_safe_contract (imp "memset") ea el ev /\
    elf_relocated_data (word(pc + libsnappy_rw)) rw
      (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
    aligned 16 stackpointer /\
    (level = 1 \/ level = 2) /\
    LENGTH inp < 2 EXP 32 /\
    val src + LENGTH inp + 65536 < 2 EXP 64 /\
    val out + snappy_max_compressed_length (LENGTH inp) < 2 EXP 64 /\
    heap_room H (snappy_working_memory_size (LENGTH inp)) /\ stk <= 1024 /\
    DISJOINT (memrange(word pc,libsnappy_rw + libsnappy_rw_size)) (heap_fp H) /\
    DISJOINT (memrange(word_sub stackpointer (word 1152),1152)) (heap_fp H) /\
    DISJOINT (memrange(out,snappy_max_compressed_length (LENGTH inp)))
             (heap_fp H) /\
    DISJOINT (memrange(so,24)) (heap_fp H) /\
    DISJOINT (memrange(sk,16)) (heap_fp H) /\
    DISJOINT (memrange(src,LENGTH inp)) (heap_fp H) /\
    DISJOINT (memrange(ea,el)) (heap_fp H) /\
    PAIRWISE nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp); so,24; sk,16;
      word_sub stackpointer (word 1152),1152] /\
    ALLPAIRS nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp); so,24; sk,16;
      word_sub stackpointer (word 1152),1152]
     [src,LENGTH inp; word pc,libsnappy_rw + libsnappy_rw_size; ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s =
              word(pc + Compress__Sourcep_Sinkp_CompressionOptions) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [so; sk; word level] s /\
              read (memory :> bytes64 so) s =
                word(pc + vtable_ByteArraySource) /\
              read (memory :> bytes64 (word_add so (word 8))) s = src /\
              read (memory :> bytes64 (word_add so (word 16))) s =
                word(LENGTH inp) /\
              read (memory :> bytes64 sk) s =
                word(pc + vtable_UncheckedByteArraySink) /\
              read (memory :> bytes64 (word_add sk (word 8))) s = out /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp /\
              heap_ok H (read (memory :> footprint (heap_fp H)) s))
         (\s. read PC s = returnaddress /\
              C_RETURN s = word(LENGTH(snappy_compress level inp)) /\
              read (memory :> bytelist
                     (out,LENGTH(snappy_compress level inp))) s =
              snappy_compress level inp /\
              read (memory :> bytes64 (word_add sk (word 8))) s =
              word_add out (word(LENGTH(snappy_compress level inp))) /\
              heap_ok H (read (memory :> footprint (heap_fp H)) s))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
          MAYCHANGE [memory :> bytes(out,snappy_max_compressed_length
                                           (LENGTH inp));
                     memory :> bytes(so,24); memory :> bytes(sk,16)] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 96),48)] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 48),48)] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 1152),1056)] ,,
          MAYCHANGE [memory :> footprint (heap_fp H)])`;;

let SNAPPY_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* Memory safety with correctness (DESIGN.md section 6): the events within   *)
(* the allocator's footprint (which contains the block of the working        *)
(* memory), the input, the output, the objects, the stack, the library and   *)
(* the region of memcpy and memset.                                          *)

let SNAPPY_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !e level inp src out so sk H pc ea el ev rw stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\
    pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
    memcpy_correct_safe_contract (imp "memcpy") ea el ev /\
    memset_correct_safe_contract (imp "memset") ea el ev /\
    elf_relocated_data (word(pc + libsnappy_rw)) rw
      (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
    aligned 16 stackpointer /\
    (level = 1 \/ level = 2) /\
    LENGTH inp < 2 EXP 32 /\
    val src + LENGTH inp + 65536 < 2 EXP 64 /\
    val out + snappy_max_compressed_length (LENGTH inp) < 2 EXP 64 /\
    heap_room H (snappy_working_memory_size (LENGTH inp)) /\ stk <= 1024 /\
    DISJOINT (memrange(word pc,libsnappy_rw + libsnappy_rw_size)) (heap_fp H) /\
    DISJOINT (memrange(word_sub stackpointer (word 1152),1152)) (heap_fp H) /\
    DISJOINT (memrange(out,snappy_max_compressed_length (LENGTH inp)))
             (heap_fp H) /\
    DISJOINT (memrange(so,24)) (heap_fp H) /\
    DISJOINT (memrange(sk,16)) (heap_fp H) /\
    DISJOINT (memrange(src,LENGTH inp)) (heap_fp H) /\
    DISJOINT (memrange(ea,el)) (heap_fp H) /\
    PAIRWISE nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp); so,24; sk,16;
      word_sub stackpointer (word 1152),1152] /\
    ALLPAIRS nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp); so,24; sk,16;
      word_sub stackpointer (word 1152),1152]
     [src,LENGTH inp; word pc,libsnappy_rw + libsnappy_rw_size; ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s =
              word(pc + Compress__Sourcep_Sinkp_CompressionOptions) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [so; sk; word level] s /\
              read (memory :> bytes64 so) s =
                word(pc + vtable_ByteArraySource) /\
              read (memory :> bytes64 (word_add so (word 8))) s = src /\
              read (memory :> bytes64 (word_add so (word 16))) s =
                word(LENGTH inp) /\
              read (memory :> bytes64 sk) s =
                word(pc + vtable_UncheckedByteArraySink) /\
              read (memory :> bytes64 (word_add sk (word 8))) s = out /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp /\
              read events s = e /\
              heap_ok H (read (memory :> footprint (heap_fp H)) s))
         (\s. read PC s = returnaddress /\
              C_RETURN s = word(LENGTH(snappy_compress level inp)) /\
              read (memory :> bytelist
                     (out,LENGTH(snappy_compress level inp))) s =
              snappy_compress level inp /\
              read (memory :> bytes64 (word_add sk (word 8))) s =
              word_add out (word(LENGTH(snappy_compress level inp))) /\
              heap_ok H (read (memory :> footprint (heap_fp H)) s) /\
              ?e2. read events s = APPEND e2 e /\
                   memaccess_inset e2
                    (heap_fp H UNION memrange(src,LENGTH inp) UNION
                     memrange(out,snappy_max_compressed_length (LENGTH inp)) UNION
                     memrange(so,24) UNION memrange(sk,16) UNION
                     memrange(word_sub stackpointer (word 1152),1152) UNION
                     memrange(word pc,libsnappy_rw + libsnappy_rw_size) UNION
                     memrange(ea,el))
                    (heap_fp H UNION
                     memrange(out,snappy_max_compressed_length (LENGTH inp)) UNION
                     memrange(so,24) UNION memrange(sk,16) UNION
                     memrange(word_sub stackpointer (word 1152),1152)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
          MAYCHANGE [memory :> bytes(out,snappy_max_compressed_length
                                           (LENGTH inp));
                     memory :> bytes(so,24); memory :> bytes(sk,16)] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 96),48)] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 48),48)] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 1152),1056)] ,,
          MAYCHANGE [memory :> footprint (heap_fp H)])`;;

let SNAPPY_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
