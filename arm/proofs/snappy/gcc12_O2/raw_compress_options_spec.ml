(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::RawCompress(const char* input, size_t input_length,              *)
(* char* compressed, size_t* compressed_length, CompressionOptions) (layout  *)
(* name RawCompress__charp_ulong_charp_ulongp_CompressionOptions), compiled  *)
(* by gcc 12 with -O2, the compressor without a context: it makes a          *)
(* ByteArraySource and an UncheckedByteArraySink on its stack, calls         *)
(* Compress(Source*, Sink*, CompressionOptions) (compress_options_spec.ml),  *)
(* which allocates the WorkingMemory on the heap and frees it, stores the    *)
(* length written and destroys the two objects.                              *)
(*                                                                           *)
(* With the level 1 or 2, an input of fewer than 2^32 bytes, an output       *)
(* buffer of snappy_max_compressed_length n bytes and room in the heap for   *)
(* the WorkingMemory (heap_room, decision D3), the output is snappy_compress *)
(* level inp (so it decodes to the input and fits, SNAPPY_COMPRESS_ROUNDTRIP *)
(* and SNAPPY_COMPRESS_LENGTH), *compressed_length is its length, and the    *)
(* heap is H again (no leak). The memory that changes is the output, the     *)
(* length, the stack (the frame of 96 bytes and the 1152 bytes below it for  *)
(* Compress and its callees) and the allocator's footprint heap_fp H, which  *)
(* is outside all the other regions.                                         *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_options_spec.ml";;

(*** The code in the image (see the listing in layout.ml):

    RawCompress__charp_ulong_charp_ulongp_CompressionOptions:
     +0x0  stp     x29, x30, [sp, #-96]!
     +0x4  adrp    x5, got_ztv_ByteArraySource
     +0x8  ldr     x5, [x5, #4056]
     +0xc  mov     x29, sp
    +0x10  adrp    x6, got_ztv_UncheckedByteArraySink
    +0x14  ldr     x6, [x6, #4040]
    +0x18  add     x5, x5, #0x10                  vptr of ByteArraySource
    +0x1c  stp     x19, x20, [sp, #16]
    +0x20  mov     x20, x2                        compressed
    +0x24  add     x6, x6, #0x10                  vptr of the sink
    +0x28  mov     w2, w4                         options.level
    +0x2c  mov     x4, x0
    +0x30  stp     x21, x22, [sp, #32]
    +0x34  mov     x22, x3                        compressed_length
    +0x38  mov     x3, x1
    +0x3c  add     x21, sp, #0x38                 the sink, at sp + 56
    +0x40  add     x19, sp, #0x48                 the source, at sp + 72
    +0x44  mov     x1, x21
    +0x48  mov     x0, x19
    +0x4c  stp     x6, x20, [sp, #56]
    +0x50  stp     x5, x4, [sp, #72]
    +0x54  str     x3, [sp, #88]
    +0x58  bl      Compress__Sourcep_Sinkp_CompressionOptions
    +0x5c  ldr     x1, [sp, #64]                  the sink's dest
    +0x60  mov     x0, x21
    +0x64  sub     x1, x1, x20
    +0x68  str     x1, [x22]
    +0x6c  bl      UncheckedByteArraySink_dtor
    +0x70  mov     x0, x19
    +0x74  bl      ByteArraySource_dtor
    +0x78  ldp     x19, x20, [sp, #16]
    +0x7c  ldp     x21, x22, [sp, #32]
    +0x80  ldp     x29, x30, [sp], #96
    +0x84  ret
 ***)

let SNAPPY_RAW_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !level inp src out lenp H pc ea el ev rw stackpointer returnaddress.
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
    DISJOINT (memrange(word_sub stackpointer (word 1248),1248)) (heap_fp H) /\
    DISJOINT (memrange(out,snappy_max_compressed_length (LENGTH inp)))
             (heap_fp H) /\
    DISJOINT (memrange(lenp,8)) (heap_fp H) /\
    DISJOINT (memrange(src,LENGTH inp)) (heap_fp H) /\
    DISJOINT (memrange(ea,el)) (heap_fp H) /\
    PAIRWISE nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp); lenp,8;
      word_sub stackpointer (word 1248),1248] /\
    ALLPAIRS nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp); lenp,8;
      word_sub stackpointer (word 1248),1248]
     [src,LENGTH inp; word pc,libsnappy_rw + libsnappy_rw_size; ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s =
              word(pc + RawCompress__charp_ulong_charp_ulongp_CompressionOptions) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; word(LENGTH inp); out; lenp; word level] s /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp /\
              heap_ok H (read (memory :> footprint (heap_fp H)) s))
         (\s. read PC s = returnaddress /\
              read (memory :> bytes64 lenp) s =
              word(LENGTH(snappy_compress level inp)) /\
              read (memory :> bytelist
                     (out,LENGTH(snappy_compress level inp))) s =
              snappy_compress level inp /\
              heap_ok H (read (memory :> footprint (heap_fp H)) s))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
          MAYCHANGE [memory :> bytes(out,snappy_max_compressed_length
                                           (LENGTH inp));
                     memory :> bytes(lenp,8)] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 96),96)] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 1248),1152)] ,,
          MAYCHANGE [memory :> footprint (heap_fp H)])`;;

let SNAPPY_RAW_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_RAW_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* Memory safety with correctness (DESIGN.md section 6).                     *)

let SNAPPY_RAW_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !e level inp src out lenp H pc ea el ev rw stackpointer returnaddress.
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
    DISJOINT (memrange(word_sub stackpointer (word 1248),1248)) (heap_fp H) /\
    DISJOINT (memrange(out,snappy_max_compressed_length (LENGTH inp)))
             (heap_fp H) /\
    DISJOINT (memrange(lenp,8)) (heap_fp H) /\
    DISJOINT (memrange(src,LENGTH inp)) (heap_fp H) /\
    DISJOINT (memrange(ea,el)) (heap_fp H) /\
    PAIRWISE nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp); lenp,8;
      word_sub stackpointer (word 1248),1248] /\
    ALLPAIRS nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp); lenp,8;
      word_sub stackpointer (word 1248),1248]
     [src,LENGTH inp; word pc,libsnappy_rw + libsnappy_rw_size; ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s =
              word(pc + RawCompress__charp_ulong_charp_ulongp_CompressionOptions) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; word(LENGTH inp); out; lenp; word level] s /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp /\
              read events s = e /\
              heap_ok H (read (memory :> footprint (heap_fp H)) s))
         (\s. read PC s = returnaddress /\
              read (memory :> bytes64 lenp) s =
              word(LENGTH(snappy_compress level inp)) /\
              read (memory :> bytelist
                     (out,LENGTH(snappy_compress level inp))) s =
              snappy_compress level inp /\
              heap_ok H (read (memory :> footprint (heap_fp H)) s) /\
              ?e2. read events s = APPEND e2 e /\
                   memaccess_inset e2
                    (heap_fp H UNION memrange(src,LENGTH inp) UNION
                     memrange(out,snappy_max_compressed_length (LENGTH inp)) UNION
                     memrange(lenp,8) UNION
                     memrange(word_sub stackpointer (word 1248),1248) UNION
                     memrange(word pc,libsnappy_rw + libsnappy_rw_size) UNION
                     memrange(ea,el))
                    (heap_fp H UNION
                     memrange(out,snappy_max_compressed_length (LENGTH inp)) UNION
                     memrange(lenp,8) UNION
                     memrange(word_sub stackpointer (word 1248),1248)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
          MAYCHANGE [memory :> bytes(out,snappy_max_compressed_length
                                           (LENGTH inp));
                     memory :> bytes(lenp,8)] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 96),96)] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 1248),1152)] ,,
          MAYCHANGE [memory :> footprint (heap_fp H)])`;;

let SNAPPY_RAW_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_RAW_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
