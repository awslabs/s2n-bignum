(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy_status snappy_compress_with_level(const char* input,              *)
(*     size_t input_length, int compression_level, char* compressed,         *)
(*     size_t* compressed_length) (snappy-c.cc, layout name                  *)
(* c_snappy_compress_with_level), compiled by gcc 12 with -O2: it returns    *)
(* SNAPPY_BUFFER_TOO_SMALL (2) if *compressed_length is below                *)
(* snappy_max_compressed_length(input_length), then SNAPPY_INVALID_INPUT (1) *)
(* for a level other than 1 and 2 (the int in the low 32 bits of x2, the     *)
(* upper bits are unspecified, lv below); otherwise it calls                 *)
(* snappy::RawCompress(input, input_length, compressed, compressed_length,   *)
(* CompressionOptions{level}) (raw_compress_options_spec.ml, the             *)
(* WorkingMemory on the heap) and returns SNAPPY_OK (0), or                  *)
(* SNAPPY_INVALID_INPUT if the length written is 0, which it never is for an *)
(* input below 2^32 bytes.                                                   *)
(*                                                                           *)
(*  - CORRECT: the buffer is large enough and the level is 1 or 2. The       *)
(*    output is snappy_compress level inp (it decodes to the input and fits, *)
(*    SNAPPY_C_COMPRESS_WITH_LEVEL_OUTPUT in the proof), *compressed_length  *)
(*    is its length, the result is OK and the heap is H again (no leak); the *)
(*    memory that changes is the output, the length, the stack (the frame of *)
(*    64 bytes and the 1248 bytes below it) and the allocator's footprint.   *)
(*  - INVALID_LEVEL: the buffer is large enough and the level is not 1 or 2: *)
(*    the result is 1 and only the frame on the stack changes.               *)
(*  - TOO_SMALL: the buffer is too small (any level): the result is 2 and    *)
(*    only the frame on the stack changes.                                   *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/raw_compress_options_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/c_max_compressed_length_spec.ml";;

(*** The code in the image (see the listing in layout.ml):

    c_snappy_compress_with_level:
     +0x0  stp     x29, x30, [sp, #-64]!
     +0x4  mov     x29, sp
     +0x8  stp     x23, x24, [sp, #48]
     +0xc  mov     x23, x3                        compressed
    +0x10  ldr     x24, [x4]                      *compressed_length
    +0x14  stp     x19, x20, [sp, #16]
    +0x18  mov     x19, x4
    +0x1c  mov     x20, x1
    +0x20  stp     x21, x22, [sp, #32]
    +0x24  mov     x22, x0
    +0x28  mov     w21, w2                        compression_level
    +0x2c  mov     x0, x1
    +0x30  bl      c_snappy_max_compressed_length
    +0x34  cmp     x24, x0
    +0x38  b.cc    +0x98                          too small
    +0x3c  sub     w1, w21, #0x1
    +0x40  mov     w0, #0x1                       INVALID_INPUT
    +0x44  cmp     w1, w0
    +0x48  b.ls    +0x60                          level 1 or 2
    +0x4c  ldp     x19, x20, [sp, #16]
    +0x50  ldp     x21, x22, [sp, #32]
    +0x54  ldp     x23, x24, [sp, #48]
    +0x58  ldp     x29, x30, [sp], #64
    +0x5c  ret
    +0x60  mov     w4, w21
    +0x64  mov     x2, x23
    +0x68  mov     x1, x20
    +0x6c  mov     x0, x22
    +0x70  mov     x3, x19
    +0x74  bl      RawCompress__charp_ulong_charp_ulongp_CompressionOptions
    +0x78  ldr     x0, [x19]
    +0x7c  ldp     x19, x20, [sp, #16]
    +0x80  cmp     x0, #0x0
    +0x84  ldp     x21, x22, [sp, #32]
    +0x88  cset    w0, eq                         INVALID_INPUT if 0
    +0x8c  ldp     x23, x24, [sp, #48]
    +0x90  ldp     x29, x30, [sp], #64
    +0x94  ret
    +0x98  ldp     x19, x20, [sp, #16]
    +0x9c  mov     w0, #0x2                       BUFFER_TOO_SMALL
    +0xa0  ldp     x21, x22, [sp, #32]
    +0xa4  ldp     x23, x24, [sp, #48]
    +0xa8  ldp     x29, x30, [sp], #64
    +0xac  ret
 ***)

let SNAPPY_C_COMPRESS_WITH_LEVEL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !level lv inp src out lenp len H pc ea el ev rw stackpointer
        returnaddress.
    aligned 4096 (word pc:int64) /\
    pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
    memcpy_contract (imp "memcpy") ea el ev /\
    memset_correct_safe_contract (imp "memset") ea el ev /\
    elf_relocated_data (word(pc + libsnappy_rw)) rw
      (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
    aligned 16 stackpointer /\
    (level = 1 \/ level = 2) /\ word_zx lv:int32 = word level /\
    LENGTH inp < 2 EXP 32 /\
    snappy_max_compressed_length (LENGTH inp) <= val len /\
    val src + LENGTH inp + 65536 < 2 EXP 64 /\
    val out + snappy_max_compressed_length (LENGTH inp) < 2 EXP 64 /\
    heap_room H (snappy_working_memory_size (LENGTH inp)) /\ stk <= 1024 /\
    DISJOINT (memrange(word pc,libsnappy_rw + libsnappy_rw_size)) (heap_fp H) /\
    DISJOINT (memrange(word_sub stackpointer (word 1312),1312)) (heap_fp H) /\
    DISJOINT (memrange(out,snappy_max_compressed_length (LENGTH inp)))
             (heap_fp H) /\
    DISJOINT (memrange(lenp,8)) (heap_fp H) /\
    DISJOINT (memrange(src,LENGTH inp)) (heap_fp H) /\
    DISJOINT (memrange(ea,el)) (heap_fp H) /\
    PAIRWISE nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp); lenp,8;
      word_sub stackpointer (word 1312),1312] /\
    ALLPAIRS nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp); lenp,8;
      word_sub stackpointer (word 1312),1312]
     [src,LENGTH inp; word pc,libsnappy_rw + libsnappy_rw_size; ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s = word(pc + c_snappy_compress_with_level) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; word(LENGTH inp); lv; out; lenp] s /\
              read (memory :> bytes64 lenp) s = len /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp /\
              heap_ok H (read (memory :> footprint (heap_fp H)) s))
         (\s. read PC s = returnaddress /\
              C_RETURN s = word 0 /\
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
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 64),64)] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 1312),1248)] ,,
          MAYCHANGE [memory :> footprint (heap_fp H)])`;;

let SNAPPY_C_COMPRESS_WITH_LEVEL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_C_COMPRESS_WITH_LEVEL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* Memory safety with correctness (DESIGN.md section 6), the level 1 or 2   *)
(* and the buffer large enough.                                              *)

let SNAPPY_C_COMPRESS_WITH_LEVEL_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !e level lv inp src out lenp len H pc ea el ev rw stackpointer
        returnaddress.
    aligned 4096 (word pc:int64) /\
    pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
    memcpy_correct_safe_contract (imp "memcpy") ea el ev /\
    memset_correct_safe_contract (imp "memset") ea el ev /\
    elf_relocated_data (word(pc + libsnappy_rw)) rw
      (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
    aligned 16 stackpointer /\
    (level = 1 \/ level = 2) /\ word_zx lv:int32 = word level /\
    LENGTH inp < 2 EXP 32 /\
    snappy_max_compressed_length (LENGTH inp) <= val len /\
    val src + LENGTH inp + 65536 < 2 EXP 64 /\
    val out + snappy_max_compressed_length (LENGTH inp) < 2 EXP 64 /\
    heap_room H (snappy_working_memory_size (LENGTH inp)) /\ stk <= 1024 /\
    DISJOINT (memrange(word pc,libsnappy_rw + libsnappy_rw_size)) (heap_fp H) /\
    DISJOINT (memrange(word_sub stackpointer (word 1312),1312)) (heap_fp H) /\
    DISJOINT (memrange(out,snappy_max_compressed_length (LENGTH inp)))
             (heap_fp H) /\
    DISJOINT (memrange(lenp,8)) (heap_fp H) /\
    DISJOINT (memrange(src,LENGTH inp)) (heap_fp H) /\
    DISJOINT (memrange(ea,el)) (heap_fp H) /\
    PAIRWISE nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp); lenp,8;
      word_sub stackpointer (word 1312),1312] /\
    ALLPAIRS nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp); lenp,8;
      word_sub stackpointer (word 1312),1312]
     [src,LENGTH inp; word pc,libsnappy_rw + libsnappy_rw_size; ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s = word(pc + c_snappy_compress_with_level) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; word(LENGTH inp); lv; out; lenp] s /\
              read (memory :> bytes64 lenp) s = len /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp /\
              read events s = e /\
              heap_ok H (read (memory :> footprint (heap_fp H)) s))
         (\s. read PC s = returnaddress /\
              C_RETURN s = word 0 /\
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
                     memrange(word_sub stackpointer (word 1312),1312) UNION
                     memrange(word pc,libsnappy_rw + libsnappy_rw_size) UNION
                     memrange(ea,el))
                    (heap_fp H UNION
                     memrange(out,snappy_max_compressed_length (LENGTH inp)) UNION
                     memrange(lenp,8) UNION
                     memrange(word_sub stackpointer (word 1312),1312)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
          MAYCHANGE [memory :> bytes(out,snappy_max_compressed_length
                                           (LENGTH inp));
                     memory :> bytes(lenp,8)] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 64),64)] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 1312),1248)] ,,
          MAYCHANGE [memory :> footprint (heap_fp H)])`;;

let SNAPPY_C_COMPRESS_WITH_LEVEL_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_C_COMPRESS_WITH_LEVEL_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

let SNAPPY_C_COMPRESS_WITH_LEVEL_INVALID_LEVEL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!src n lv out lenp len pc stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
    aligned 16 stackpointer /\
    snappy_max_compressed_length (val n) <= val len /\
    ~(word_zx lv:int32 = word 1) /\ ~(word_zx lv:int32 = word 2) /\
    nonoverlapping (word_sub stackpointer (word 64),64)
                   (word pc,libsnappy_size) /\
    nonoverlapping (lenp,8) (word_sub stackpointer (word 64),64)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s = word(pc + c_snappy_compress_with_level) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; n; lv; out; lenp] s /\
              read (memory :> bytes64 lenp) s = len)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word 1)
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X30] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let SNAPPY_C_COMPRESS_WITH_LEVEL_INVALID_LEVEL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_C_COMPRESS_WITH_LEVEL_INVALID_LEVEL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

let SNAPPY_C_COMPRESS_WITH_LEVEL_TOO_SMALL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!src n lv out lenp len pc stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
    aligned 16 stackpointer /\
    val len < snappy_max_compressed_length (val n) /\
    nonoverlapping (word_sub stackpointer (word 64),64)
                   (word pc,libsnappy_size) /\
    nonoverlapping (lenp,8) (word_sub stackpointer (word 64),64)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s = word(pc + c_snappy_compress_with_level) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; n; lv; out; lenp] s /\
              read (memory :> bytes64 lenp) s = len)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word 2)
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X30] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let SNAPPY_C_COMPRESS_WITH_LEVEL_TOO_SMALL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_C_COMPRESS_WITH_LEVEL_TOO_SMALL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
