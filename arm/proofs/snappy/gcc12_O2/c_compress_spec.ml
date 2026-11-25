(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy_status snappy_compress(const char* input, size_t input_length,    *)
(*                               char* compressed, size_t* compressed_length) *)
(* (snappy-c.cc, layout name c_snappy_compress), compiled by gcc 12 with    *)
(* -O2: it returns SNAPPY_BUFFER_TOO_SMALL (2) if *compressed_length is      *)
(* below snappy_max_compressed_length(input_length); otherwise it calls      *)
(* snappy::RawCompress(input, input_length, compressed, compressed_length)  *)
(* (raw_compress_spec.ml, level 1, the WorkingMemory on the heap) and       *)
(* returns SNAPPY_OK (0), or SNAPPY_INVALID_INPUT (1) if the length written  *)
(* is 0, which it never is for an input below 2^32 bytes (the varint of the  *)
(* length is at least one byte).                                             *)
(*                                                                           *)
(*  - CORRECT: the buffer is large enough. The output is snappy_compress 1   *)
(*    inp (so it decodes to the input and fits, SNAPPY_C_COMPRESS_OUTPUT     *)
(*    in the proof), *compressed_length is its length, the result is OK and  *)
(*    the heap is H again (no leak); the memory that changes is the output,  *)
(*    the length, the stack (the frame of 64 bytes and the 1248 bytes below  *)
(*    it for RawCompress and its callees) and the allocator's footprint.     *)
(*  - TOO_SMALL: the buffer is too small: the result is 2 and only the       *)
(*    frame on the stack changes (no heap, no output, any input length).     *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/raw_compress_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/c_max_compressed_length_spec.ml";;

(*** The code in the image (see the listing in layout.ml):

    c_snappy_compress:
     +0x0  stp     x29, x30, [sp, #-64]!
     +0x4  mov     x29, sp
     +0x8  str     x23, [sp, #48]
     +0xc  ldr     x23, [x3]                      *compressed_length
    +0x10  stp     x19, x20, [sp, #16]
    +0x14  mov     x19, x3
    +0x18  mov     x20, x1
    +0x1c  stp     x21, x22, [sp, #32]
    +0x20  mov     x21, x0
    +0x24  mov     x22, x2
    +0x28  mov     x0, x1
    +0x2c  bl      c_snappy_max_compressed_length
    +0x30  cmp     x23, x0
    +0x34  b.cc    +0x6c                          too small
    +0x38  mov     x2, x22
    +0x3c  mov     x1, x20
    +0x40  mov     x0, x21
    +0x44  mov     x3, x19
    +0x48  bl      RawCompress__charp_ulong_charp_ulongp
    +0x4c  ldr     x0, [x19]
    +0x50  ldp     x19, x20, [sp, #16]
    +0x54  cmp     x0, #0x0
    +0x58  ldp     x21, x22, [sp, #32]
    +0x5c  cset    w0, eq                         INVALID_INPUT if 0
    +0x60  ldr     x23, [sp, #48]
    +0x64  ldp     x29, x30, [sp], #64
    +0x68  ret
    +0x6c  ldp     x19, x20, [sp, #16]
    +0x70  mov     w0, #0x2                       BUFFER_TOO_SMALL
    +0x74  ldp     x21, x22, [sp, #32]
    +0x78  ldr     x23, [sp, #48]
    +0x7c  ldp     x29, x30, [sp], #64
    +0x80  ret
 ***)

let SNAPPY_C_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !inp src out lenp len H pc ea el ev rw stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\
    pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
    memcpy_contract (imp "memcpy") ea el ev /\
    memset_correct_safe_contract (imp "memset") ea el ev /\
    elf_relocated_data (word(pc + libsnappy_rw)) rw
      (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
    aligned 16 stackpointer /\
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
              read PC s = word(pc + c_snappy_compress) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; word(LENGTH inp); out; lenp] s /\
              read (memory :> bytes64 lenp) s = len /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp /\
              heap_ok H (read (memory :> footprint (heap_fp H)) s))
         (\s. read PC s = returnaddress /\
              C_RETURN s = word 0 /\
              read (memory :> bytes64 lenp) s =
              word(LENGTH(snappy_compress 1 inp)) /\
              read (memory :> bytelist
                     (out,LENGTH(snappy_compress 1 inp))) s =
              snappy_compress 1 inp /\
              heap_ok H (read (memory :> footprint (heap_fp H)) s))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
          MAYCHANGE [memory :> bytes(out,snappy_max_compressed_length
                                           (LENGTH inp));
                     memory :> bytes(lenp,8)] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 64),64)] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 1312),1248)] ,,
          MAYCHANGE [memory :> footprint (heap_fp H)])`;;

let SNAPPY_C_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_C_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* Memory safety with correctness (DESIGN.md section 6), the buffer large    *)
(* enough.                                                                   *)

let SNAPPY_C_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !e inp src out lenp len H pc ea el ev rw stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\
    pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
    memcpy_correct_safe_contract (imp "memcpy") ea el ev /\
    memset_correct_safe_contract (imp "memset") ea el ev /\
    elf_relocated_data (word(pc + libsnappy_rw)) rw
      (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
    aligned 16 stackpointer /\
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
              read PC s = word(pc + c_snappy_compress) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; word(LENGTH inp); out; lenp] s /\
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
              word(LENGTH(snappy_compress 1 inp)) /\
              read (memory :> bytelist
                     (out,LENGTH(snappy_compress 1 inp))) s =
              snappy_compress 1 inp /\
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

let SNAPPY_C_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_C_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

let SNAPPY_C_COMPRESS_TOO_SMALL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!src n out lenp len pc stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
    aligned 16 stackpointer /\
    val len < snappy_max_compressed_length (val n) /\
    nonoverlapping (word_sub stackpointer (word 64),64)
                   (word pc,libsnappy_size) /\
    nonoverlapping (lenp,8) (word_sub stackpointer (word 64),64)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s = word(pc + c_snappy_compress) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; n; out; lenp] s /\
              read (memory :> bytes64 lenp) s = len)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word 2)
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X30] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let SNAPPY_C_COMPRESS_TOO_SMALL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_C_COMPRESS_TOO_SMALL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
