(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::RawCompress(const char* input, size_t input_length,              *)
(* char* compressed, size_t* compressed_length) (layout name                 *)
(* RawCompress__charp_ulong_charp_ulongp), compiled by gcc 12 with -O2: a    *)
(* tail call of RawCompress(..., CompressionOptions{1})                      *)
(* (raw_compress_options_spec.ml), so its result is that of level 1, with   *)
(* the same heap hypotheses and the same frame (the callee's frame of 96     *)
(* bytes below SP and the 1152 bytes below it).                              *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/raw_compress_options_spec.ml";;

(*** The code in the image (see the listing in layout.ml):

    RawCompress__charp_ulong_charp_ulongp:
     +0x0  mov     w4, #0x1                       kDefaultCompressionLevel
     +0x4  b       RawCompress__charp_ulong_charp_ulongp_CompressionOptions
 ***)

let SNAPPY_RAW_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !inp src out lenp H pc ea el ev rw stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\
    pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
    memcpy_contract (imp "memcpy") ea el ev /\
    memset_correct_safe_contract (imp "memset") ea el ev /\
    elf_relocated_data (word(pc + libsnappy_rw)) rw
      (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
    aligned 16 stackpointer /\
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
              word(pc + RawCompress__charp_ulong_charp_ulongp) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; word(LENGTH inp); out; lenp] s /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp /\
              heap_ok H (read (memory :> footprint (heap_fp H)) s))
         (\s. read PC s = returnaddress /\
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
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 96),96)] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 1248),1152)] ,,
          MAYCHANGE [memory :> footprint (heap_fp H)])`;;

let SNAPPY_RAW_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_RAW_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* Memory safety with correctness (DESIGN.md section 6).                     *)

let SNAPPY_RAW_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !e inp src out lenp H pc ea el ev rw stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\
    pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
    memcpy_correct_safe_contract (imp "memcpy") ea el ev /\
    memset_correct_safe_contract (imp "memset") ea el ev /\
    elf_relocated_data (word(pc + libsnappy_rw)) rw
      (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
    aligned 16 stackpointer /\
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
              word(pc + RawCompress__charp_ulong_charp_ulongp) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; word(LENGTH inp); out; lenp] s /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp /\
              read events s = e /\
              heap_ok H (read (memory :> footprint (heap_fp H)) s))
         (\s. read PC s = returnaddress /\
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

let SNAPPY_RAW_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_RAW_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
