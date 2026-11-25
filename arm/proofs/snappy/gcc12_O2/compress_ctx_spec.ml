(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::Compress(Source*, Sink*, CompressionOptions, CompressionContext* )*)
(* (layout name Compress__Sourcep_Sinkp_CompressionOptions_                  *)
(* CompressionContextp), compiled by gcc 12 with -O2: it loads the context's *)
(* working_memory_ and tail-calls InternalCompress. For the Source and Sink  *)
(* of RawCompress, its result is that of internal_compress_spec.ml.          *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/internal_compress_spec.ml";;

let SNAPPY_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!level inp src out so sk cc wm owc mem nw owns pc imp ea el ev rw
   stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\
    pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
    memcpy_contract (imp "memcpy") ea el ev /\
    memset_correct_safe_contract (imp "memset") ea el ev /\
    elf_relocated_data (word(pc + libsnappy_rw)) rw
      (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
    aligned 16 stackpointer /\
    (level = 1 \/ level = 2) /\
    LENGTH inp < 2 EXP 32 /\
    snappy_fragment_size (LENGTH inp) <= snappy_fragment_size nw /\
    val src + LENGTH inp + 65536 < 2 EXP 64 /\
    val out + snappy_max_compressed_length (LENGTH inp) < 2 EXP 64 /\
    PAIRWISE nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp);
      mem,snappy_working_memory_size nw; so,24; sk,16;
      word_sub stackpointer (word 160),160;
      word_sub stackpointer (word 208),48] /\
    ALLPAIRS nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp);
      mem,snappy_working_memory_size nw; so,24; sk,16;
      word_sub stackpointer (word 160),160;
      word_sub stackpointer (word 208),48]
     [src,LENGTH inp; wm,48; cc,16; word pc,libsnappy_rw + libsnappy_rw_size;
      ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s =
              word(pc + Compress__Sourcep_Sinkp_CompressionOptions_CompressionContextp) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [so; sk; word level; cc] s /\
              read (memory :> bytes64 so) s =
                word(pc + vtable_ByteArraySource) /\
              read (memory :> bytes64 (word_add so (word 8))) s = src /\
              read (memory :> bytes64 (word_add so (word 16))) s =
                word(LENGTH inp) /\
              read (memory :> bytes64 sk) s =
                word(pc + vtable_UncheckedByteArraySink) /\
              read (memory :> bytes64 (word_add sk (word 8))) s = out /\
              snappy_compression_context cc wm owc s /\
              snappy_working_memory wm mem nw owns s /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word(LENGTH(snappy_compress level inp)) /\
              read (memory :> bytelist
                     (out,LENGTH(snappy_compress level inp))) s =
              snappy_compress level inp /\
              read (memory :> bytes64 (word_add sk (word 8))) s =
              word_add out (word(LENGTH(snappy_compress level inp))))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
          MAYCHANGE [memory :> bytes(out,snappy_max_compressed_length
                                           (LENGTH inp));
                     memory :> bytes(mem,snappy_working_memory_size nw);
                     memory :> bytes(so,24); memory :> bytes(sk,16);
                     memory :> bytes(word_sub stackpointer (word 160),160);
                     memory :> bytes(word_sub stackpointer (word 208),48)])`;;

let SNAPPY_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* Memory safety with correctness (DESIGN.md section 6), from the _SAFE     *)
(* contract of InternalCompress: also the load of the context.              *)

let SNAPPY_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e level inp src out so sk cc wm owc mem nw owns pc imp ea el ev rw
   stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\
    pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
    memcpy_correct_safe_contract (imp "memcpy") ea el ev /\
    memset_correct_safe_contract (imp "memset") ea el ev /\
    elf_relocated_data (word(pc + libsnappy_rw)) rw
      (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
    aligned 16 stackpointer /\
    (level = 1 \/ level = 2) /\
    LENGTH inp < 2 EXP 32 /\
    snappy_fragment_size (LENGTH inp) <= snappy_fragment_size nw /\
    val src + LENGTH inp + 65536 < 2 EXP 64 /\
    val out + snappy_max_compressed_length (LENGTH inp) < 2 EXP 64 /\
    PAIRWISE nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp);
      mem,snappy_working_memory_size nw; so,24; sk,16;
      word_sub stackpointer (word 160),160;
      word_sub stackpointer (word 208),48] /\
    ALLPAIRS nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp);
      mem,snappy_working_memory_size nw; so,24; sk,16;
      word_sub stackpointer (word 160),160;
      word_sub stackpointer (word 208),48]
     [src,LENGTH inp; wm,48; cc,16; word pc,libsnappy_rw + libsnappy_rw_size;
      ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s =
              word(pc + Compress__Sourcep_Sinkp_CompressionOptions_CompressionContextp) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [so; sk; word level; cc] s /\
              read (memory :> bytes64 so) s =
                word(pc + vtable_ByteArraySource) /\
              read (memory :> bytes64 (word_add so (word 8))) s = src /\
              read (memory :> bytes64 (word_add so (word 16))) s =
                word(LENGTH inp) /\
              read (memory :> bytes64 sk) s =
                word(pc + vtable_UncheckedByteArraySink) /\
              read (memory :> bytes64 (word_add sk (word 8))) s = out /\
              snappy_compression_context cc wm owc s /\
              snappy_working_memory wm mem nw owns s /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp /\
              read events s = e)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word(LENGTH(snappy_compress level inp)) /\
              read (memory :> bytelist
                     (out,LENGTH(snappy_compress level inp))) s =
              snappy_compress level inp /\
              read (memory :> bytes64 (word_add sk (word 8))) s =
              word_add out (word(LENGTH(snappy_compress level inp))) /\
              ?e2. read events s = APPEND e2 e /\
                   memaccess_inset e2
                    (memrange(src,LENGTH inp) UNION memrange(wm,48) UNION
                     memrange(cc,16) UNION
                     memrange(out,snappy_max_compressed_length (LENGTH inp)) UNION
                     memrange(mem,snappy_working_memory_size nw) UNION
                     memrange(so,24) UNION memrange(sk,16) UNION
                     memrange(word_sub stackpointer (word 160),160) UNION
                     memrange(word_sub stackpointer (word 208),48) UNION
                     memrange(word pc,libsnappy_rw + libsnappy_rw_size) UNION
                     memrange(ea,el))
                    (memrange(out,snappy_max_compressed_length (LENGTH inp)) UNION
                     memrange(mem,snappy_working_memory_size nw) UNION
                     memrange(so,24) UNION memrange(sk,16) UNION
                     memrange(word_sub stackpointer (word 160),160) UNION
                     memrange(word_sub stackpointer (word 208),48)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
          MAYCHANGE [memory :> bytes(out,snappy_max_compressed_length
                                           (LENGTH inp));
                     memory :> bytes(mem,snappy_working_memory_size nw);
                     memory :> bytes(so,24); memory :> bytes(sk,16);
                     memory :> bytes(word_sub stackpointer (word 160),160);
                     memory :> bytes(word_sub stackpointer (word 208),48)])`;;

let SNAPPY_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
