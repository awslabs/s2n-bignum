(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::RawCompress(const char* input, size_t input_length,              *)
(* char* compressed, size_t* compressed_length, CompressionOptions,         *)
(* CompressionContext* ) (layout name RawCompress__charp_ulong_charp_ulongp_ *)
(* CompressionOptions_CompressionContextp), compiled by gcc 12 with -O2: it  *)
(* makes a ByteArraySource and an UncheckedByteArraySink on its stack, calls *)
(* Compress(Source*, Sink*, CompressionOptions, CompressionContext* ),       *)
(* stores the length written and destroys the two objects. With the level 1 *)
(* or 2, an input of fewer than 2^32 bytes and an output buffer of          *)
(* snappy_max_compressed_length n bytes, the output is snappy_compress level *)
(* inp, so (SNAPPY_RAW_COMPRESS_CTX_ROUNDTRIP below) it decodes to the input *)
(* and fits. The context cc is as CompressionContext(void*, size_t) leaves   *)
(* it (snappy_compression_context and snappy_working_memory of              *)
(* arm/proofs/snappy/objects.ml); for a caller workspace ws of WorkspaceSize *)
(* bytes, wm = ws, mem = ws + 48 and nw = 65536.                             *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_ctx_spec.ml";;
needs "common/snappy/snappy_roundtrip.ml";;

let SNAPPY_RAW_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!level inp src out lenp cc wm owc mem nw owns pc imp ea el ev rw
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
      mem,snappy_working_memory_size nw; lenp,8;
      word_sub stackpointer (word 96),96;
      word_sub (word_sub stackpointer (word 96)) (word 160),160;
      word_sub (word_sub stackpointer (word 96)) (word 208),48] /\
    ALLPAIRS nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp);
      mem,snappy_working_memory_size nw; lenp,8;
      word_sub stackpointer (word 96),96;
      word_sub (word_sub stackpointer (word 96)) (word 160),160;
      word_sub (word_sub stackpointer (word 96)) (word 208),48]
     [src,LENGTH inp; wm,48; cc,16; word pc,libsnappy_rw + libsnappy_rw_size;
      ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s =
              word(pc + RawCompress__charp_ulong_charp_ulongp_CompressionOptions_CompressionContextp) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; word(LENGTH inp); out; lenp; word level; cc] s /\
              snappy_compression_context cc wm owc s /\
              snappy_working_memory wm mem nw owns s /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp)
         (\s. read PC s = returnaddress /\
              read (memory :> bytes64 lenp) s =
              word(LENGTH(snappy_compress level inp)) /\
              read (memory :> bytelist
                     (out,LENGTH(snappy_compress level inp))) s =
              snappy_compress level inp)
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
          MAYCHANGE [memory :> bytes(out,snappy_max_compressed_length
                                           (LENGTH inp));
                     memory :> bytes(mem,snappy_working_memory_size nw);
                     memory :> bytes(lenp,8);
                     memory :> bytes(word_sub stackpointer (word 96),96);
                     memory :> bytes(word_sub (word_sub stackpointer (word 96)) (word 160),160);
                     memory :> bytes(word_sub (word_sub stackpointer (word 96)) (word 208),48)])`;;

let SNAPPY_RAW_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_RAW_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* Memory safety with correctness (DESIGN.md section 6), from the _SAFE     *)
(* contract of Compress(ctx): also the Source and Sink in the frame and the  *)
(* length.                                                                   *)

let SNAPPY_RAW_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e level inp src out lenp cc wm owc mem nw owns pc imp ea el ev rw
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
      mem,snappy_working_memory_size nw; lenp,8;
      word_sub stackpointer (word 96),96;
      word_sub (word_sub stackpointer (word 96)) (word 160),160;
      word_sub (word_sub stackpointer (word 96)) (word 208),48] /\
    ALLPAIRS nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp);
      mem,snappy_working_memory_size nw; lenp,8;
      word_sub stackpointer (word 96),96;
      word_sub (word_sub stackpointer (word 96)) (word 160),160;
      word_sub (word_sub stackpointer (word 96)) (word 208),48]
     [src,LENGTH inp; wm,48; cc,16; word pc,libsnappy_rw + libsnappy_rw_size;
      ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s =
              word(pc + RawCompress__charp_ulong_charp_ulongp_CompressionOptions_CompressionContextp) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; word(LENGTH inp); out; lenp; word level; cc] s /\
              snappy_compression_context cc wm owc s /\
              snappy_working_memory wm mem nw owns s /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp /\
              read events s = e)
         (\s. read PC s = returnaddress /\
              read (memory :> bytes64 lenp) s =
              word(LENGTH(snappy_compress level inp)) /\
              read (memory :> bytelist
                     (out,LENGTH(snappy_compress level inp))) s =
              snappy_compress level inp /\
              ?e2. read events s = APPEND e2 e /\
                   memaccess_inset e2
                    (memrange(src,LENGTH inp) UNION memrange(wm,48) UNION
                     memrange(cc,16) UNION
                     memrange(out,snappy_max_compressed_length (LENGTH inp)) UNION
                     memrange(mem,snappy_working_memory_size nw) UNION
                     memrange(lenp,8) UNION
                     memrange(word_sub stackpointer (word 96),96) UNION
                     memrange(word_sub (word_sub stackpointer (word 96)) (word 160),160) UNION
                     memrange(word_sub (word_sub stackpointer (word 96)) (word 208),48) UNION
                     memrange(word pc,libsnappy_rw + libsnappy_rw_size) UNION
                     memrange(ea,el))
                    (memrange(out,snappy_max_compressed_length (LENGTH inp)) UNION
                     memrange(mem,snappy_working_memory_size nw) UNION
                     memrange(lenp,8) UNION
                     memrange(word_sub stackpointer (word 96),96) UNION
                     memrange(word_sub (word_sub stackpointer (word 96)) (word 160),160) UNION
                     memrange(word_sub (word_sub stackpointer (word 96)) (word 208),48)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
          MAYCHANGE [memory :> bytes(out,snappy_max_compressed_length
                                           (LENGTH inp));
                     memory :> bytes(mem,snappy_working_memory_size nw);
                     memory :> bytes(lenp,8);
                     memory :> bytes(word_sub stackpointer (word 96),96);
                     memory :> bytes(word_sub (word_sub stackpointer (word 96)) (word 160),160);
                     memory :> bytes(word_sub (word_sub stackpointer (word 96)) (word 208),48)])`;;

let SNAPPY_RAW_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_RAW_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

