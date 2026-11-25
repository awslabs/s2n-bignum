(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::InternalCompress(Source*, Sink*, CompressionOptions,             *)
(* WorkingMemory* ), compiled by gcc 12 with -O2 (see arm/snappy/README.md),*)
(* in the whole image (libsnappy.ml), for the Source and Sink of RawCompress:*)
(* an in-image ByteArraySource (vptr, pointer, bytes left) over the input    *)
(* inp at src and an in-image UncheckedByteArraySink (vptr, dest) whose      *)
(* dest is out. Its virtual calls go through the vtables in the relocated    *)
(* data to the methods of these classes in the image. The result is the     *)
(* model snappy_compress level inp of common/snappy/snappy_compress.ml: the  *)
(* varint of the length, then each fragment of 65536 bytes compressed by     *)
(* CompressFragment (level 1) or CompressFragmentDoubleHash (level 2) with a *)
(* fresh table from WorkingMemory::GetHashTable; the function returns its    *)
(* length and the sink's dest has advanced by it. The WorkingMemory at wm   *)
(* (snappy_working_memory of arm/proofs/snappy/objects.ml) was made for nw   *)
(* bytes, at least the fragment size of the input, with its memory at mem;  *)
(* InternalCompress writes the table there (no heap terms: the memory at    *)
(* mem is in the frame, see DESIGN.md section 6).                           *)
(*                                                                           *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "arm/proofs/libc.ml";;
needs "arm/proofs/snappy/objects.ml";;
needs "common/snappy/snappy_compress.ml";;
needs "arm/proofs/snappy/gcc12_O2/max_compressed_length_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/working_memory_get_hash_table_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_spec.ml";;

let SNAPPY_INTERNAL_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!level inp src out so sk wm mem nw owns pc imp ea el ev rw stackpointer
   returnaddress.
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
     [src,LENGTH inp; wm,48; word pc,libsnappy_rw + libsnappy_rw_size;
      ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s = word(pc + InternalCompress) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [so; sk; word level; wm] s /\
              read (memory :> bytes64 so) s =
                word(pc + vtable_ByteArraySource) /\
              read (memory :> bytes64 (word_add so (word 8))) s = src /\
              read (memory :> bytes64 (word_add so (word 16))) s =
                word(LENGTH inp) /\
              read (memory :> bytes64 sk) s =
                word(pc + vtable_UncheckedByteArraySink) /\
              read (memory :> bytes64 (word_add sk (word 8))) s = out /\
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

let SNAPPY_INTERNAL_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_INTERNAL_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* Memory safety with correctness (DESIGN.md sections 2 and 6): the same     *)
(* with memcpy's contract with memory safety and the _SAFE contracts of the  *)
(* fragment compressors, and the events of the call within the regions that *)
(* it may read and write, in the set form of the heap clients.               *)

let SNAPPY_INTERNAL_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e level inp src out so sk wm mem nw owns pc imp ea el ev rw stackpointer
   returnaddress.
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
     [src,LENGTH inp; wm,48; word pc,libsnappy_rw + libsnappy_rw_size;
      ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s = word(pc + InternalCompress) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [so; sk; word level; wm] s /\
              read (memory :> bytes64 so) s =
                word(pc + vtable_ByteArraySource) /\
              read (memory :> bytes64 (word_add so (word 8))) s = src /\
              read (memory :> bytes64 (word_add so (word 16))) s =
                word(LENGTH inp) /\
              read (memory :> bytes64 sk) s =
                word(pc + vtable_UncheckedByteArraySink) /\
              read (memory :> bytes64 (word_add sk (word 8))) s = out /\
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

let SNAPPY_INTERNAL_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_INTERNAL_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
