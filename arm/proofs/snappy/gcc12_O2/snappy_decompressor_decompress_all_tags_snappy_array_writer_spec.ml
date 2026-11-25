(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::SnappyDecompressor::DecompressAllTags<SnappyArrayWriter>(writer)  *)
(* (snappy.cc) for a decompressor whose reader_ is a ByteArraySource of the  *)
(* image, as RawUncompress(Source*, char* out) calls it after the header:   *)
(* the decompressor at d has no buffered bytes (ip_ = ip_limit_ = ip),      *)
(* nothing peeked (peeked_ = 0), eof_ = false; the source at src holds the  *)
(* bytes inp of the stream after the header (ptr_ = q, left_ = LENGTH inp);  *)
(* the writer at wr is a fresh SnappyArrayWriter for the m bytes at out:    *)
(*                                                                           *)
(*    +0   base_               out                                           *)
(*    +8   op_                 out (the next byte to write)                  *)
(*    +16  op_limit_           out + m                                       *)
(*    +24  op_limit_min_slop_  out + m - min(m, 63)                          *)
(*                                                                           *)
(* It decodes the tags of inp into the output (common/snappy/               *)
(* snappy_format.ml): at the return, eof_ and op_ = op_limit_ both hold iff  *)
(* snappy_decode_tags m inp [] succeeds, and then the m bytes at out are its *)
(* result. On failure the output holds unspecified bytes (FINDINGS F4: only *)
(* bytes of [out, out + m) are written). The caller (RawUncompress) tests    *)
(* eof_ and op_ == op_limit_; it then calls reader_->Skip(peeked_), so       *)
(* reader_ is given in the postcondition (peeked_ may be anything).          *)
(*                                                                           *)
(* Hypotheses: m < 2^32 (a header value); 17 <= val out, which             *)
(* IncrementalCopy needs (it computes op_limit_ - 17 as a pointer) and which *)
(* makes base_ nonzero, so the fast path DecompressBranchless always runs;  *)
(* the output ends more than 64 bytes below the top of the address space   *)
(* (IncrementalCopy compares op_limit with op + 16, op + 32 and op + 48,    *)
(* which must not wrap: with out + m closer to 2^64 a copy with a short     *)
(* pattern can store at a wrapped address); and the decompressor is 8-byte  *)
(* aligned, as its type requires (scratch_ at d + 41 is then not split by   *)
(* the top of the address space: the code compares ip with                  *)
(* ip_limit_min_maxtaglen_ = d + 41 in the scratch state, and DecompressBr- *)
(* anchless needs d + 41 + 5 not to wrap). The input may be anywhere except *)
(* the regions written.                                                     *)
(*                                                                           *)
(* Callees: DecompressBranchless<char*> (its frame of 240 bytes and that of  *)
(* MemCopy64, 48, below it), RefillTag (80), IncrementalCopy (none), memcpy  *)
(* and memmove through the PLT, and the virtual Skip/Peek of the source     *)
(* (leaf functions, stepped through). The function's own frame is 112 bytes *)
(* (X19-X30 saved), the callees' area the 288 bytes below it. The frame     *)
(* lists the decompressor as its fields (d, 41 bytes) and scratch_ (d + 41,  *)
(* 5), and only op_ of the writer, which is all that it writes there.        *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/snappy/decompressor_objects.ml";;

(*** The code in the image: see the listing of                             ***)
(*** SnappyDecompressor_DecompressAllTags_SnappyArrayWriter in layout.ml    ***)
(*** (0x3fc bytes).                                                        ***)

let SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_SNAPPY_ARRAY_WRITER_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "SnappyDecompressor_DecompressAllTags_SnappyArrayWriter";
    layout_range "plt_memmove"; layout_range "plt_memcpy";
    layout_range "ByteArraySource_Peek"; layout_range "ByteArraySource_Skip"];;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety.                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_SNAPPY_ARRAY_WRITER_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e d wr src q inp ip out m pc rw sp returnaddress
    x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ea el ev.
     memcpy_correct_safe_contract (imp "memcpy") ea el ev /\
     memmove_correct_safe_contract (imp "memmove") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\ aligned 8 d /\
     m < 2 EXP 32 /\ 17 <= val out /\ val out + m + 64 < 2 EXP 64 /\
     val q + LENGTH inp < 2 EXP 64 /\ LENGTH inp < 2 EXP 63 /\
     ALLPAIRS nonoverlapping
      [(d,48); (wr,32); (src,24); (out,m); (word_sub sp (word 400),400)]
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el)] /\
     ALL (nonoverlapping (d,48))
      [(wr,32); (src,24); (out,m); (word_sub sp (word 400),400)] /\
     ALL (nonoverlapping (wr,32))
      [(src,24); (out,m); (word_sub sp (word 400),400)] /\
     ALL (nonoverlapping (src,24)) [(out,m); (word_sub sp (word 400),400)] /\
     nonoverlapping (out,m) (word_sub sp (word 400),400) /\
     ALL (nonoverlapping (q,LENGTH inp))
      [(d,48); (wr,32); (src,24); (out,m); (word_sub sp (word 400),400)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s =
             word (pc + SnappyDecompressor_DecompressAllTags_SnappyArrayWriter) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           C_ARGUMENTS [d; wr] s /\
           read (memory :> bytes64 d) s = src /\
           read (memory :> bytes64 (word_add d (word 8))) s = ip /\
           read (memory :> bytes64 (word_add d (word 16))) s = ip /\
           read (memory :> bytes64 (word_add d (word 32))) s = word 0 /\
           read (memory :> bytes8 (word_add d (word 40))) s = word 0 /\
           read (memory :> bytes64 src) s =
             word_add (word pc) (word vtable_ByteArraySource) /\
           read (memory :> bytes64 (word_add src (word 8))) s = q /\
           read (memory :> bytes64 (word_add src (word 16))) s =
             word(LENGTH inp) /\
           read (memory :> bytelist(q,LENGTH inp)) s = inp /\
           read (memory :> bytes64 wr) s = out /\
           read (memory :> bytes64 (word_add wr (word 8))) s = out /\
           read (memory :> bytes64 (word_add wr (word 16))) s =
             word_add out (word m) /\
           read (memory :> bytes64 (word_add wr (word 24))) s =
             word_sub (word_add out (word m)) (word(MIN m 63)) /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s =
             rw /\
           read (memory :> bytes(ea,el)) s = ev /\
           read events s = e)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           read (memory :> bytes64 d) s = src /\
           (?ok. read (memory :> bytes8 (word_add d (word 40))) s =
                   word(bitval ok) /\
                 (ok /\
                  read (memory :> bytes64 (word_add wr (word 8))) s =
                  word_add out (word m) <=>
                  ~(snappy_decode_tags m inp [] = NONE))) /\
           (!x. snappy_decode_tags m inp [] = SOME x
                ==> read (memory :> bytelist(out,m)) s = x) /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2
                 (memrange(d,48) UNION memrange(wr,32) UNION
                  memrange(src,24) UNION memrange(out,m) UNION
                  memrange(word_sub sp (word 400),400) UNION
                  memrange(q,LENGTH inp) UNION
                  memrange(word pc,libsnappy_size) UNION
                  memrange(word(pc + libsnappy_rw),libsnappy_rw_size) UNION
                  memrange(ea,el))
                 (memrange(d,48) UNION memrange(wr,32) UNION
                  memrange(src,24) UNION memrange(out,m) UNION
                  memrange(word_sub sp (word 400),400)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28;
                  X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 112),112)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 400),288)] ,,
       MAYCHANGE [memory :> bytes(d,41)] ,,
       MAYCHANGE [memory :> bytes(word_add d (word 41),5)] ,,
       MAYCHANGE [memory :> bytes(word_add src (word 8),16)] ,,
       MAYCHANGE [memory :> bytes(word_add wr (word 8),8)] ,,
       MAYCHANGE [memory :> bytes(out,m)])`;;

let SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_SNAPPY_ARRAY_WRITER_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_SNAPPY_ARRAY_WRITER_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
