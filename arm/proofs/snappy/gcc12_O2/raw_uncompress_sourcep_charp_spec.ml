(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::RawUncompress(Source* compressed, char* uncompressed) (snappy.cc) *)
(* for a ByteArraySource of the image at src holding the compressed stream  *)
(* l at inp (ptr_ = inp, left_ = LENGTH l), as RawUncompress(const char* p, *)
(* size_t n, char* out) calls it. It builds a SnappyArrayWriter for out and *)
(* a SnappyDecompressor on its stack, reads the header                       *)
(* (ReadUncompressedLength, inlined: virtual Peek and Skip(1) for each      *)
(* byte), calls Available() and                                              *)
(* DecompressAllTags<SnappyArrayWriter>, and returns eof_ && op_ ==         *)
(* op_limit_; the destructor of the decompressor (inlined) skips the peeked *)
(* bytes. The result is snappy_decode l <> NONE, and then out holds the      *)
(* decoded bytes.                                                            *)
(*                                                                           *)
(* The output region is (out, outlen) for any outlen that is at least the    *)
(* header value (if the header is valid): only bytes of [out, out + m) are   *)
(* written, m the header value (nothing if the header is invalid). As for    *)
(* DecompressAllTags, 17 <= val out (IncrementalCopy), the output ends more *)
(* than 64 bytes below the top of the address space (IncrementalCopy        *)
(* compares op + 16, op + 32 and op + 48 with op_limit) and the input does   *)
(* not reach it.                                                             *)
(*                                                                           *)
(* The frame is 176 bytes: the saved X19-X26, X29, X30 and Peek's count     *)
(* (+0 .. +95), the writer (+96: base_ and op_, +112: op_limit_ and         *)
(* op_limit_min_slop_) and the decompressor (+128, its fields and scratch_), *)
(* one clause each in the frame, as DecompressAllTags writes only some of    *)
(* them; the callees' area is the 400 bytes of DecompressAllTags below it.   *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_spec.ml";;

(*** The code in the image: see the listing of RawUncompress__Sourcep_charp ***)
(*** in layout.ml (0x144 bytes).                                           ***)

let SNAPPY_RAW_UNCOMPRESS_SOURCEP_CHARP_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "RawUncompress__Sourcep_charp";
    layout_range "ByteArraySource_Available";
    layout_range "ByteArraySource_Peek"; layout_range "ByteArraySource_Skip"];;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety.                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_RAW_UNCOMPRESS_SOURCEP_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e src inp l out outlen pc rw sp returnaddress
    x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ea el ev.
     memcpy_correct_safe_contract (imp "memcpy") ea el ev /\
     memmove_correct_safe_contract (imp "memmove") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     val inp + LENGTH l < 2 EXP 64 /\ LENGTH l < 2 EXP 63 /\
     17 <= val out /\ val out + outlen + 64 < 2 EXP 64 /\
     (!m. snappy_header l = SOME m ==> m <= outlen) /\
     ALLPAIRS nonoverlapping
      [(src,24); (out,outlen); (word_sub sp (word 576),576)]
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el)] /\
     ALL (nonoverlapping (src,24))
      [(out,outlen); (word_sub sp (word 576),576)] /\
     nonoverlapping (out,outlen) (word_sub sp (word 576),576) /\
     ALL (nonoverlapping (inp,LENGTH l))
      [(src,24); (out,outlen); (word_sub sp (word 576),576)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + RawUncompress__Sourcep_charp) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           C_ARGUMENTS [src; out] s /\
           read (memory :> bytes64 src) s =
             word_add (word pc) (word vtable_ByteArraySource) /\
           read (memory :> bytes64 (word_add src (word 8))) s = inp /\
           read (memory :> bytes64 (word_add src (word 16))) s =
             word(LENGTH l) /\
           read (memory :> bytelist(inp,LENGTH l)) s = l /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s =
             rw /\
           read (memory :> bytes(ea,el)) s = ev /\
           read events s = e)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           C_RETURN s = word(bitval(~(snappy_decode l = NONE))) /\
           (!x. snappy_decode l = SOME x
                ==> read (memory :> bytelist(out,LENGTH x)) s = x) /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2
                 (memrange(src,24) UNION memrange(out,outlen) UNION
                  memrange(word_sub sp (word 576),576) UNION
                  memrange(inp,LENGTH l) UNION
                  memrange(word pc,libsnappy_size) UNION
                  memrange(word(pc + libsnappy_rw),libsnappy_rw_size) UNION
                  memrange(ea,el))
                 (memrange(src,24) UNION memrange(out,outlen) UNION
                  memrange(word_sub sp (word 576),576)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27;
                  X28; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 176),96)] ,,
       MAYCHANGE [memory :> bytes(word_add (word_sub sp (word 176)) (word 96),
                                   16)] ,,
       MAYCHANGE [memory :> bytes(word_add (word_sub sp (word 176)) (word 112),
                                   16)] ,,
       MAYCHANGE [memory :> bytes(word_add (word_sub sp (word 176)) (word 128),
                                   41)] ,,
       MAYCHANGE [memory :> bytes(word_add (word_sub sp (word 176)) (word 169),
                                   5)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 576),400)] ,,
       MAYCHANGE [memory :> bytes(word_add src (word 8),16)] ,,
       MAYCHANGE [memory :> bytes(out,outlen)])`;;

let SNAPPY_RAW_UNCOMPRESS_SOURCEP_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_RAW_UNCOMPRESS_SOURCEP_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
