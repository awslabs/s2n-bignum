(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::SnappyDecompressor::DecompressAllTags<SnappyDecompressionValidator> *)
(* (snappy.cc) for a decompressor whose reader_ is a ByteArraySource (the     *)
(* flat-buffer entry points), as InternalUncompress<Validator> calls it:     *)
(* after the header, with nothing buffered (ip_ = ip_limit_, peeked_ = 0,     *)
(* eof_ = false), the source at the rest r of the stream, the validator with *)
(* expected_ = m (the length of the header) and produced_ = 0.               *)
(*                                                                           *)
(* It decodes the tags of r, the fast path DecompressBranchless<size_t>      *)
(* (decompress_branchless_ulong_spec.ml) and the slow path in turn, the      *)
(* window refilled by RefillTag (snappy_decompressor_refill_tag_spec.ml),    *)
(* and stores the count of bytes produced at the exit. InternalUncompress     *)
(* then accepts iff eof_ is set and produced_ = expected_: so the result is  *)
(* stated as the pair (eof_, produced_), which is (true, m) iff the tags of r *)
(* decode to m bytes, snappy_decode_tags m r [] <> NONE. The hypothesis      *)
(* LENGTH r < 2^58 (FINDINGS F2) keeps the count from wrapping.              *)
(*                                                                           *)
(* The objects are as in arm/proofs/snappy/decompressor_objects.ml: the      *)
(* decompressor at d with reader_ = src, the ByteArraySource at src with     *)
(* ptr_ = q and left_ = LENGTH r holding the bytes r, the validator at v.    *)
(* Memory written: the fields of the decompressor (d .. d + 40) and          *)
(* scratch_ (d + 41 .. d + 45), as two clauses (RefillTag), ptr_ and left_  *)
(* of the source, produced_, the frame of 96 bytes, and below it the frames  *)
(* of the callees (DecompressBranchless 224 bytes, RefillTag 80 bytes), as   *)
(* two clauses, so that the facts about the frame cross the calls. Read: the *)
(* objects, the input, the stack, the image (the table kLengthMinusOffset),  *)
(* the RW segment (the vtable, the GOT slot of memmove) and memmove's region *)
(* (ea,el). X27 and X28, which DecompressBranchless saves and restores, are *)
(* not in the frame.                                                         *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/snappy/decompressor_objects.ml";;
needs "common/snappy/snappy_validator.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_refill_tag_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/decompress_branchless_ulong_spec.ml";;

(*** The code in the image: see the listing of                             ***)
(*** SnappyDecompressor_DecompressAllTags_SnappyDecompressionValidator in   ***)
(*** layout.ml (0x304 bytes, frame 96 bytes with X19-X25, X29, X30; the    ***)
(*** size of Peek at sp+88). Callees: DecompressBranchless_ulong (0x6a90),  ***)
(*** SnappyDecompressor_RefillTag (0x6b1c, 0x6c4c, 0x6ca8, 0x6cfc), and     ***)
(*** the Skip and Peek of the reader through its vtable (0x6bd0, 0x6be4).   ***)

let SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_VALIDATOR_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range
     "SnappyDecompressor_DecompressAllTags_SnappyDecompressionValidator";
    layout_range "ByteArraySource_Peek"; layout_range "ByteArraySource_Skip"];;

let SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_VALIDATOR_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e d src v q r m ip pc rw sp returnaddress
    x19 x20 x21 x22 x23 x24 x25 x26 x29 ea el ev.
     memmove_correct_safe_contract (imp "memmove") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     LENGTH r < 2 EXP 58 /\ val q + LENGTH r < 2 EXP 64 /\ m < 2 EXP 32 /\
     val d + 48 <= 2 EXP 64 /\
     ALLPAIRS nonoverlapping
      [(d,48); (src,24); (v,16); (word_sub sp (word 320),320)]
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el)] /\
     PAIRWISE nonoverlapping
      [(d,48); (src,24); (v,16); (word_sub sp (word 320),320)] /\
     ALL (nonoverlapping (q,LENGTH r))
      [(d,48); (src,24); (v,16); (word_sub sp (word 320),320)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s =
             word (pc +
              SnappyDecompressor_DecompressAllTags_SnappyDecompressionValidator) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X29 s = x29 /\
           C_ARGUMENTS [d; v] s /\
           read (memory :> bytes64 d) s = src /\
           read (memory :> bytes64 (word_add d (word 8))) s = ip /\
           read (memory :> bytes64 (word_add d (word 16))) s = ip /\
           read (memory :> bytes64 (word_add d (word 32))) s = word 0 /\
           read (memory :> bytes8 (word_add d (word 40))) s = word 0 /\
           read (memory :> bytes64 src) s =
             word_add (word pc) (word vtable_ByteArraySource) /\
           read (memory :> bytes64 (word_add src (word 8))) s = q /\
           read (memory :> bytes64 (word_add src (word 16))) s =
             word(LENGTH r) /\
           read (memory :> bytelist(q,LENGTH r)) s = r /\
           read (memory :> bytes64 v) s = word m /\
           read (memory :> bytes64 (word_add v (word 8))) s = word 0 /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s =
             rw /\
           read (memory :> bytes(ea,el)) s = ev /\
           read events s = e)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X29 s = x29 /\
           read (memory :> bytes64 d) s = src /\
           read (memory :> bytes64 src) s =
             word_add (word pc) (word vtable_ByteArraySource) /\
           read (memory :> bytes64 v) s = word m /\
           (?eofv pr.
              read (memory :> bytes8 (word_add d (word 40))) s =
                word(bitval eofv) /\
              read (memory :> bytes64 (word_add v (word 8))) s = pr /\
              (eofv /\ pr = word m <=>
               ~(snappy_decode_tags m r [] = NONE))) /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2
                 (memrange(d,48) UNION memrange(src,24) UNION
                  memrange(v,16) UNION memrange(q,LENGTH r) UNION
                  memrange(word_sub sp (word 320),320) UNION
                  memrange(word pc,libsnappy_size) UNION
                  memrange(word(pc + libsnappy_rw),libsnappy_rw_size) UNION
                  memrange(ea,el))
                 (memrange(d,48) UNION memrange(src,24) UNION
                  memrange(v,16) UNION
                  memrange(word_sub sp (word 320),320)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X25; X26; X29;
                  X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 96),96)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 320),224)] ,,
       MAYCHANGE [memory :> bytes(d,41)] ,,
       MAYCHANGE [memory :> bytes(word_add d (word 41),5)] ,,
       MAYCHANGE [memory :> bytes(word_add src (word 8),16)] ,,
       MAYCHANGE [memory :> bytes(word_add v (word 8),8)])`;;

let SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_VALIDATOR_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_VALIDATOR_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
