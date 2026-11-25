(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::InternalUncompress<SnappyDecompressionValidator>(Source* r,       *)
(* SnappyDecompressionValidator* writer) [clone .constprop.0] (snappy.cc),   *)
(* for a ByteArraySource reader at src holding the n bytes l at inp, and a   *)
(* validator at v with produced_ = 0 (as IsValidCompressedBuffer builds      *)
(* them): true iff l is a valid compressed stream, snappy_decode l <> NONE   *)
(* (common/snappy/snappy_format.ml).                                         *)
(*                                                                           *)
(* It builds a SnappyDecompressor on its stack (at sp - 48), reads the       *)
(* header with ReadUncompressedLength (inlined: at most 5 bytes, each a      *)
(* virtual Peek, a load and a virtual Skip(1), the check of the 5th byte by  *)
(* the table LeftShiftOverflows_masks in the image, FINDINGS F5), sets       *)
(* expected_ to its value m, calls the reader's Available (the result is not *)
(* used) and DecompressAllTags<Validator>                                    *)
(* (snappy_decompressor_decompress_all_tags_validator_spec.ml), and returns  *)
(* eof_ && expected_ == produced_; the destructor of the decompressor (also  *)
(* inlined) skips the peeked bytes. LENGTH l < 2^58 (FINDINGS F2).           *)
(*                                                                           *)
(* Memory written: ptr_ and left_ of the source, the validator, the frame of *)
(* 144 bytes (three clauses: the saved registers and the size of Peek, the  *)
(* decompressor's fields and its scratch_, which DecompressAllTags writes)   *)
(* and the 320 bytes of stack of DecompressAllTags below it.                 *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/snappy/decompressor_objects.ml";;
needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_validator_spec.ml";;

(*** The code in the image: see the listing of                             ***)
(*** InternalUncompress_SnappyDecompressionValidator in layout.ml (0x128    ***)
(*** bytes, frame 144 bytes with X19-X26, X29, X30; the decompressor at     ***)
(*** sp+96, the size of Peek at sp+88). The header loop is at 0x52a8 (x19   ***)
(*** the shift, 0, 7, .., 35, also the index of LeftShiftOverflows_masks,   ***)
(*** reached as rodata_pattern_generation_masks + 0x200).                   ***)

let SNAPPY_INTERNAL_UNCOMPRESS_VALIDATOR_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "InternalUncompress_SnappyDecompressionValidator";
    layout_range "ByteArraySource_Available";
    layout_range "ByteArraySource_Peek"; layout_range "ByteArraySource_Skip"];;

let SNAPPY_INTERNAL_UNCOMPRESS_VALIDATOR_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e src v inp l pc rw sp returnaddress
    x19 x20 x21 x22 x23 x24 x25 x26 x29 ea el ev.
     memmove_correct_safe_contract (imp "memmove") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\ 464 <= val sp /\
     LENGTH l < 2 EXP 58 /\ val inp + LENGTH l < 2 EXP 64 /\
     ALLPAIRS nonoverlapping
      [(src,24); (v,16); (word_sub sp (word 464),464)]
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el)] /\
     PAIRWISE nonoverlapping
      [(src,24); (v,16); (word_sub sp (word 464),464)] /\
     ALL (nonoverlapping (inp,LENGTH l))
      [(src,24); (v,16); (word_sub sp (word 464),464)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s =
             word (pc + InternalUncompress_SnappyDecompressionValidator) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X29 s = x29 /\
           C_ARGUMENTS [src; v] s /\
           read (memory :> bytes64 src) s =
             word_add (word pc) (word vtable_ByteArraySource) /\
           read (memory :> bytes64 (word_add src (word 8))) s = inp /\
           read (memory :> bytes64 (word_add src (word 16))) s =
             word(LENGTH l) /\
           read (memory :> bytelist(inp,LENGTH l)) s = l /\
           read (memory :> bytes64 (word_add v (word 8))) s = word 0 /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s =
             rw /\
           read (memory :> bytes(ea,el)) s = ev /\
           read events s = e)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X29 s = x29 /\
           C_RETURN s = word(bitval(~(snappy_decode l = NONE))) /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2
                 (memrange(src,24) UNION memrange(v,16) UNION
                  memrange(inp,LENGTH l) UNION
                  memrange(word_sub sp (word 464),464) UNION
                  memrange(word pc,libsnappy_size) UNION
                  memrange(word(pc + libsnappy_rw),libsnappy_rw_size) UNION
                  memrange(ea,el))
                 (memrange(src,24) UNION memrange(v,16) UNION
                  memrange(word_sub sp (word 464),464)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X25; X26; X29;
                  X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 144),96)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 48),41)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 7),5)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 464),320)] ,,
       MAYCHANGE [memory :> bytes(word_add src (word 8),16)] ,,
       MAYCHANGE [memory :> bytes(v,16)])`;;

let SNAPPY_INTERNAL_UNCOMPRESS_VALIDATOR_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_INTERNAL_UNCOMPRESS_VALIDATOR_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
