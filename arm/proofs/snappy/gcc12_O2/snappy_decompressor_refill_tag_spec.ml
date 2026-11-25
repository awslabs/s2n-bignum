(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::SnappyDecompressor::RefillTag() (snappy.cc) for a decompressor    *)
(* whose reader_ is a ByteArraySource of the image (the flat-buffer entry    *)
(* points: RawUncompress, IsValidCompressedBuffer, ...), as the slow path of *)
(* DecompressAllTags calls it. The objects are as in                         *)
(* arm/proofs/snappy/decompressor_objects.ml: the decompressor at d, with    *)
(* reader_ = src, ip_ = ip, ip_limit_ = lim, peeked_ = pk, scratch_ at       *)
(* d + 41, and the ByteArraySource at src with ptr_ = p, left_ = n. The     *)
(* virtual calls of Skip and Peek go through the vtable of the image to the  *)
(* methods ByteArraySource_Skip and ByteArraySource_Peek.                    *)
(*                                                                           *)
(* RefillTag makes the bytes of the next tag (snappy_tag_needed of its first *)
(* byte, common/snappy/snappy_decompressor.ml) available at ip_, and returns *)
(* true, or returns false at the end of the input (then eof_ = true) or if  *)
(* the input ends inside the tag (eof_ = false). A window of fewer than 5    *)
(* bytes (kMaximumTagLength) is moved into scratch_ and the reader is then   *)
(* used up (its peeked bytes skipped), so that the code may read 5 bytes at  *)
(* ip_; a window of at least 5 bytes stays where it is.                      *)
(*                                                                           *)
(* Two theorems, for the two states in which DecompressAllTags calls it:    *)
(*                                                                           *)
(*  _EMPTY: ip_ = ip_limit_ (no buffered bytes, e.g. at the start, or once   *)
(*    the buffered bytes are used up). RefillTag skips the k peeked bytes   *)
(*    and peeks the rest of the source, rest, the n - k bytes at p + k.      *)
(*    Let r = n - k = LENGTH rest. It returns snappy_refill_ok rest, sets    *)
(*    eof_ to rest = [], and:                                                *)
(*      r >= 5: ip_ = p + k, ip_limit_ = p + n, peeked_ = r, and the source  *)
(*              is at (p + k, r);                                            *)
(*      r < 5:  the source is at (p + n, 0), peeked_ = 0, scratch_ holds     *)
(*              rest, and if it returns true, ip_ = d + 41 and               *)
(*              ip_limit_ = d + 41 + r.                                      *)
(*                                                                           *)
(*  _WINDOW: the r = LENGTH w > 0 bytes w are buffered at ip, ip_limit_ =    *)
(*    ip + r, and the source has no unpeeked bytes (peeked_ = n = left_).    *)
(*    It returns snappy_refill_ok w, eof_ stays false, and:                  *)
(*      r >= 5: nothing changes;                                             *)
(*      r < 5:  as for _EMPTY with rest = w.                                 *)
(*                                                                           *)
(* In both the window may be anywhere that the stack frame of RefillTag (80  *)
(* bytes) does not overlap, e.g. in the input or in scratch_ itself (memmove *)
(* allows the overlap). The function writes the decompressor (its fields,   *)
(* d .. d + 40, and scratch_, d + 41 .. d + 45, as two clauses of the frame, *)
(* so that the facts about the fields cross the call of memmove), ptr_ and  *)
(* left_ of the source and its frame; it reads them, the vptr and the       *)
(* vtable (in the RW segment), the window, and memmove's region (ea,el).     *)
(*                                                                           *)
(* With a ByteArraySource the loop of RefillTag that stitches a tag from     *)
(* several fragments of the reader (memcpy) never runs more than its test:  *)
(* after the peeked bytes are skipped the source is empty.                   *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/snappy/decompressor_objects.ml";;

(*** The code in the image: see the listing of SnappyDecompressor_RefillTag ***)
(*** in layout.ml (0x1b4 bytes; frame 80 bytes with X19-X24, X29, X30).    ***)

let SNAPPY_DECOMPRESSOR_REFILL_TAG_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "SnappyDecompressor_RefillTag"; layout_range "plt_memmove";
    layout_range "ByteArraySource_Peek"; layout_range "ByteArraySource_Skip"];;

(* ------------------------------------------------------------------------- *)
(* No buffered bytes.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_DECOMPRESSOR_REFILL_TAG_EMPTY_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e d src p n k ip rest pc rw sp returnaddress
    x19 x20 x21 x22 x23 x24 x29 ea el ev.
     memmove_correct_safe_contract (imp "memmove") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     k <= n /\ n < 2 EXP 64 /\ LENGTH rest = n - k /\
     ALLPAIRS nonoverlapping
      [(d,48); (src,24); (word_sub sp (word 80),80)]
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el)] /\
     nonoverlapping (d,48) (src,24) /\
     ALL (nonoverlapping (word_sub sp (word 80),80)) [(d,48); (src,24)] /\
     ALL (nonoverlapping (word_add p (word k),n - k))
      [(d,48); (src,24); (word_sub sp (word 80),80)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + SnappyDecompressor_RefillTag) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X29 s = x29 /\
           C_ARGUMENTS [d] s /\
           read (memory :> bytes64 d) s = src /\
           read (memory :> bytes64 (word_add d (word 8))) s = ip /\
           read (memory :> bytes64 (word_add d (word 16))) s = ip /\
           read (memory :> bytes64 (word_add d (word 32))) s = word k /\
           read (memory :> bytes64 src) s =
             word_add (word pc) (word vtable_ByteArraySource) /\
           read (memory :> bytes64 (word_add src (word 8))) s = p /\
           read (memory :> bytes64 (word_add src (word 16))) s = word n /\
           read (memory :> bytelist(word_add p (word k),n - k)) s = rest /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s =
             rw /\
           read (memory :> bytes(ea,el)) s = ev /\
           read events s = e)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X29 s = x29 /\
           C_RETURN s = word(bitval(snappy_refill_ok rest)) /\
           read (memory :> bytes64 d) s = src /\
           read (memory :> bytes64 (word_add d (word 32))) s =
             (if n - k < 5 then word 0 else word(n - k)) /\
           read (memory :> bytes8 (word_add d (word 40))) s =
             word(bitval(rest = [])) /\
           read (memory :> bytes64 (word_add src (word 8))) s =
             (if n - k < 5 then word_add p (word n) else word_add p (word k)) /\
           read (memory :> bytes64 (word_add src (word 16))) s =
             (if n - k < 5 then word 0 else word(n - k)) /\
           (snappy_refill_ok rest
            ==> read (memory :> bytes64 (word_add d (word 8))) s =
                  (if n - k < 5 then word_add d (word 41)
                   else word_add p (word k)) /\
                read (memory :> bytes64 (word_add d (word 16))) s =
                  (if n - k < 5 then word_add d (word (41 + (n - k)))
                   else word_add p (word n))) /\
           (n - k < 5
            ==> read (memory :> bytelist(word_add d (word 41),n - k)) s =
                rest) /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2
                 (memrange(d,48) UNION memrange(src,24) UNION
                  memrange(word_sub sp (word 80),80) UNION
                  memrange(word_add p (word k),n - k) UNION
                  memrange(word(pc + libsnappy_rw),libsnappy_rw_size) UNION
                  memrange(ea,el))
                 (memrange(d,48) UNION memrange(src,24) UNION
                  memrange(word_sub sp (word 80),80)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 80),80)] ,,
       MAYCHANGE [memory :> bytes(d,41)] ,,
       MAYCHANGE [memory :> bytes(word_add d (word 41),5)] ,,
       MAYCHANGE [memory :> bytes(word_add src (word 8),16)])`;;

let SNAPPY_DECOMPRESSOR_REFILL_TAG_EMPTY_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_DECOMPRESSOR_REFILL_TAG_EMPTY_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* A nonempty window, the source fully peeked.                               *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_DECOMPRESSOR_REFILL_TAG_WINDOW_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e d src p n ip w pc rw sp returnaddress
    x19 x20 x21 x22 x23 x24 x29 ea el ev.
     memmove_correct_safe_contract (imp "memmove") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     ~(w = []) /\ LENGTH w < 2 EXP 64 /\
     ALLPAIRS nonoverlapping
      [(d,48); (src,24); (word_sub sp (word 80),80)]
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el)] /\
     nonoverlapping (d,48) (src,24) /\
     ALL (nonoverlapping (word_sub sp (word 80),80))
      [(d,48); (src,24); (ip,LENGTH w)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + SnappyDecompressor_RefillTag) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X29 s = x29 /\
           C_ARGUMENTS [d] s /\
           read (memory :> bytes64 d) s = src /\
           read (memory :> bytes64 (word_add d (word 8))) s = ip /\
           read (memory :> bytes64 (word_add d (word 16))) s =
             word_add ip (word(LENGTH w)) /\
           read (memory :> bytes64 (word_add d (word 32))) s = n /\
           read (memory :> bytes8 (word_add d (word 40))) s = word 0 /\
           read (memory :> bytes64 src) s =
             word_add (word pc) (word vtable_ByteArraySource) /\
           read (memory :> bytes64 (word_add src (word 8))) s = p /\
           read (memory :> bytes64 (word_add src (word 16))) s = n /\
           read (memory :> bytelist(ip,LENGTH w)) s = w /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s =
             rw /\
           read (memory :> bytes(ea,el)) s = ev /\
           read events s = e)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X29 s = x29 /\
           C_RETURN s = word(bitval(snappy_refill_ok w)) /\
           read (memory :> bytes64 d) s = src /\
           read (memory :> bytes64 (word_add d (word 32))) s =
             (if LENGTH w < 5 then word 0 else n) /\
           read (memory :> bytes8 (word_add d (word 40))) s = word 0 /\
           read (memory :> bytes64 (word_add src (word 8))) s =
             (if LENGTH w < 5 then word_add p n else p) /\
           read (memory :> bytes64 (word_add src (word 16))) s =
             (if LENGTH w < 5 then word 0 else n) /\
           (snappy_refill_ok w
            ==> read (memory :> bytes64 (word_add d (word 8))) s =
                  (if LENGTH w < 5 then word_add d (word 41) else ip) /\
                read (memory :> bytes64 (word_add d (word 16))) s =
                  (if LENGTH w < 5 then word_add d (word (41 + LENGTH w))
                   else word_add ip (word(LENGTH w)))) /\
           (LENGTH w < 5
            ==> read (memory :> bytelist(word_add d (word 41),LENGTH w)) s =
                w) /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2
                 (memrange(d,48) UNION memrange(src,24) UNION
                  memrange(word_sub sp (word 80),80) UNION
                  memrange(ip,LENGTH w) UNION
                  memrange(word(pc + libsnappy_rw),libsnappy_rw_size) UNION
                  memrange(ea,el))
                 (memrange(d,48) UNION memrange(src,24) UNION
                  memrange(word_sub sp (word 80),80)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 80),80)] ,,
       MAYCHANGE [memory :> bytes(d,41)] ,,
       MAYCHANGE [memory :> bytes(word_add d (word 41),5)] ,,
       MAYCHANGE [memory :> bytes(word_add src (word 8),16)])`;;

let SNAPPY_DECOMPRESSOR_REFILL_TAG_WINDOW_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_DECOMPRESSOR_REFILL_TAG_WINDOW_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
