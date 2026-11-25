(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy_uncompress(const char* compressed, size_t compressed_length,       *)
(* char* uncompressed, size_t* uncompressed_length) of the C interface       *)
(* (snappy-c.cc), for any input bytes l and an output buffer of the size     *)
(* ulen that *uncompressed_length holds on entry:                            *)
(*                                                                           *)
(*  - the status is snappy_uncompress_status l (val ulen)                    *)
(*    (common/snappy/snappy_format.ml): SNAPPY_OK (0) iff snappy_decode l =  *)
(*    SOME x with LENGTH x <= ulen, SNAPPY_BUFFER_TOO_SMALL (2) iff the      *)
(*    header is valid and above ulen, SNAPPY_INVALID_INPUT (1) otherwise;    *)
(*  - on SNAPPY_OK the output holds x and *uncompressed_length = LENGTH x;   *)
(*  - otherwise *uncompressed_length is not written (FINDINGS F4);           *)
(*  - it writes only the ulen bytes of the output (on failure some of them   *)
(*    may have been written), *uncompressed_length and its stack.            *)
(*                                                                           *)
(* It calls GetUncompressedLength (the header, into a local), compares it   *)
(* with *uncompressed_length and calls RawUncompress(const char*, size_t,   *)
(* char* out). As for RawUncompress, 17 <= val out (IncrementalCopy), the   *)
(* output ends more than 64 bytes below the top of the address space and the *)
(* input does not reach it.                                                  *)
(*                                                                           *)
(* The frame is 64 bytes: the saved X19-X22, X29, X30 (+0 .. +55) and the    *)
(* header value (+56); the callees' area is the 640 bytes of RawUncompress  *)
(* below it.                                                                 *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/get_uncompressed_length_charp_ulong_ulongp_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/raw_uncompress_charp_ulong_charp_spec.ml";;

(*** The code in the image: see the listing of c_snappy_uncompress in       ***)
(*** layout.ml (0x8c bytes).                                               ***)

let SNAPPY_C_UNCOMPRESS_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "c_snappy_uncompress"];;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety.                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_C_UNCOMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e inp n l out ulenp ulen pc rw sp returnaddress
    x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ea el ev.
     memcpy_correct_safe_contract (imp "memcpy") ea el ev /\
     memmove_correct_safe_contract (imp "memmove") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     val n = LENGTH l /\ val inp + LENGTH l < 2 EXP 64 /\
     LENGTH l < 2 EXP 63 /\
     17 <= val out /\ val out + val ulen + 64 < 2 EXP 64 /\
     ALLPAIRS nonoverlapping
      [(out,val ulen); (ulenp,8); (word_sub sp (word 704),704)]
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el)] /\
     nonoverlapping (out,val ulen) (ulenp,8) /\
     ALL (nonoverlapping (word_sub sp (word 704),704))
      [(out,val ulen); (ulenp,8)] /\
     ALL (nonoverlapping (inp,LENGTH l))
      [(out,val ulen); (ulenp,8); (word_sub sp (word 704),704)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + c_snappy_uncompress) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           C_ARGUMENTS [inp; n; out; ulenp] s /\
           read (memory :> bytelist(inp,LENGTH l)) s = l /\
           read (memory :> bytes64 ulenp) s = ulen /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s =
             rw /\
           read (memory :> bytes(ea,el)) s = ev /\
           read events s = e)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           C_RETURN s = word(snappy_uncompress_status l (val ulen)) /\
           (!x. snappy_decode l = SOME x /\ LENGTH x <= val ulen
                ==> read (memory :> bytelist(out,LENGTH x)) s = x /\
                    read (memory :> bytes64 ulenp) s = word(LENGTH x)) /\
           (~(snappy_uncompress_status l (val ulen) = 0)
            ==> read (memory :> bytes64 ulenp) s = ulen) /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2
                 (memrange(inp,LENGTH l) UNION memrange(out,val ulen) UNION
                  memrange(ulenp,8) UNION
                  memrange(word_sub sp (word 704),704) UNION
                  memrange(word pc,libsnappy_size) UNION
                  memrange(word(pc + libsnappy_rw),libsnappy_rw_size) UNION
                  memrange(ea,el))
                 (memrange(out,val ulen) UNION memrange(ulenp,8) UNION
                  memrange(word_sub sp (word 704),704)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27;
                  X28; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 64),56)] ,,
       MAYCHANGE [memory :> bytes(word_add (word_sub sp (word 64)) (word 56),
                                   8)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 704),640)] ,,
       MAYCHANGE [memory :> bytes(out,val ulen)] ,,
       MAYCHANGE [memory :> bytes(ulenp,8)])`;;

let SNAPPY_C_UNCOMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_C_UNCOMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness alone.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_C_UNCOMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!inp n l out ulenp ulen pc rw sp returnaddress
    x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ea el ev.
     memcpy_correct_safe_contract (imp "memcpy") ea el ev /\
     memmove_correct_safe_contract (imp "memmove") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     val n = LENGTH l /\ val inp + LENGTH l < 2 EXP 64 /\
     LENGTH l < 2 EXP 63 /\
     17 <= val out /\ val out + val ulen + 64 < 2 EXP 64 /\
     ALLPAIRS nonoverlapping
      [(out,val ulen); (ulenp,8); (word_sub sp (word 704),704)]
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el)] /\
     nonoverlapping (out,val ulen) (ulenp,8) /\
     ALL (nonoverlapping (word_sub sp (word 704),704))
      [(out,val ulen); (ulenp,8)] /\
     ALL (nonoverlapping (inp,LENGTH l))
      [(out,val ulen); (ulenp,8); (word_sub sp (word 704),704)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + c_snappy_uncompress) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           C_ARGUMENTS [inp; n; out; ulenp] s /\
           read (memory :> bytelist(inp,LENGTH l)) s = l /\
           read (memory :> bytes64 ulenp) s = ulen /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s =
             rw /\
           read (memory :> bytes(ea,el)) s = ev)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           C_RETURN s = word(snappy_uncompress_status l (val ulen)) /\
           (!x. snappy_decode l = SOME x /\ LENGTH x <= val ulen
                ==> read (memory :> bytelist(out,LENGTH x)) s = x /\
                    read (memory :> bytes64 ulenp) s = word(LENGTH x)) /\
           (~(snappy_uncompress_status l (val ulen) = 0)
            ==> read (memory :> bytes64 ulenp) s = ulen))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27;
                  X28; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 64),56)] ,,
       MAYCHANGE [memory :> bytes(word_add (word_sub sp (word 64)) (word 56),
                                   8)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 704),640)] ,,
       MAYCHANGE [memory :> bytes(out,val ulen)] ,,
       MAYCHANGE [memory :> bytes(ulenp,8)])`;;

let SNAPPY_C_UNCOMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_C_UNCOMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
