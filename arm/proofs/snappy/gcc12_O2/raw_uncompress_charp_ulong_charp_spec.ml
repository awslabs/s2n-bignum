(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::RawUncompress(const char* compressed, size_t compressed_length,  *)
(* char* uncompressed) (snappy.cc): for the n bytes l at inp, it builds a    *)
(* ByteArraySource on its stack and calls RawUncompress(Source* r, char* o); *)
(* it returns snappy_decode l <> NONE, and then the output holds the        *)
(* decoded bytes. Only bytes of [out, out + m) are written, m the header    *)
(* value (FINDINGS F4), so the output region is (out, outlen) for any       *)
(* outlen that is at least the header value. As for DecompressAllTags,      *)
(* 17 <= val out (IncrementalCopy), the output ends more than 64 bytes below *)
(* the top of the address space and the input does not reach it.            *)
(*                                                                           *)
(* The frame is 64 bytes: the saved X19, X29, X30 (+0 .. +39) and the        *)
(* ByteArraySource (+40, 24 bytes); the callees' area is the 576 bytes of    *)
(* RawUncompress(Source* r, char* o) below it.                               *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/raw_uncompress_sourcep_charp_spec.ml";;

(*** The code in the image: see the listing of                             ***)
(*** RawUncompress__charp_ulong_charp in layout.ml (0x54 bytes).            ***)

let SNAPPY_RAW_UNCOMPRESS_CHARP_ULONG_CHARP_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "RawUncompress__charp_ulong_charp";
    layout_range "ByteArraySource_dtor"; layout_range "Source_dtor"];;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety.                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_RAW_UNCOMPRESS_CHARP_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e inp n l out outlen pc rw sp returnaddress
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
     17 <= val out /\ val out + outlen + 64 < 2 EXP 64 /\
     (!m. snappy_header l = SOME m ==> m <= outlen) /\
     ALLPAIRS nonoverlapping
      [(out,outlen); (word_sub sp (word 640),640)]
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el)] /\
     nonoverlapping (out,outlen) (word_sub sp (word 640),640) /\
     ALL (nonoverlapping (inp,LENGTH l))
      [(out,outlen); (word_sub sp (word 640),640)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + RawUncompress__charp_ulong_charp) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           C_ARGUMENTS [inp; n; out] s /\
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
                 (memrange(inp,LENGTH l) UNION memrange(out,outlen) UNION
                  memrange(word_sub sp (word 640),640) UNION
                  memrange(word pc,libsnappy_size) UNION
                  memrange(word(pc + libsnappy_rw),libsnappy_rw_size) UNION
                  memrange(ea,el))
                 (memrange(out,outlen) UNION
                  memrange(word_sub sp (word 640),640)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27;
                  X28; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 64),40)] ,,
       MAYCHANGE [memory :> bytes(word_add (word_sub sp (word 64)) (word 40),
                                   24)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 640),576)] ,,
       MAYCHANGE [memory :> bytes(out,outlen)])`;;

let SNAPPY_RAW_UNCOMPRESS_CHARP_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_RAW_UNCOMPRESS_CHARP_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness alone.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_RAW_UNCOMPRESS_CHARP_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!inp n l out outlen pc rw sp returnaddress
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
     17 <= val out /\ val out + outlen + 64 < 2 EXP 64 /\
     (!m. snappy_header l = SOME m ==> m <= outlen) /\
     ALLPAIRS nonoverlapping
      [(out,outlen); (word_sub sp (word 640),640)]
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el)] /\
     nonoverlapping (out,outlen) (word_sub sp (word 640),640) /\
     ALL (nonoverlapping (inp,LENGTH l))
      [(out,outlen); (word_sub sp (word 640),640)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + RawUncompress__charp_ulong_charp) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           C_ARGUMENTS [inp; n; out] s /\
           read (memory :> bytelist(inp,LENGTH l)) s = l /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s =
             rw /\
           read (memory :> bytes(ea,el)) s = ev)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           C_RETURN s = word(bitval(~(snappy_decode l = NONE))) /\
           (!x. snappy_decode l = SOME x
                ==> read (memory :> bytelist(out,LENGTH x)) s = x))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27;
                  X28; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 64),40)] ,,
       MAYCHANGE [memory :> bytes(word_add (word_sub sp (word 64)) (word 40),
                                   24)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 640),576)] ,,
       MAYCHANGE [memory :> bytes(out,outlen)])`;;

let SNAPPY_RAW_UNCOMPRESS_CHARP_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_RAW_UNCOMPRESS_CHARP_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
