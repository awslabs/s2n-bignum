(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::IsValidCompressedBuffer(const char* in, size_t n) (snappy.cc):   *)
(* true iff the n bytes l at in are a valid compressed stream,              *)
(* snappy_decode l <> NONE (common/snappy/snappy_format.ml), for any bytes. *)
(* It builds a ByteArraySource and a SnappyDecompressionValidator on its    *)
(* stack and calls InternalUncompress<SnappyDecompressionValidator>, which  *)
(* reads the header (ReadUncompressedLength, inlined) and runs              *)
(* DecompressAllTags<SnappyDecompressionValidator> with the fast path       *)
(* DecompressBranchless<size_t> (FINDINGS F1, F2: the hypothesis            *)
(* LENGTH l < 2^58 keeps the validator's count of produced bytes from       *)
(* wrapping); then the destructor of the source. The input must not wrap    *)
(* around the end of the address space (val in + LENGTH l < 2^64, as for a  *)
(* C object: the code compares pointers into it unsigned). It writes only   *)
(* its stack: 544 bytes below sp, the frames of the chain (80 + 144 + 96 +  *)
(* 224; RefillTag's 80 bytes are within DecompressBranchless's 224). It     *)
(* reads the input, the stack, the image (the tables kLengthMinusOffset and *)
(* LeftShiftOverflows_masks), the RW segment (the vtable of the source and  *)
(* the GOT) and memmove's region (ea,el). X27 and X28, which                *)
(* DecompressBranchless saves and restores, are not in the frame.           *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/snappy/decompressor_objects.ml";;
needs "arm/proofs/snappy/gcc12_O2/internal_uncompress_validator_spec.ml";;

(*** The code in the image: see the listing of IsValidCompressedBuffer in ***)
(*** layout.ml (0x58 bytes, frame 80 bytes with X19, X29, X30; the         ***)
(*** validator at sp+32, the ByteArraySource at sp+56).                    ***)

let SNAPPY_IS_VALID_COMPRESSED_BUFFER_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "IsValidCompressedBuffer"; layout_range "ByteArraySource_dtor";
    layout_range "Source_dtor"];;

let SNAPPY_IS_VALID_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e inp n l pc rw sp returnaddress x19 x20 x21 x22 x23 x24 x25 x26 x29
    ea el ev.
     memmove_correct_safe_contract (imp "memmove") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\ 544 <= val sp /\
     val n = LENGTH l /\ LENGTH l < 2 EXP 58 /\ val inp + LENGTH l < 2 EXP 64 /\
     ALL (nonoverlapping (word_sub sp (word 544),544))
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el); (inp,LENGTH l)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + IsValidCompressedBuffer) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X29 s = x29 /\
           C_ARGUMENTS [inp; n] s /\
           read (memory :> bytelist(inp,LENGTH l)) s = l /\
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
                 (memrange(inp,LENGTH l) UNION
                  memrange(word_sub sp (word 544),544) UNION
                  memrange(word pc,libsnappy_size) UNION
                  memrange(word(pc + libsnappy_rw),libsnappy_rw_size) UNION
                  memrange(ea,el))
                 (memrange(word_sub sp (word 544),544)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X25; X26; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 544),544)])`;;

let SNAPPY_IS_VALID_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_IS_VALID_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

let SNAPPY_IS_VALID_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!inp n l pc rw sp returnaddress x19 x20 x21 x22 x23 x24 x25 x26 x29
    ea el ev.
     memmove_correct_safe_contract (imp "memmove") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\ 544 <= val sp /\
     val n = LENGTH l /\ LENGTH l < 2 EXP 58 /\ val inp + LENGTH l < 2 EXP 64 /\
     ALL (nonoverlapping (word_sub sp (word 544),544))
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el); (inp,LENGTH l)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + IsValidCompressedBuffer) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X29 s = x29 /\
           C_ARGUMENTS [inp; n] s /\
           read (memory :> bytelist(inp,LENGTH l)) s = l /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s =
             rw /\
           read (memory :> bytes(ea,el)) s = ev)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X29 s = x29 /\
           C_RETURN s = word(bitval(~(snappy_decode l = NONE))))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X25; X26; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 544),544)])`;;

let SNAPPY_IS_VALID_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_IS_VALID_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
