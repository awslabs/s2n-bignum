(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::GetUncompressedLength(const char* start, size_t n, size_t* result) *)
(* (snappy.cc): parses the header of the n bytes l at start with            *)
(* Varint::Parse32WithLimit and returns true iff it is a valid header,       *)
(* snappy_header l = SOME m (common/snappy/snappy_format.ml); then it stores *)
(* m at result, else it writes nothing. It reads at most the first 5 bytes   *)
(* of the input. The input must not end at the top of the address space     *)
(* (val start + n < 2^64): the code compares against start + n.             *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "common/footprint.ml";;
needs "common/snappy/snappy_format.ml";;

(*** The code in the image: see the listing of                             ***)
(*** GetUncompressedLength__charp_ulong_ulongp in layout.ml (0xac bytes, a  ***)
(*** leaf function: the varint, unrolled, bytes 1-5).                       ***)

let SNAPPY_GET_UNCOMPRESSED_LENGTH_CHARP_ULONG_ULONGP_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "GetUncompressedLength__charp_ulong_ulongp"];;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety.                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_GET_UNCOMPRESSED_LENGTH_CHARP_ULONG_ULONGP_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e inp n res l r0 pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
     val n = LENGTH l /\ val inp + LENGTH l < 2 EXP 64 /\
     nonoverlapping (res,8) (word pc,libsnappy_size)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + GetUncompressedLength__charp_ulong_ulongp) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [inp; n; res] s /\
           read (memory :> bytelist(inp,LENGTH l)) s = l /\
           read (memory :> bytes64 res) s = r0 /\
           read events s = e)
      (\s. read PC s = returnaddress /\
           C_RETURN s = word(bitval(~(snappy_header l = NONE))) /\
           (!m. snappy_header l = SOME m
                ==> read (memory :> bytes64 res) s = word m) /\
           (snappy_header l = NONE ==> read (memory :> bytes64 res) s = r0) /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2 (memrange(inp,LENGTH l)) (memrange(res,8)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(res,8)])`;;

let SNAPPY_GET_UNCOMPRESSED_LENGTH_CHARP_ULONG_ULONGP_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_GET_UNCOMPRESSED_LENGTH_CHARP_ULONG_ULONGP_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness alone.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_GET_UNCOMPRESSED_LENGTH_CHARP_ULONG_ULONGP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!inp n res l r0 pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
     val n = LENGTH l /\ val inp + LENGTH l < 2 EXP 64 /\
     nonoverlapping (res,8) (word pc,libsnappy_size)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + GetUncompressedLength__charp_ulong_ulongp) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [inp; n; res] s /\
           read (memory :> bytelist(inp,LENGTH l)) s = l /\
           read (memory :> bytes64 res) s = r0)
      (\s. read PC s = returnaddress /\
           C_RETURN s = word(bitval(~(snappy_header l = NONE))) /\
           (!m. snappy_header l = SOME m
                ==> read (memory :> bytes64 res) s = word m) /\
           (snappy_header l = NONE ==> read (memory :> bytes64 res) s = r0))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(res,8)])`;;

let SNAPPY_GET_UNCOMPRESSED_LENGTH_CHARP_ULONG_ULONGP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_GET_UNCOMPRESSED_LENGTH_CHARP_ULONG_ULONGP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
