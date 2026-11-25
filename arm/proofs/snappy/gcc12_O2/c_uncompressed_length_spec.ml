(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy_uncompressed_length(const char* compressed, size_t                 *)
(* compressed_length, size_t* result) of the C interface (snappy-c.cc):      *)
(* SNAPPY_OK (0) iff the header of the input l is valid, and then *result =  *)
(* m for snappy_header l = SOME m; else SNAPPY_INVALID_INPUT (1) and        *)
(* *result is not written. The status is snappy_uncompressed_length_status *)
(* l (common/snappy/snappy_format.ml). It calls GetUncompressedLength with a *)
(* 16-byte frame (X29, X30).                                                 *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/get_uncompressed_length_charp_ulong_ulongp_spec.ml";;

(*** The code in the image:

    c_snappy_uncompressed_length:
     +0x0  stp     x29, x30, [sp, #-16]!
     +0x4  mov     x29, sp
     +0x8  bl      GetUncompressedLength__charp_ulong_ulongp
     +0xc  and     w0, w0, #0xff
    +0x10  eor     w0, w0, #0x1
    +0x14  ldp     x29, x30, [sp], #16
    +0x18  ret
 ***)

let SNAPPY_C_UNCOMPRESSED_LENGTH_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "c_snappy_uncompressed_length";
    layout_range "GetUncompressedLength__charp_ulong_ulongp"];;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety.                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_C_UNCOMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e inp n res l r0 pc sp returnaddress x29.
     aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
     val n = LENGTH l /\ val inp + LENGTH l < 2 EXP 64 /\
     nonoverlapping (res,8) (word pc,libsnappy_size) /\
     aligned 16 sp /\
     ALL (nonoverlapping (word_sub sp (word 16),16))
      [(word pc,libsnappy_size); (inp,LENGTH l); (res,8)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + c_snappy_uncompressed_length) /\
           read SP s = sp /\ read X30 s = returnaddress /\ read X29 s = x29 /\
           C_ARGUMENTS [inp; n; res] s /\
           read (memory :> bytelist(inp,LENGTH l)) s = l /\
           read (memory :> bytes64 res) s = r0 /\
           read events s = e)
      (\s. read PC s = returnaddress /\ read SP s = sp /\ read X29 s = x29 /\
           C_RETURN s = word(snappy_uncompressed_length_status l) /\
           (!m. snappy_header l = SOME m
                ==> read (memory :> bytes64 res) s = word m) /\
           (snappy_header l = NONE ==> read (memory :> bytes64 res) s = r0) /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2
                 (memrange(inp,LENGTH l) UNION memrange(word_sub sp (word 16),16))
                 (memrange(res,8) UNION memrange(word_sub sp (word 16),16)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 16),16)] ,,
       MAYCHANGE [memory :> bytes(res,8)])`;;

let SNAPPY_C_UNCOMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_C_UNCOMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness alone.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_C_UNCOMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!inp n res l r0 pc sp returnaddress x29.
     aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
     val n = LENGTH l /\ val inp + LENGTH l < 2 EXP 64 /\
     nonoverlapping (res,8) (word pc,libsnappy_size) /\
     aligned 16 sp /\
     ALL (nonoverlapping (word_sub sp (word 16),16))
      [(word pc,libsnappy_size); (inp,LENGTH l); (res,8)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + c_snappy_uncompressed_length) /\
           read SP s = sp /\ read X30 s = returnaddress /\ read X29 s = x29 /\
           C_ARGUMENTS [inp; n; res] s /\
           read (memory :> bytelist(inp,LENGTH l)) s = l /\
           read (memory :> bytes64 res) s = r0)
      (\s. read PC s = returnaddress /\ read SP s = sp /\ read X29 s = x29 /\
           C_RETURN s = word(snappy_uncompressed_length_status l) /\
           (!m. snappy_header l = SOME m
                ==> read (memory :> bytes64 res) s = word m) /\
           (snappy_header l = NONE ==> read (memory :> bytes64 res) s = r0))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 16),16)] ,,
       MAYCHANGE [memory :> bytes(res,8)])`;;

let SNAPPY_C_UNCOMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_C_UNCOMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
