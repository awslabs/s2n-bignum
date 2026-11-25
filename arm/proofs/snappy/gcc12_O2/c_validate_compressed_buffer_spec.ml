(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy_validate_compressed_buffer(const char* compressed, size_t n) of  *)
(* the C interface (snappy-c.cc): SNAPPY_OK (0) iff IsValidCompressedBuffer *)
(* accepts the input, else SNAPPY_INVALID_INPUT (1): the status            *)
(* snappy_validate_status l (common/snappy/snappy_format.ml), for any bytes *)
(* of fewer than 2^58 that do not wrap around the end of the address space. *)
(* Its frame is 16 bytes (X29, X30) above the 544 of the callee.            *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/is_valid_compressed_buffer_spec.ml";;

(*** The code in the image:

    c_snappy_validate_compressed_buffer:
     +0x0  stp     x29, x30, [sp, #-16]!
     +0x4  mov     x29, sp
     +0x8  bl      IsValidCompressedBuffer
     +0xc  and     w0, w0, #0xff
    +0x10  eor     w0, w0, #0x1
    +0x14  ldp     x29, x30, [sp], #16
    +0x18  ret
 ***)

let SNAPPY_C_VALIDATE_COMPRESSED_BUFFER_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "c_snappy_validate_compressed_buffer"];;

let SNAPPY_C_VALIDATE_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e inp n l pc rw sp returnaddress x19 x20 x21 x22 x23 x24 x25 x26 x29
    ea el ev.
     memmove_correct_safe_contract (imp "memmove") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\ 560 <= val sp /\
     val n = LENGTH l /\ LENGTH l < 2 EXP 58 /\ val inp + LENGTH l < 2 EXP 64 /\
     ALL (nonoverlapping (word_sub sp (word 560),560))
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el); (inp,LENGTH l)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + c_snappy_validate_compressed_buffer) /\
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
           C_RETURN s = word(snappy_validate_status l) /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2
                 (memrange(inp,LENGTH l) UNION
                  memrange(word_sub sp (word 560),560) UNION
                  memrange(word pc,libsnappy_size) UNION
                  memrange(word(pc + libsnappy_rw),libsnappy_rw_size) UNION
                  memrange(ea,el))
                 (memrange(word_sub sp (word 560),560)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X25; X26; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 560),560)])`;;

let SNAPPY_C_VALIDATE_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_C_VALIDATE_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

let SNAPPY_C_VALIDATE_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!inp n l pc rw sp returnaddress x19 x20 x21 x22 x23 x24 x25 x26 x29
    ea el ev.
     memmove_correct_safe_contract (imp "memmove") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\ 560 <= val sp /\
     val n = LENGTH l /\ LENGTH l < 2 EXP 58 /\ val inp + LENGTH l < 2 EXP 64 /\
     ALL (nonoverlapping (word_sub sp (word 560),560))
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el); (inp,LENGTH l)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + c_snappy_validate_compressed_buffer) /\
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
           C_RETURN s = word(snappy_validate_status l))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X25; X26; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 560),560)])`;;

let SNAPPY_C_VALIDATE_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_C_VALIDATE_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
