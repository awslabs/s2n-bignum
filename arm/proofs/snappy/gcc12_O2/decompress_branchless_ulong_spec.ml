(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::DecompressBranchless<size_t>(const uint8_t* ip, const uint8_t*    *)
(* ip_limit, ptrdiff_t op, size_t op_base, ptrdiff_t op_limit_min_slop)     *)
(* (snappy.cc), the fast loop of DecompressAllTags<SnappyDecompressionValidator>, *)
(* as that calls it (at 0x6a90):                                            *)
(*                                                                           *)
(*     DecompressBranchless(ip, ip_limit_, produced - 1, 1,                  *)
(*                          PTRDIFF_MAX - 63)                                *)
(*                                                                           *)
(* (SnappyDecompressionValidator::GetBase returns 1 and sets the limit to    *)
(* PTRDIFF_MAX - kSlopBytes + 1), with the decompressor's buffered input inp *)
(* at [ip, ip_limit_) and produced = LENGTH out, for any model output out of *)
(* that length (the validator keeps only the count, out is a ghost). It      *)
(* returns the pair (ip', op') in (X0, X1), and the caller sets produced to *)
(* op' + 1.                                                                  *)
(*                                                                           *)
(* It decodes some number k >= 0 of tags of inp as snappy_tag_step does with *)
(* the bound M = 2^63 (common/snappy/snappy_format.ml): the result is        *)
(* snappy_steps k (2 EXP 63) (inp,out) = SOME(inp',out') with                *)
(* ip' = ip + (LENGTH inp - LENGTH inp') and op' = LENGTH out' - 1. The      *)
(* validator's fast path does not bound the output by the length of the     *)
(* header (FINDINGS F2); the caller relates the steps with the bound 2^63 to *)
(* the decode with its bound m by SNAPPY_STEPS_BOUND_NONE                    *)
(* (common/snappy/snappy_validator.ml). It stops before a tag that the slow *)
(* path must do (a literal of more than 60 bytes, a copy with a 4-byte       *)
(* offset, a copy whose offset is not below the output so far: FINDINGS F1, *)
(* offset = produced is left to the slow path), when at most 129 bytes of    *)
(* input follow the next tag, or (never, under the hypothesis on the        *)
(* lengths) when op plus the deferred length reaches PTRDIFF_MAX - 127. If  *)
(* LENGTH inp <= 130 it returns at once with k = 0.                          *)
(*                                                                           *)
(* The hypothesis LENGTH out + 22 * LENGTH inp <= 2^63 - 128 bounds the     *)
(* output at every point (SNAPPY_STEPS_RATIO), so that the signed compares  *)
(* of the code on op do not wrap; the callers have it from LENGTH l < 2^58.  *)
(*                                                                           *)
(* For size_t, MemCopy64 is a function that returns at once (ret), so the   *)
(* deferred copy (deferred_src, deferred_length, in the frame at sp+144 and *)
(* sp+152, set by the leaf functions ClearDeferred and DeferMemCopy) only   *)
(* counts: op + deferred_length + 1 is the output so far. Nothing is written *)
(* but the frame of 224 bytes; the reads are the input, the frame and the    *)
(* table kLengthMinusOffset in the image. The input must not overlap the     *)
(* frame, and its end must be a pointer value below 2^64 (the code compares *)
(* ip_limit - 129 with ip unsigned).                                         *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "common/snappy/snappy_validator.ml";;

(*** The code in the image: see the listing of DecompressBranchless_ulong    ***)
(*** in layout.ml (0x290 bytes, frame 224 bytes with X19-X30; safe_source  ***)
(*** at sp+160, deferred_src at sp+144, deferred_length at sp+152,         ***)
(*** ip_limit - 129 at sp+112, the address of kLengthMinusOffset at        ***)
(*** sp+96). The loop is unrolled twice (w26 counts the tags of an         ***)
(*** iteration, 2 then 1); the tag is dispatched at 0x689c and 0x6948, the  ***)
(*** limits are checked at 0x696c. Callees: MemCopy64 (0x4670, ret),        ***)
(*** ClearDeferred (0x4674) and DeferMemCopy (0x4680), leaf functions of    ***)
(*** two stores.                                                            ***)

let SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "DecompressBranchless_ulong";
    layout_range "MemCopy64__long_voidp_ulong";
    layout_range "ClearDeferred"; layout_range "DeferMemCopy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety.                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e ip inp out pc sp returnaddress
    x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29.
     aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
     aligned 16 sp /\
     val ip + LENGTH inp < 2 EXP 64 /\
     LENGTH out + 22 * LENGTH inp <= 2 EXP 63 - 128 /\
     nonoverlapping (word_sub sp (word 224),224) (word pc,libsnappy_size) /\
     nonoverlapping (ip,LENGTH inp) (word_sub sp (word 224),224)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + DecompressBranchless_ulong) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           C_ARGUMENTS [ip; word_add ip (word(LENGTH inp));
                        word_sub (word(LENGTH out)) (word 1); word 1;
                        word 9223372036854775744] s /\
           read (memory :> bytelist(ip,LENGTH inp)) s = inp /\
           read events s = e)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           (?k inp' out'.
              snappy_steps k (2 EXP 63) (inp,out) = SOME(inp',out') /\
              read X0 s = word_add ip (word(LENGTH inp - LENGTH inp')) /\
              read X1 s = word_sub (word(LENGTH out')) (word 1)) /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2
                 (memrange(ip,LENGTH inp) UNION
                  memrange(word_sub sp (word 224),224) UNION
                  memrange(word pc,libsnappy_size))
                 (memrange(word_sub sp (word 224),224)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28;
                  X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 224),224)])`;;

let SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness alone.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ip inp out pc sp returnaddress
    x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29.
     aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
     aligned 16 sp /\
     val ip + LENGTH inp < 2 EXP 64 /\
     LENGTH out + 22 * LENGTH inp <= 2 EXP 63 - 128 /\
     nonoverlapping (word_sub sp (word 224),224) (word pc,libsnappy_size) /\
     nonoverlapping (ip,LENGTH inp) (word_sub sp (word 224),224)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + DecompressBranchless_ulong) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           C_ARGUMENTS [ip; word_add ip (word(LENGTH inp));
                        word_sub (word(LENGTH out)) (word 1); word 1;
                        word 9223372036854775744] s /\
           read (memory :> bytelist(ip,LENGTH inp)) s = inp)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           ?k inp' out'.
              snappy_steps k (2 EXP 63) (inp,out) = SOME(inp',out') /\
              read X0 s = word_add ip (word(LENGTH inp - LENGTH inp')) /\
              read X1 s = word_sub (word(LENGTH out')) (word 1))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28;
                  X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 224),224)])`;;

let SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
