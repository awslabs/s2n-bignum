(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::DecompressBranchless<char*>(const uint8_t* ip, const uint8_t*     *)
(* ip_limit, ptrdiff_t op, char* op_base, ptrdiff_t op_limit_min_slop)      *)
(* (snappy.cc), the fast loop of DecompressAllTags<SnappyArrayWriter>, as    *)
(* that calls it (at 0x6420):                                                *)
(*                                                                           *)
(*     DecompressBranchless(ip, ip_limit_, op - base_, base_,                *)
(*                          op_limit_min_slop_ - base_)                      *)
(*                                                                           *)
(* with the decompressor's buffered input inp at [ip, ip_limit_), the output *)
(* so far out at base (op = base + LENGTH out) and the writer's buffer of m  *)
(* bytes (op_limit_ = base + m, op_limit_min_slop_ = op_limit_ - min(63, m), *)
(* SnappyArrayWriter::SetExpectedLength), so the last argument is            *)
(* m - MIN 63 m. It returns the pair (ip', op' - base) in (X0, X1).          *)
(*                                                                           *)
(* It decodes some number k >= 0 of tags of inp, exactly as snappy_tag_step  *)
(* m does (common/snappy/snappy_format.ml): the result is                    *)
(* snappy_steps k m (inp,out) = SOME(inp',out') with ip' = ip + (LENGTH inp  *)
(* - LENGTH inp') (inp' is a suffix of inp: SNAPPY_STEPS_SOME) and the       *)
(* output out' at base, of length val op'. The caller continues with the     *)
(* slow path at (inp', out'), so how many tags it decoded does not matter:   *)
(* it stops before a tag that the slow path must do (a literal of more than  *)
(* 60 bytes, a copy with a 4-byte offset, a copy with offset 0 or beyond     *)
(* the output so far), when at most 129 bytes of input follow the next tag,  *)
(* or when op plus the deferred length reaches op_limit_min_slop_ - 64. If   *)
(* m <= 127 or LENGTH inp <= 130 it returns at once with k = 0.              *)
(*                                                                           *)
(* The deferred copy (deferred_src, deferred_length, in the frame at sp+160  *)
(* and sp+168, set by the leaf functions ClearDeferred and DeferMemCopy) is  *)
(* internal: it is always flushed (MemCopy64) before the function returns,   *)
(* so nothing of it is left for the caller.                                  *)
(*                                                                           *)
(* Writes: the output buffer (base,m) (slop up to 64 bytes beyond op' but    *)
(* never beyond base + m, see DESIGN section 7b), its frame of 240 bytes and *)
(* MemCopy64's frame of 48 bytes below it. Reads: the input, the output     *)
(* buffer, the two frames (the 64-byte safe_source in its frame, of which   *)
(* MemCopy64 copies 32 bytes as slop when no copy is deferred), the tables   *)
(* kLengthMinusOffset and the pattern masks in the image, the GOT slot of    *)
(* memmove in the RW segment and memmove's region (ea,el). The input must   *)
(* not overlap the output buffer or the stack below sp; a pointer value at   *)
(* most 2^64 - 1 at the end of the input (the code compares ip_limit - 129   *)
(* with ip unsigned).                                                        *)
(*                                                                           *)
(* The contract of memmove (arm/proofs/libc.ml) is reached through           *)
(* MemCopy64<64> (mem_copy64_spec.ml).                                       *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "common/snappy/snappy_format.ml";;
needs "arm/proofs/snappy/gcc12_O2/mem_copy64_spec.ml";;

(*** The code in the image: see the listing of DecompressBranchless_charp ***)
(*** in layout.ml (0x350 bytes, frame 240 bytes with X19-X30; safe_source ***)
(*** at sp+176, deferred_src at sp+160, deferred_length at sp+168). The    ***)
(*** loop is unrolled twice (w26 counts the tags of an iteration, 2 then   ***)
(*** 1); the tag is at 0x6174 (dispatch at 0x6140 and 0x61f0), the check   ***)
(*** of the limits at 0x621c. Callees: ClearDeferred (0x4674) and          ***)
(*** DeferMemCopy (0x4680), leaf functions of two stores, and MemCopy64.   ***)

let SNAPPY_DECOMPRESS_BRANCHLESS_CHARP_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "DecompressBranchless_charp"; layout_range "ClearDeferred";
    layout_range "DeferMemCopy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety.                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_DECOMPRESS_BRANCHLESS_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e ip inp base out m pc rw sp returnaddress
    x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ea el ev.
     memmove_correct_safe_contract (imp "memmove") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     val ip + LENGTH inp < 2 EXP 64 /\
     LENGTH out <= m /\ m < 2 EXP 32 /\ val base + m < 2 EXP 64 /\
     ALLPAIRS nonoverlapping
      [(base,m); (word_sub sp (word 288),288)]
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el)] /\
     nonoverlapping (base,m) (word_sub sp (word 288),288) /\
     ALL (nonoverlapping (ip,LENGTH inp))
      [(base,m); (word_sub sp (word 288),288)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + DecompressBranchless_charp) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           C_ARGUMENTS [ip; word_add ip (word(LENGTH inp));
                        word(LENGTH out); base; word(m - MIN 63 m)] s /\
           read (memory :> bytelist(ip,LENGTH inp)) s = inp /\
           read (memory :> bytelist(base,LENGTH out)) s = out /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s =
             rw /\
           read (memory :> bytes(ea,el)) s = ev /\
           read events s = e)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           (?k inp' out'.
              snappy_steps k m (inp,out) = SOME(inp',out') /\
              read X0 s = word_add ip (word(LENGTH inp - LENGTH inp')) /\
              read X1 s = word(LENGTH out') /\
              read (memory :> bytelist(base,LENGTH out')) s = out') /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2
                 (memrange(ip,LENGTH inp) UNION memrange(base,m) UNION
                  memrange(word_sub sp (word 288),288) UNION
                  memrange(word pc,libsnappy_size) UNION
                  memrange(word(pc + libsnappy_rw),libsnappy_rw_size) UNION
                  memrange(ea,el))
                 (memrange(base,m) UNION memrange(word_sub sp (word 288),288)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28;
                  X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 240),240)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 288),48)] ,,
       MAYCHANGE [memory :> bytes(base,m)])`;;

let SNAPPY_DECOMPRESS_BRANCHLESS_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_DECOMPRESS_BRANCHLESS_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness alone.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_DECOMPRESS_BRANCHLESS_CHARP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ip inp base out m pc rw sp returnaddress
    x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ea el ev.
     memmove_correct_safe_contract (imp "memmove") ea el ev /\
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     val ip + LENGTH inp < 2 EXP 64 /\
     LENGTH out <= m /\ m < 2 EXP 32 /\ val base + m < 2 EXP 64 /\
     ALLPAIRS nonoverlapping
      [(base,m); (word_sub sp (word 288),288)]
      [(word pc,libsnappy_rw + libsnappy_rw_size); (ea,el)] /\
     nonoverlapping (base,m) (word_sub sp (word 288),288) /\
     ALL (nonoverlapping (ip,LENGTH inp))
      [(base,m); (word_sub sp (word 288),288)]
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + DecompressBranchless_charp) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           C_ARGUMENTS [ip; word_add ip (word(LENGTH inp));
                        word(LENGTH out); base; word(m - MIN 63 m)] s /\
           read (memory :> bytelist(ip,LENGTH inp)) s = inp /\
           read (memory :> bytelist(base,LENGTH out)) s = out /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s =
             rw /\
           read (memory :> bytes(ea,el)) s = ev)
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
           read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
           read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
           read X28 s = x28 /\ read X29 s = x29 /\
           ?k inp' out'.
              snappy_steps k m (inp,out) = SOME(inp',out') /\
              read X0 s = word_add ip (word(LENGTH inp - LENGTH inp')) /\
              read X1 s = word(LENGTH out') /\
              read (memory :> bytelist(base,LENGTH out')) s = out')
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28;
                  X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 240),240)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 288),48)] ,,
       MAYCHANGE [memory :> bytes(base,m)])`;;

let SNAPPY_DECOMPRESS_BRANCHLESS_CHARP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_DECOMPRESS_BRANCHLESS_CHARP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
