(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::(anonymous)::IncrementalCopy(const char* src, char* op,           *)
(* char* const op_limit, char* const buf_limit) (snappy.cc), as              *)
(* SnappyArrayWriter::AppendFromSelf calls it: the copy of a tag with offset *)
(* off and length n, IncrementalCopy(op - off, op, op + n, op + b), where    *)
(* the output so far is out at base (op = base + LENGTH out) and the buffer  *)
(* ends b bytes after op. It appends n bytes, each the byte off positions    *)
(* before it (the copy may overlap its own output), so the output becomes    *)
(* snappy_copy off n out, and returns op + n.                                *)
(*                                                                           *)
(* The conditions are the asserts of the source: src < op < op_limit <=      *)
(* buf_limit and op_limit - op <= 64, i.e. 1 <= off <= LENGTH out (the copy  *)
(* starts inside the output) and 1 <= n <= 64, n <= b. The pointers do not   *)
(* wrap around (the code compares them unsigned) and buf_limit is at least   *)
(* 17 (it computes buf_limit - 17 .. buf_limit - 8 as pointers). Also op +   *)
(* 64 does not wrap: for op_limit <= buf_limit - 15 the code compares        *)
(* op_limit with op + 16, op + 32 and op + 48 (whatever buf_limit is), so a  *)
(* buffer that ends just below 2^64 would get a store at a wrapped address.  *)
(*                                                                           *)
(* It writes only between op and buf_limit: blocks of 16 or 8 bytes while    *)
(* they fit before buf_limit, then single bytes up to op_limit; so it writes *)
(* beyond op_limit ("slop") but never beyond buf_limit. It reads only        *)
(* between src and buf_limit (16 bytes at src for a pattern of fewer than 16 *)
(* bytes, of which the shuffle masks select the pattern) and the shuffle     *)
(* masks in the image. It is a leaf function without a stack frame.          *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "common/snappy/snappy_decompress.ml";;
needs "common/footprint.ml";;
needs "arm/proofs/bstep.ml";;
needs "arm/proofs/heap_plt.ml";;

(*** The code in the image: see the listing of IncrementalCopy in          ***)
(*** layout.ml (0x1e8 bytes). x5 = op - src is the pattern size; the       ***)
(*** paths are: pattern < 16 with op_limit <= buf_limit - 15 (masks, 1 to  ***)
(*** 4 stores of 16 bytes); pattern < 16 otherwise (masks, a loop of 16-   ***)
(*** byte stores while op < buf_limit - 15, then the byte loop); pattern   ***)
(*** >= 16 with op_limit <= buf_limit - 15 (1 to 4 copies of 16 bytes);    ***)
(*** pattern >= 16 otherwise (a loop of 16-byte copies while op <          ***)
(*** buf_limit - 16, an 8-byte copy if op <= buf_limit - 8, the byte       ***)
(*** loop).                                                                ***)

let SNAPPY_INCREMENTAL_COPY_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "IncrementalCopy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety.                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_INCREMENTAL_COPY_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e src op op_limit buf_limit base out off n b pc returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_size <= 2 EXP 64 /\
     op = word_add base (word(LENGTH out)) /\
     src = word_sub op (word off) /\
     op_limit = word_add op (word n) /\
     buf_limit = word_add op (word b) /\
     1 <= off /\ off <= LENGTH out /\ 1 <= n /\ n <= 64 /\ n <= b /\
     17 <= val base + LENGTH out + b /\
     val base + LENGTH out + b < 2 EXP 64 /\
     val base + LENGTH out + 64 < 2 EXP 64 /\
     nonoverlapping (op,b) (word pc,libsnappy_size)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + IncrementalCopy) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [src; op; op_limit; buf_limit] s /\
           read (memory :> bytelist(base,LENGTH out)) s = out /\
           read events s = e)
      (\s. read PC s = returnaddress /\
           C_RETURN s = op_limit /\
           read (memory :> bytelist(base,LENGTH out + n)) s =
             snappy_copy off n out /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2
                 (memrange(src,off + b) UNION
                  memrange(word pc,libsnappy_size))
                 (memrange(op,b)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(op,b)])`;;

let SNAPPY_INCREMENTAL_COPY_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_INCREMENTAL_COPY_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness alone.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_INCREMENTAL_COPY_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!src op op_limit buf_limit base out off n b pc returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_size <= 2 EXP 64 /\
     op = word_add base (word(LENGTH out)) /\
     src = word_sub op (word off) /\
     op_limit = word_add op (word n) /\
     buf_limit = word_add op (word b) /\
     1 <= off /\ off <= LENGTH out /\ 1 <= n /\ n <= 64 /\ n <= b /\
     17 <= val base + LENGTH out + b /\
     val base + LENGTH out + b < 2 EXP 64 /\
     val base + LENGTH out + 64 < 2 EXP 64 /\
     nonoverlapping (op,b) (word pc,libsnappy_size)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + IncrementalCopy) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [src; op; op_limit; buf_limit] s /\
           read (memory :> bytelist(base,LENGTH out)) s = out)
      (\s. read PC s = returnaddress /\
           C_RETURN s = op_limit /\
           read (memory :> bytelist(base,LENGTH out + n)) s =
             snappy_copy off n out)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(op,b)])`;;

let SNAPPY_INCREMENTAL_COPY_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_INCREMENTAL_COPY_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
