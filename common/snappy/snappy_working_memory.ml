(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The sizes of the scratch memory of snappy's compressor (snappy.cc and    *)
(* snappy-internal.h, snappy 1.3.1), as functions of the input size, for    *)
(* the specifications of WorkingMemory and CompressionContext:              *)
(*                                                                           *)
(*  - snappy_table_size n (common/snappy/snappy_compress.ml) is            *)
(*    CalculateTableSize(n), the number of the uint16_t entries of the hash *)
(*    table for a fragment of n bytes: the least power of two that is at    *)
(*    least n, within kMinHashTableSize = 256 and kMaxHashTableSize = 32768 *)
(*    (for 256 <= n <= 32768 the code's 2 << Log2Floor(n - 1));             *)
(*                                                                           *)
(*  - snappy_fragment_size n = min(n, kBlockSize), kBlockSize = 65536, the  *)
(*    largest fragment that the compressor works on for an input of n bytes;*)
(*                                                                           *)
(*  - snappy_working_memory_size n is WorkingMemory::RequiredSize(n): the   *)
(*    hash table (2 bytes an entry), then the scratch input (a fragment)    *)
(*    and the scratch output (snappy_max_compressed_length of a fragment,   *)
(*    32 + m + m / 6 for a fragment of m <= 65536 bytes), laid out in this  *)
(*    order by WorkingMemory(size_t, char* );                              *)
(*                                                                           *)
(*  - snappy_working_memory_input n and snappy_working_memory_output n, the *)
(*    offsets of the scratch input and output in that memory.               *)
(*                                                                           *)
(* The memory is at most 207562 bytes (for n >= 65536), so the check of     *)
(* std::allocator<char>::allocate against PTRDIFF_MAX, which would throw    *)
(* std::bad_alloc, never fails (SNAPPY_WORKING_MEMORY_SIZE_BOUND).          *)
(* ========================================================================= *)

needs "common/snappy/snappy_compress.ml";;

let snappy_fragment_size = new_definition
 `snappy_fragment_size n = MIN n 65536`;;

let snappy_working_memory_size = new_definition
 `snappy_working_memory_size n =
    2 * snappy_table_size (snappy_fragment_size n) +
    snappy_fragment_size n +
    snappy_max_compressed_length (snappy_fragment_size n)`;;

let snappy_working_memory_input = new_definition
 `snappy_working_memory_input n =
    2 * snappy_table_size (snappy_fragment_size n)`;;

let snappy_working_memory_output = new_definition
 `snappy_working_memory_output n =
    2 * snappy_table_size (snappy_fragment_size n) +
    snappy_fragment_size n`;;

(* ------------------------------------------------------------------------- *)
(* Bounds.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_TABLE_SIZE_BOUNDS = prove
 (`!n. 256 <= snappy_table_size n /\ snappy_table_size n <= 32768`,
  GEN_TAC THEN REWRITE_TAC[snappy_table_size] THEN
  REPEAT COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV);;

let SNAPPY_FRAGMENT_SIZE_BOUND = prove
 (`!n. snappy_fragment_size n <= 65536 /\ snappy_fragment_size n <= n`,
  REWRITE_TAC[snappy_fragment_size] THEN ARITH_TAC);;

(* The size with MaxCompressedLength of a fragment, which is small.          *)

let SNAPPY_WORKING_MEMORY_SIZE_ALT = prove
 (`!n. snappy_working_memory_size n =
       2 * snappy_table_size (snappy_fragment_size n) +
       snappy_fragment_size n +
       (32 + snappy_fragment_size n + snappy_fragment_size n DIV 6)`,
  GEN_TAC THEN REWRITE_TAC[snappy_working_memory_size] THEN
  REPEAT AP_TERM_TAC THEN MATCH_MP_TAC SNAPPY_MAX_COMPRESSED_LENGTH_32 THEN
  MP_TAC(SPEC `n:num` SNAPPY_FRAGMENT_SIZE_BOUND) THEN ARITH_TAC);;

let SNAPPY_WORKING_MEMORY_SIZE_BOUND = prove
 (`!n. snappy_working_memory_size n <= 207562`,
  GEN_TAC THEN REWRITE_TAC[SNAPPY_WORKING_MEMORY_SIZE_ALT] THEN
  MP_TAC(SPEC `snappy_fragment_size n` SNAPPY_TABLE_SIZE_BOUNDS) THEN
  MP_TAC(SPEC `n:num` SNAPPY_FRAGMENT_SIZE_BOUND) THEN
  SPEC_TAC(`snappy_table_size (snappy_fragment_size n)`,`t:num`) THEN
  SPEC_TAC(`snappy_fragment_size n`,`m:num`) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `65536`] DIV_MONO) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

(* The parts of the memory: the table, the input and the output, in order.   *)

let SNAPPY_WORKING_MEMORY_PARTS = prove
 (`!n. snappy_working_memory_input n <= snappy_working_memory_output n /\
       snappy_working_memory_output n <= snappy_working_memory_size n /\
       snappy_working_memory_output n =
       snappy_working_memory_input n + snappy_fragment_size n /\
       snappy_working_memory_size n =
       snappy_working_memory_output n +
       snappy_max_compressed_length (snappy_fragment_size n)`,
  REWRITE_TAC[snappy_working_memory_input; snappy_working_memory_output;
              snappy_working_memory_size] THEN ARITH_TAC);;

(* The values of CalculateTableSize as the code computes them for            *)
(* 256 <= n <= 32768: 2 << Log2Floor(n - 1), i.e. 2^(k + 1) for              *)
(* 2^k <= n - 1 < 2^(k + 1).                                                 *)

let SNAPPY_TABLE_SIZE_LOG = prove
 (`!n k. 2 EXP k < n /\ n <= 2 EXP (k + 1) /\ 7 <= k /\ k <= 14
         ==> snappy_table_size n = 2 EXP (k + 1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE
   `7 <= k /\ k <= 14 <=>
    k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/
    k = 14`] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[snappy_table_size] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let SNAPPY_TABLE_SIZE_MAX = prove
 (`!n. 16384 < n ==> snappy_table_size n = 32768`,
  REWRITE_TAC[snappy_table_size] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN REFL_TAC);;

let SNAPPY_TABLE_SIZE_MIN = prove
 (`!n. n <= 256 ==> snappy_table_size n = 256`,
  SIMP_TAC[snappy_table_size]);;

(* The sizes for the three ranges of n that the code distinguishes.         *)

let SNAPPY_WORKING_MEMORY_SIZE_CASES = prove
 (`!n. snappy_working_memory_size n =
       if 65536 < n then 65536 + 65536 + (32 + 65536 + 65536 DIV 6)
       else if 32768 < n then 65536 + n + (32 + n + n DIV 6)
       else 2 * snappy_table_size n + n + (32 + n + n DIV 6)`,
  GEN_TAC THEN
  REWRITE_TAC[SNAPPY_WORKING_MEMORY_SIZE_ALT; snappy_fragment_size] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `MIN n 65536 = 65536` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MATCH_MP SNAPPY_TABLE_SIZE_MAX
                  (ARITH_RULE `16384 < 65536`)] THEN
    CONV_TAC NUM_REDUCE_CONV;
    SUBGOAL_THEN `MIN n 65536 = n` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_SIMP_TAC[SNAPPY_TABLE_SIZE_MAX;
                 ARITH_RULE `32768 < n ==> 16384 < n`] THEN ARITH_TAC]);;
