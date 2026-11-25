(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The objects of snappy's compressor in memory, as the AArch64 Linux C++    *)
(* ABI (LP64, Itanium C++ ABI) lays them out; they do not depend on the      *)
(* compiler or its options.                                                  *)
(*                                                                           *)
(* snappy::internal::WorkingMemory (snappy-internal.h), 48 bytes, 8-aligned: *)
(*                                                                           *)
(*    +0   char* mem_         the memory: table, scratch input and output    *)
(*    +8   size_t size_       its size, RequiredSize(input_size)             *)
(*    +16  bool owns_mem_     whether the destructor frees mem_              *)
(*    +24  uint16_t* table_   = mem_                                         *)
(*    +32  char* input_       = mem_ + 2 * CalculateTableSize(fragment)      *)
(*    +40  char* output_      = input_ + fragment                            *)
(*                                                                           *)
(* (bytes 17 to 23 are padding). snappy_working_memory wm mem n owns s says  *)
(* that in the state s the object at wm was constructed for an input of n    *)
(* bytes with the memory at mem, as WorkingMemory(n, mem) does (owns F) and  *)
(* WorkingMemory(n) does (owns T, mem a block of the heap), with the sizes   *)
(* of common/snappy/snappy_working_memory.ml.                                *)
(*                                                                           *)
(* snappy::CompressionContext (snappy.h), 16 bytes, 8-aligned:              *)
(*                                                                           *)
(*    +0   internal::WorkingMemory* working_memory_   (nullptr after Reset)  *)
(*    +8   bool owns_working_memory_                                         *)
(*                                                                           *)
(* snappy_compression_context cc wm owns s says that the object at cc points *)
(* to the WorkingMemory at wm (word 0 for none) and owns it or not.          *)
(* ========================================================================= *)

needs "common/snappy/snappy_working_memory.ml";;

let snappy_working_memory = new_definition
 `snappy_working_memory (wm:int64) (mem:int64) (n:num) (owns:bool)
                        (s:armstate) <=>
    read (memory :> bytes64 wm) s = mem /\
    read (memory :> bytes64 (word_add wm (word 8))) s =
      word(snappy_working_memory_size n) /\
    read (memory :> bytes8 (word_add wm (word 16))) s = word(bitval owns) /\
    read (memory :> bytes64 (word_add wm (word 24))) s = mem /\
    read (memory :> bytes64 (word_add wm (word 32))) s =
      word_add mem (word(snappy_working_memory_input n)) /\
    read (memory :> bytes64 (word_add wm (word 40))) s =
      word_add mem (word(snappy_working_memory_output n))`;;

let snappy_compression_context = new_definition
 `snappy_compression_context (cc:int64) (wm:int64) (owns:bool)
                             (s:armstate) <=>
    read (memory :> bytes64 cc) s = wm /\
    read (memory :> bytes8 (word_add cc (word 8))) s = word(bitval owns)`;;

(* The facts of the predicates, as assumptions for the step tactics.         *)

let SNAPPY_OBJECTS_EXPAND_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[snappy_working_memory;
                              snappy_compression_context]) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC));;
