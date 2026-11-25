(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The piece of CompressFragmentDoubleHash from loop1                        *)
(* (CompressFragmentDoubleHash_loop1): phase 1, the head of the main loop:   *)
(* next_emit = ip++ and the bound of the first probe of the search (see      *)
(* compress_fragment_double_hash_model_spec.ml).                             *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_model_spec.ml";;

let SNAPPY_CF2_GCC12_O2_LOOP1_STMT =
  snappy_cf2_piece_stmt "CompressFragmentDoubleHash_loop1";;

let SNAPPY_CF2_GCC12_O2_LOOP1 = assume_spec SNAPPY_CF2_GCC12_O2_LOOP1_STMT;;
