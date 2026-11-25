(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The piece of CompressFragmentDoubleHash from join4                        *)
(* (CompressFragmentDoubleHash_join4): phase 7, the head of the backtracking *)
(* loop: its bound, then a step (see                                         *)
(* compress_fragment_double_hash_model_spec.ml).                             *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_model_spec.ml";;

let SNAPPY_CF2_GCC12_O2_JOIN4_STMT =
  snappy_cf2_piece_stmt "CompressFragmentDoubleHash_join4";;

let SNAPPY_CF2_GCC12_O2_JOIN4 = assume_spec SNAPPY_CF2_GCC12_O2_JOIN4_STMT;;
