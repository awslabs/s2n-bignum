(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The piece of CompressFragmentDoubleHash from loop4                        *)
(* (CompressFragmentDoubleHash_loop4): phase 7, a step of the backtracking   *)
(* loop whose bound is checked (see                                          *)
(* compress_fragment_double_hash_model_spec.ml).                             *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_model_spec.ml";;

let SNAPPY_CF2_GCC12_O2_LOOP4_STMT =
  snappy_cf2_piece_stmt "CompressFragmentDoubleHash_loop4";;

let SNAPPY_CF2_GCC12_O2_LOOP4 = assume_spec SNAPPY_CF2_GCC12_O2_LOOP4_STMT;;
