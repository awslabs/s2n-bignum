(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The piece of CompressFragmentDoubleHash from join5                        *)
(* (CompressFragmentDoubleHash_join5): phase 3, the three table updates and  *)
(* EmitLiteral of [next_emit, ip) (see                                       *)
(* compress_fragment_double_hash_model_spec.ml).                             *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_model_spec.ml";;

let SNAPPY_CF2_GCC12_O2_JOIN5_STMT =
  snappy_cf2_piece_stmt "CompressFragmentDoubleHash_join5";;

let SNAPPY_CF2_GCC12_O2_JOIN5 = assume_spec SNAPPY_CF2_GCC12_O2_JOIN5_STMT;;
