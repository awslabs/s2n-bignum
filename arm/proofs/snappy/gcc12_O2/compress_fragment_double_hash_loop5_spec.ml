(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The piece of CompressFragmentDoubleHash from loop5                        *)
(* (CompressFragmentDoubleHash_loop5): phase 4, the head of the copy loop:   *)
(* EmitCopy, the table updates and the checks for a next match (see          *)
(* compress_fragment_double_hash_model_spec.ml).                             *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_fml_spec.ml";;

let SNAPPY_CF2_GCC12_O2_LOOP5_STMT =
  snappy_cf2_piece_stmt "CompressFragmentDoubleHash_loop5";;

let SNAPPY_CF2_GCC12_O2_LOOP5 = assume_spec SNAPPY_CF2_GCC12_O2_LOOP5_STMT;;
