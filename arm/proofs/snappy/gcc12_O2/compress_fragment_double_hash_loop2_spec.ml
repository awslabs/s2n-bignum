(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The piece of CompressFragmentDoubleHash from loop2                        *)
(* (CompressFragmentDoubleHash_loop2): phase 2, a probe of the search at ip  *)
(* with both tables, and FindMatchLengthPlain if a candidate matches (see    *)
(* compress_fragment_double_hash_model_spec.ml).                             *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_fml_spec.ml";;

let SNAPPY_CF2_GCC12_O2_LOOP2_STMT =
  snappy_cf2_piece_stmt "CompressFragmentDoubleHash_loop2";;

let SNAPPY_CF2_GCC12_O2_LOOP2 = assume_spec SNAPPY_CF2_GCC12_O2_LOOP2_STMT;;
