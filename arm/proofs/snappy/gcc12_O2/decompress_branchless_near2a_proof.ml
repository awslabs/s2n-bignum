(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* DecompressBranchless<char*>: the leaves of                              *)
(* decompress_branchless_near2a_spec.ml.                                              *)

needs "arm/proofs/snappy/gcc12_O2/decompress_branchless_near2a_spec.ml";;

let SNAPPY_DB_TAG_NEAR2A = prove(SNAPPY_DB_TAG_NEAR2A_STMT,
  ACCEPT_TAC(end_itlist CONJ (map (db_near_leaf 2) (0--8))));;
