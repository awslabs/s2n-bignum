(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* DecompressBranchless<char*>: the leaves of                              *)
(* decompress_branchless_near2b_spec.ml.                                              *)

needs "arm/proofs/snappy/gcc12_O2/decompress_branchless_near2b_spec.ml";;

let SNAPPY_DB_TAG_NEAR2B = prove(SNAPPY_DB_TAG_NEAR2B_STMT,
  ACCEPT_TAC(end_itlist CONJ (map (db_near_leaf 2) (9--16))));;
