(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* DecompressBranchless<char*>: the leaves of                              *)
(* decompress_branchless_near1_spec.ml.                                               *)

needs "arm/proofs/snappy/gcc12_O2/decompress_branchless_near1_spec.ml";;

let SNAPPY_DB_TAG_NEAR1 = prove(SNAPPY_DB_TAG_NEAR1_STMT,
  ACCEPT_TAC(end_itlist CONJ (map (db_near_leaf 1) (0--10))));;
