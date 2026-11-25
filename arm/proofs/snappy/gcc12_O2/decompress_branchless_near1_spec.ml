(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* DecompressBranchless<char*> (gcc12_O2): the leaves of the tag segment     *)
(* for the copies with a 1-byte offset, offsets 0..10                        *)
(* (Copy64BytesWithPatternExtension, the offset below the length), as        *)
(* one conjunction. Proved in decompress_branchless_near1_proof.ml,          *)
(* a job of its own in the link.                                             *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/decompress_branchless_lib.ml";;

let SNAPPY_DB_TAG_NEAR1_STMT = db_near_leaves_stmt 1 (0--10);;

let SNAPPY_DB_TAG_NEAR1 = assume_spec SNAPPY_DB_TAG_NEAR1_STMT;;
