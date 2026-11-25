(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* DecompressBranchless<char*> (gcc12_O2): the leaves of the tag segment     *)
(* for the copies with a 2-byte offset, offsets 0..8                         *)
(* (Copy64BytesWithPatternExtension, the offset below the length), as        *)
(* one conjunction. Proved in decompress_branchless_near2a_proof.ml,         *)
(* a job of its own in the link.                                             *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/decompress_branchless_lib.ml";;

let SNAPPY_DB_TAG_NEAR2A_STMT = db_near_leaves_stmt 2 (0--8);;

let SNAPPY_DB_TAG_NEAR2A = assume_spec SNAPPY_DB_TAG_NEAR2A_STMT;;
