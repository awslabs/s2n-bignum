(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* DecompressBranchless<char*> (gcc12_O2): the lemmas of                     *)
(* decompress_branchless_lib.ml that it states without proving it           *)
(* (assuming_proofs): DB_AND255_X_STMT, proved in                            *)
(* decompress_branchless_lemmas_proof.ml, a job of its own. (The table       *)
(* kLengthMinusOffset is length_minus_offset_lib.ml's.)                      *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/decompress_branchless_lib.ml";;
