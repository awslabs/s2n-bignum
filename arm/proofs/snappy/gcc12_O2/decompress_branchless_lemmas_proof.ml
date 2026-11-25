(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* The lemma of decompress_branchless_lemmas_spec.ml.                        *)

needs "arm/proofs/snappy/gcc12_O2/decompress_branchless_lemmas_spec.ml";;

let DB_AND255_X = prove(DB_AND255_X_STMT, BITBLAST_TAC);;
