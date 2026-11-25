(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* The lemma of length_minus_offset_lemmas_spec.ml.                          *)

needs "arm/proofs/snappy/gcc12_O2/length_minus_offset_lemmas_spec.ml";;

let SNAPPY_LMO_TABLE = prove(SNAPPY_LMO_TABLE_STMT, SNAPPY_LMO_TABLE_TAC);;
