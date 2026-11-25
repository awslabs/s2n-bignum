(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* The segment T_B, tag class LIT, of DecompressAllTags<Validator>       *)
(* (snappy_decompressor_decompress_all_tags_validator_t_b_lit_spec.ml).     *)

needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_validator_t_b_lit_spec.ml";;

let SNAPPY_DAT_VALIDATOR_T_B_LIT = prove(SNAPPY_DAT_VALIDATOR_T_B_LIT_STMT, DAT_T_CLASS_TAC "B" "LIT");;

tactic_timing_report "SNAPPY_DAT_VALIDATOR_T_B_LIT";;
