(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* CompressFragment, the segment from loop6 (SNAPPY_CF1_SEG4, stated in      *)
(* compress_fragment_seg4_spec.ml) from its five cases by the match length  *)
(* (compress_fragment_seg4{a,...,e}_spec.ml, proved as jobs of their own;   *)
(* the lemmas and tactics are in compress_fragment_seg4_lib.ml).            *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_seg4_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_seg4a_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_seg4b_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_seg4c_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_seg4d_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_seg4e_spec.ml";;

let SNAPPY_CF1_SEG4 = prove
 (SNAPPY_CF1_SEG4_STMT,
  S4_FROM_CASES_TAC [SNAPPY_CF1_SEG4A; SNAPPY_CF1_SEG4B; SNAPPY_CF1_SEG4C;
                     SNAPPY_CF1_SEG4D; SNAPPY_CF1_SEG4E]);;
