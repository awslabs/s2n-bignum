(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* CompressFragment (gcc12_O2): the statement of the segment from loop6      *)
(* (phase 4, the head of the emit_match loop). It is proved in               *)
(* compress_fragment_seg4_proof.ml, a job of its own in the link; the proof  *)
(* of CompressFragment uses it as a contract (common/relative.ml).           *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_lib.ml";;

let SNAPPY_CF1_SEG4 = assume_spec SNAPPY_CF1_SEG4_STMT;;
