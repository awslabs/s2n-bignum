(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* CompressFragment (gcc12_O2): the segment from loop6 (SNAPPY_CF1_SEG4)     *)
(* in the case 60 < ML < 64 of the match length ML                           *)
(* (s4_cases of compress_fragment_seg4_lib.ml), proved in                    *)
(* compress_fragment_seg4c_proof.ml, a job of its own in the link.           *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_seg4_lib.ml";;

let SNAPPY_CF1_SEG4C_STMT = s4_case_stmt (el 2 s4_cases);;

let SNAPPY_CF1_SEG4C = assume_spec SNAPPY_CF1_SEG4C_STMT;;
