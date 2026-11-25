(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* CompressFragment: the segment from loop6 in the case ML < 8.              *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_seg4a_spec.ml";;

(* The arithmetic of the lib's tactics without the last try with all facts, *)
(* for this proof (snappy_arith_full is per domain).                        *)
snappy_arith_full () := false;;

let SNAPPY_CF1_SEG4A = prove(SNAPPY_CF1_SEG4A_STMT, S4_SEG_TAC);;

snappy_arith_full () := true;;
