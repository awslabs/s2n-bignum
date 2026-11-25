(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* CompressFragment: the segment from loop6 in the case 64 <= ML, s4_rest <= 64. *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_seg4d_spec.ml";;

(* The arithmetic of the lib's tactics without the last try with all facts, *)
(* for this proof (snappy_arith_full is per domain).                        *)
snappy_arith_full () := false;;

let SNAPPY_CF1_SEG4D = prove(SNAPPY_CF1_SEG4D_STMT, S4_SEG_TAC);;

snappy_arith_full () := true;;
