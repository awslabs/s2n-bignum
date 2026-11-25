(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* DecompressAllTags<SnappyArrayWriter>: the segment T_B, class COPY4.      *)

needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_t_b_copy4_spec.ml";;

let SNAPPY_DAT_SAW_T_B_COPY4 = prove(SNAPPY_DAT_SAW_T_B_COPY4_STMT, DAW_T_CLASS_TAC true "COPY4");;
