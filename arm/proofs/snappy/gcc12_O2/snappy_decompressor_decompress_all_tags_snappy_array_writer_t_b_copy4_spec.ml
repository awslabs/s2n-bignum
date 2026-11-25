(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* DecompressAllTags<SnappyArrayWriter> (gcc12_O2): the segment from the     *)
(* cut point T (one tag of the slow path) with the window in the input (B),  *)
(* restricted to the copy with a 4-byte offset:                              *)
(* a conjunct of the precondition (daw_class_goal). The proof file of        *)
(* the function combines the classes (DAW_T_FROM_CLASSES_TAC).               *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_snappy_array_writer_lib.ml";;

let SNAPPY_DAT_SAW_T_B_COPY4_STMT = daw_class_goal true "COPY4";;

let SNAPPY_DAT_SAW_T_B_COPY4 = assume_spec SNAPPY_DAT_SAW_T_B_COPY4_STMT;;
