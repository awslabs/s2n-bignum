(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Checks of the ISA-independent snappy specification (common/snappy).       *)
(* ========================================================================= *)

needs "common/snappy/snappy_roundtrip.ml";;
needs "common/snappy/snappy_format_tests.ml";;
needs "common/snappy/snappy_compress_tests.ml";;

List.iter (fun th -> Printf.printf "%s\n%!" (string_of_thm th))
  [SNAPPY_COMPRESS_ROUNDTRIP; SNAPPY_COMPRESS_LENGTH];;
