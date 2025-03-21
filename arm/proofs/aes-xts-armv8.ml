(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

use_file_raise_failure := true;;

needs "arm/proofs/base.ml";;

(* print_literal_from_elf "arm/aes-xts/aes-xts-armv8.o";; *)
save_literal_from_elf "arm/aes-xts/aes-xts-armv8.txt" "arm/aes-xts/aes-xts-armv8.o";;

(* let aes_xts_armv8 = define_assert_from_elf "aes_xts_armv8" "arm/aes-xts/aes-xts-armv8.o" ..*)
