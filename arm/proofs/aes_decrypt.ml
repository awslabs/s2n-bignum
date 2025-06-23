(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

use_file_raise_failure := true;;

needs "arm/proofs/base.ml";;

save_literal_from_elf "arm/aes-xts/aes256_decrypt.txt" "arm/aes-xts/aes256_decrypt.o";;

let aes256_decrypt_mc = define_assert_from_elf "aes256_decrypt" "arm/aes-xts/aes256_decrypt.o"
[];;