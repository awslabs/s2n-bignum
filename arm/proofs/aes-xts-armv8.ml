(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

use_file_raise_failure := true;;

needs "arm/proofs/base.ml";;

print_literal_from_elf "arm/aes-xts/aes-xts-armv8.o";;
