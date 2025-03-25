(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

use_file_raise_failure := true;;

needs "arm/proofs/base.ml";;

(* print_literal_from_elf "arm/aes-xts/aes-xts-armv8.o";; *)
save_literal_from_elf "arm/aes-xts/aes-xts-armv8.txt" "arm/aes-xts/aes-xts-armv8.o";;

(* let aes_xts_armv8 = define_assert_from_elf "aes_xts_armv8" "arm/aes-xts/aes-xts-armv8.o" ..*)

(* Missing instructions that were added in PR#211
4c4070a6   10: 4c4070a6      ld1.16b { v6 }, [x5]
4cdfa87c   5c: 4cdfa87c      ld1.4s  { v28, v29 }, [x3], #32
d503201f   f8: d503201f      nop
4cc87000   198: 4cc87000      ld1.16b { v0 }, [x0], x8
4c40a870   19c: 4c40a870      ld1.4s  { v16, v17 }, [x3]
3875682f   818: 3875682f      ldrb    w15, [x1, x21]
*)