(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The piece from loop4: a step of the backtracking whose bound              *)
(* (next_emit < ip, base < candidate) is checked. The bytes before ip and    *)
(* candidate are compared; if they differ, join5 (phase 3); if they agree,   *)
(* ip, candidate and the length are stepped back and the bound is checked    *)
(* again: loop4 (phase 7) or join5 (phase 3, two steps of the model).        *)
(*                                                                           *)
(*   +0x180 ldurb w7, [x8, #-1]     +0x168 sub   x8, x8, #0x1               *)
(*   +0x184 ldurb w6, [x14, #-1]    +0x16c sub   x14, x14, #0x1             *)
(*   +0x188 cmp   w7, w6            +0x170 cmp   x1, x8                     *)
(*   +0x18c b.eq  +0x168            +0x174 add   w4, w4, #0x1               *)
(*   (join5 +0x190)                 +0x178 ccmp  x0, x14, #0x2, cc          *)
(*                                  +0x17c b.cs  join5   (else loop4)       *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_loop4_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_lib.ml";;

let SNAPPY_CF2_GCC12_O2_LOOP4 = prove
 (SNAPPY_CF2_GCC12_O2_LOOP4_STMT,
  CF2_PIECE_START_TAC THEN CF2_INIT_TAC THEN
  CF2_BT_BODY_TAC SNAPPY_CF2_GCC12_O2_EXEC 1);;
