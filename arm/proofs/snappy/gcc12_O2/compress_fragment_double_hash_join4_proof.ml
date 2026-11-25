(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The piece from join4: the head of the backtracking. If base < candidate   *)
(* and next_emit < ip, the step of loop4 follows (as in the proof of loop4,  *)
(* with the same tactics, compress_fragment_double_hash_lib.ml); otherwise   *)
(* join5 (phase 3).                                                          *)
(*                                                                           *)
(*   +0x158 cmp   x0, x14                                                    *)
(*   +0x15c ccmp  x1, x8, #0x2, cc                                           *)
(*   +0x160 b.cc  loop4                                                      *)
(*   +0x164 b     join5                                                      *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_join4_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_lib.ml";;

let SNAPPY_CF2_GCC12_O2_JOIN4 = prove
 (SNAPPY_CF2_GCC12_O2_JOIN4_STMT,
  CF2_PIECE_START_TAC THEN CF2_INIT_TAC THEN
  ARM_BSTEP_TAC SNAPPY_CF2_GCC12_O2_EXEC (1--3) THEN
  CF2_BT_BRANCH_TAC (CF2_BT_CARRY_EQ_TAC [`c:num`; `ne:num`; `ip:num`])
   `ne < ip /\ 0 < c` THENL
   [CF2_BT_BODY_TAC SNAPPY_CF2_GCC12_O2_EXEC 4;
    ARM_BSTEP_TAC SNAPPY_CF2_GCC12_O2_EXEC (4--4) THEN BSTEP_FINAL_TAC THEN
    CF2_BT_TARGET_TAC `CompressFragmentDoubleHash_join5:num`
     `SnappyCState 3 ip ne sk c x t1 t2 out` []]);;
