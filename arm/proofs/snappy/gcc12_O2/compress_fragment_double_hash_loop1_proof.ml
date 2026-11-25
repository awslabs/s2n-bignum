(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The piece from loop1: next_emit = ip++, data = Load64(ip), the entry of   *)
(* table2 for it, and the bound of the first probe (ip + 1 > ip_limit goes   *)
(* to emit_remainder with ip = next_emit, i.e. two steps of the model).      *)
(*                                                                           *)
(*   +0x44  ldur  x16, [x1, #1]          +0x58  add   x4, x5, x4            *)
(*   +0x48  add   x17, x1, #0x2          +0x5c  cmp   x17, x10              *)
(*   +0x4c  add   x8, x1, #0x1           +0x60  b.hi  join1                 *)
(*   +0x50  mul   x4, x16, x11           +0x64  mov   w18, #0x201  (loop2)  *)
(*   +0x54  and   x4, x9, x4, lsr #49    join1: mov x0, x2      (join2)     *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_loop1_spec.ml";;

let SNAPPY_CF2_GCC12_O2_LOOP1 = prove
 (SNAPPY_CF2_GCC12_O2_LOOP1_STMT,
  CF2_PIECE_START_TAC THEN CF2_INIT_TAC THEN
  CF2_INPUT_TAC SNAPPY_READ_LOAD64 `ip + 1` THEN
  ARM_BSTEP_TAC SNAPPY_CF2_GCC12_O2_EXEC (1--8) THEN
  CF2_BRANCH_TAC `LENGTH(src:byte list) - 15 < ip + 2` THENL
   [ARM_BSTEP_TAC SNAPPY_CF2_GCC12_O2_EXEC (9--9) THEN BSTEP_FINAL_TAC THEN
    CF2_TARGET_TAC `CompressFragmentDoubleHash_join2:num`
     `SnappyCState 5 ip ip 513 c x t1 t2 out`
     [`SnappyCState 2 (ip + 1) ip 512 c x t1 t2 out`];
    ARM_BSTEP_TAC SNAPPY_CF2_GCC12_O2_EXEC (9--9) THEN BSTEP_FINAL_TAC THEN
    CF2_TARGET_TAC `CompressFragmentDoubleHash_loop2:num`
     `SnappyCState 2 (ip + 1) ip 512 c x t1 t2 out` []]);;
