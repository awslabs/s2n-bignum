(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* RISC-V instruction-level integration checks for immutable reads and
   parent snapshots. Shared tactic checks live under common/.
   Run with `make -C riscv test_execution`. *)

needs "riscv/proofs/base.ml";;

(* Load immutable memory, store to mutable memory, then read both again.
   The later immutable load needs the preceding frame while its new
   register value is simplified; the mutable read must see the store. *)

let read_only_mc = define_word_list "read_only_mc"
 `[word 0x83; word 0x22; word 0x05; word 0x00;
   word 0x23; word 0xa0; word 0x55; word 0x00;
   word 0x03; word 0x23; word 0x05; word 0x00;
   word 0x83; word 0xa3; word 0x05; word 0x00]:byte list`;;

let READ_ONLY_EXEC = RISCV_MK_EXEC_RULE read_only_mc;;

let READ_ONLY_SYMBOLIC_EXECUTION = prove
 (`!pc (p:int32) q x y.
    aligned 4 p /\ aligned 4 q /\
    nonoverlapping (word pc,LENGTH read_only_mc) (q,4) /\
    nonoverlapping (q,4) (p,4)
    ==> ensures riscv
      (\s. aligned_bytes_loaded s (word pc) read_only_mc /\
           read PC s = word pc /\
           read A0 s = p /\ read A1 s = q /\
           read (memory :> bytes32 p) s = x /\
           read (memory :> bytes32 q) s = y)
      (\s. read PC s = word(pc + 16) /\
           read T1 s = x /\ read T2 s = x /\
           read (memory :> bytes32 q) s = x)
      (MAYCHANGE [PC;T0;T1;T2] ,,
       MAYCHANGE [memory :> bytes32 q] ,, MAYCHANGE [events])`,
  REWRITE_TAC[fst READ_ONLY_EXEC] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC ~seed_frame:true "s0" THEN
  ENSURES_READ_ONLY_MEMORY_TAC THEN
  (fun (asl,_ as gl) ->
    if length(filter (is_frame_read_rule o concl o snd) asl) <> 1
    then failwith "READ_ONLY_SYMBOLIC_EXECUTION expected one immutable read";
    ALL_TAC gl) THEN
  MAP_EVERY (fun n ->
    RISCV_SINGLE_STEP_TAC READ_ONLY_EXEC ("s" ^ string_of_int n) THEN
    (fun (asl,_ as gl) ->
      if length(filter (is_frame_read_rule o concl o snd) asl) <> 1
      then failwith "immutable read was discarded during execution";
      ALL_TAC gl)) (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let SNAPSHOT_SYMBOLIC_EXECUTION = prove
 (`!pc (p:int32) q x y.
    aligned 4 p /\ aligned 4 q /\
    nonoverlapping (word pc,LENGTH read_only_mc) (q,4) /\
    nonoverlapping (q,4) (p,4)
    ==> ensures riscv
      (\s. aligned_bytes_loaded s (word pc) read_only_mc /\
           read PC s = word pc /\
           read A0 s = p /\ read A1 s = q /\
           read (memory :> bytes32 p) s = x /\
           read (memory :> bytes32 q) s = y)
      (\s. read PC s = word(pc + 16) /\
           read T1 s = x /\ read T2 s = x /\
           read (memory :> bytes32 q) s = x)
      (MAYCHANGE [PC;T0;T1;T2] ,,
       MAYCHANGE [memory :> bytes32 q] ,, MAYCHANGE [events])`,
  REWRITE_TAC[fst READ_ONLY_EXEC] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC ~seed_frame:true "s0" THEN
  ENSURES_READ_ONLY_MEMORY_TAC THEN
  WITH_COMPONENT_SNAPSHOTS_TAC [`memory:(riscvstate,int32->byte)component`,
                                "memory_snapshot"]
   (MAP_EVERY (fun n ->
      RISCV_SINGLE_STEP_TAC READ_ONLY_EXEC ("s" ^ string_of_int n) THEN
      (fun (asl,_ as gl) ->
        if length(filter (is_frame_read_rule o concl o snd) asl) <> 1 then
          failwith "snapshot execution discarded an immutable fact";
        ALL_TAC gl)) (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN
    W(fun (asl,_) ->
      CONV_TAC(TOP_DEPTH_CONV(!extra_context_read_CONV(map snd asl)))) THEN
    ASM_REWRITE_TAC[]));;
