(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Default initialization must retain the precise observed write frame. *)

needs "riscv/tutorial/simple.ml";;

let CHECK_OBSERVED_FRAME_TAC expected (asl,w as gl) =
  let frame = find (maychange_term o concl o snd) asl |> snd in
  if rator(rator(concl frame)) <> expected then
    failwith "ENSURES_INIT_TAC changed the observed write frame";
  ALL_TAC gl;;

let CHECK_EMPTY_INITIAL_FRAME_TAC (asl,w as gl) =
  let frame = find (maychange_term o concl o snd) asl |> snd in
  let relation = rator(rator(concl frame)) in
  if name_of(fst(strip_comb relation)) <> "MAYCHANGE" ||
     dest_list(rand relation) <> []
  then failwith "ENSURES_INIT_TAC changed the default empty starter";
  ALL_TAC gl;;

let ENSURES_INIT_OBSERVED_FRAME_DEFAULT = prove
 (`!a:int32.
    ensures (\s s':riscvstate. s' = s) (\s. T) (\s. T)
      (MAYCHANGE [PC] ,, MAYCHANGE [memory :> bytes(a,64)])`,
  GEN_TAC THEN ENSURES_INIT_TAC "s0" THEN
  CHECK_EMPTY_INITIAL_FRAME_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[]);;

let ENSURES_N_INIT_OBSERVED_FRAME_DEFAULT = prove
 (`ensures_n (\s s':riscvstate. s' = s) (\s. T) (\s. T)
    (MAYCHANGE [PC]) (\s. 0)`,
  ENSURES_INIT_TAC "s0" THEN CHECK_EMPTY_INITIAL_FRAME_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[]);;

(* A0 is permitted to change but is not written by the instruction. *)
let ENSURES_INIT_PRECISE_STEP_FRAME = prove
 (`!pc x.
    ensures riscv
      (\s. aligned_bytes_loaded s (word pc) pc_wrap_mc /\
           read PC s = word pc /\ read A0 s = x)
      (\s. read PC s = word(pc + 4) /\ read A0 s = x)
      (MAYCHANGE [PC;A0] ,, MAYCHANGE [events])`,
  REWRITE_TAC[fst PC_WRAP_EXEC] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC PC_WRAP_EXEC [1] THEN
  CHECK_OBSERVED_FRAME_TAC `MAYCHANGE [PC]` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;
