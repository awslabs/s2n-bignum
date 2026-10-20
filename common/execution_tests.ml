(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Regression checks for shared frame and snapshot tactics.
   The RV32 state supplies concrete memory and register components; these
   checks do not execute instructions or claim ARM/x86 coverage.
   Run with `make -C common test_execution`. *)

needs "riscv/proofs/base.ml";;

let ASSIGNS_ABSORB_CONTAINED = prove
 (`!a:int32.
    ASSIGNS (memory :> bytes(a,64)) ,,
    ASSIGNS (memory :> bytes32(word_add a (word 4))) =
    ASSIGNS (memory :> bytes(a,64))`,
  GEN_TAC THEN CONV_TAC(LAND_CONV ASSIGNS_ABSORB_CONV) THEN REFL_TAC);;

let _ =
  let frame = ASSUME
    `(MAYCHANGE [PC] ,, MAYCHANGE [memory :> bytes(a,64)])
       (s0:riscvstate) s` in
  let update = ASSUME
    `write PC pc
       (write (memory :> bytes32(word_add a (word 4))) v
          (s:riscvstate)) = s'` in
  let updated = MAYCHANGE_UPDATE_RULE update frame in
  if rator(rator(concl updated)) <> rator(rator(concl frame))
  then failwith "MAYCHANGE_UPDATE_RULE grew a frame for a contained write";;

let _ =
  if can ASSIGNS_ABSORB_CONV
    `ASSIGNS (memory :> bytes(a,64)) ,,
     ASSIGNS (memory :> bytes32(word_add (a:int32) (word 64)))`
  then failwith "ASSIGNS_ABSORB_CONV absorbed an out-of-range write";;

let CHECK_INITIAL_FRAME_TAC expected (asl,w as gl) =
  let frame = find (maychange_term o concl o snd) asl |> snd in
  if rator(rator(concl frame)) <> expected
  then failwith "ENSURES_INIT_TAC chose the wrong initial frame";
  ALL_TAC gl;;

let ENSURES_INIT_REQUESTED_FRAME = prove
 (`!a:int32.
    ensures (\s s':riscvstate. s' = s) (\s. T) (\s. T)
      (MAYCHANGE [PC] ,, MAYCHANGE [memory :> bytes(a,64)])`,
  GEN_TAC THEN ENSURES_INIT_TAC ~seed_frame:true "s0" THEN
  CHECK_INITIAL_FRAME_TAC
    `MAYCHANGE [PC] ,, MAYCHANGE [memory :> bytes(a,64)]` THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[]);;

let ENSURES_N_INIT_REQUESTED_FRAME = prove
 (`ensures_n (\s s':riscvstate. s' = s) (\s. T) (\s. T)
    (MAYCHANGE [PC]) (\s. 0)`,
  ENSURES_INIT_TAC ~seed_frame:true "s0" THEN
  CHECK_INITIAL_FRAME_TAC `MAYCHANGE [PC]` THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[]);;

let ENSURES_INIT_FALLBACK_FRAME = prove
 (`ensures (\s s':riscvstate. s' = s) (\s. T) (\s. T)
    (\s s'. s = s')`,
  ENSURES_INIT_TAC ~seed_frame:true "s0" THEN
  (fun (asl,w as gl) ->
    let frame = find (maychange_term o concl o snd) asl |> snd in
    let relation = rator(rator(concl frame)) in
    if name_of(fst(strip_comb relation)) <> "MAYCHANGE" ||
       dest_list(rand relation) <> []
    then failwith "ENSURES_INIT_TAC did not retain the empty-frame fallback";
    ALL_TAC gl) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[]);;
