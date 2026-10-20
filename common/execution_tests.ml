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
  let frame = find (is_maychange_state_fact o concl o snd) asl |> snd in
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

let FRAME_PRESERVES_MEMORY_READ = prove
 (`!a z:int32. !s s':riscvstate.
    nonoverlapping (a,64) (z,8) /\
    (MAYCHANGE [PC;T0] ,, MAYCHANGE [memory :> bytes(a,64)]) s s' /\
    read (memory :> bytes32 z) s = x
    ==> read (memory :> bytes32 z) s' = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  W(fun (asl,_) ->
    let ths = map snd asl in
    let preservation = FRAME_PRESERVES_COMPONENT_RULE
      (NONOVERLAPPING_DRIVERS ths,FILTER_CANONIZE_ASSUMPTIONS ths)
      `MAYCHANGE [PC;T0] ,, MAYCHANGE [memory :> bytes(a,64)]`
      `memory :> bytes32 z` in
    MP_TAC(SPECL [`s:riscvstate`;`s':riscvstate`] preservation)) THEN
  ASM_REWRITE_TAC[]);;

let _ =
  let frame = `MAYCHANGE [memory :> bytes(a,64)]` in
  if can (FRAME_PRESERVES_COMPONENT_RULE (NONOVERLAPPING_DRIVERS [],[])
    frame) `memory :> bytes32(a:int32)`
  then failwith "FRAME_PRESERVES_COMPONENT_RULE preserved mutable memory";;

let READ_ONLY_MEMORY_PROMOTION = prove
 (`!a z:int32. !s0 s1:riscvstate.
    nonoverlapping (a,64) (z,8) /\
    (MAYCHANGE [PC;T0] ,, MAYCHANGE [memory :> bytes(a,64)]) s0 s0 /\
    read (memory :> bytes32 z) s0 = x /\
    read (memory :> bytes32 a) s0 = y
    ==> (MAYCHANGE [PC;T0] ,, MAYCHANGE [memory :> bytes(a,64)]) s0 s1
    ==> read (memory :> bytes32 z) s1 = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_READ_ONLY_MEMORY_TAC THEN
  DISCH_TAC THEN
  (fun (asl,w as gl) ->
    let ths = map snd asl in
    if not(exists (is_frame_read_rule o concl) ths) then
      failwith "ENSURES_READ_ONLY_MEMORY_TAC did not promote a read";
    if not(exists (fun th ->
      concl th = `read (memory :> bytes32 a) (s0:riscvstate) = y`) ths)
    then failwith "ENSURES_READ_ONLY_MEMORY_TAC removed a mutable read";
    CONV_TAC(LAND_CONV(FRAME_READ_CONV ths)) gl) THEN REFL_TAC);;

let _ =
  let static = ASSUME
    `!s:riscvstate.
      MAYCHANGE [PC] s0 s ==> read (memory :> bytes32 z) s = x` in
  let conv = FRAME_READ_CONV [static] in
  if can conv `read (memory :> bytes32 z) (s1:riscvstate)`
  then failwith "FRAME_READ_CONV ignored the frame guard";;

let _ =
  let static = ASSUME
    `!s:riscvstate. MAYCHANGE [PC] s0 s ==>
      read (memory :> bytes32 z) s = read (memory :> bytes32 z) s` in
  let frame = ASSUME `MAYCHANGE [PC] (s0:riscvstate) s1` in
  if can (FRAME_READ_CONV [static;frame])
    `read (memory :> bytes32 z) (s1:riscvstate)`
  then failwith "FRAME_READ_CONV accepted an unchanged rewrite";;

let _ =
  let static = ASSUME
    `!s:riscvstate.
      MAYCHANGE [PC] s0 s ==> read (memory :> bytes32 z) s = x` in
  let frame = ASSUME `MAYCHANGE [PC] (s0:riscvstate) s1` in
  let target = `read (memory :> bytes32 z) (s1:riscvstate)` in
  ignore(FRAME_READ_CONV [static;frame] target);
  if can (FRAME_READ_CONV [static]) target then
    failwith "FRAME_READ_CONV reused a cached frame";
  let wrong_frame = ASSUME `MAYCHANGE [PC] (s2:riscvstate) s1` in
  if can (FRAME_READ_CONV [static;wrong_frame]) target then
    failwith "FRAME_READ_CONV accepted a different initial state";;

let _ =
  let frame = ASSUME `MAYCHANGE [PC] (s0:riscvstate) s1` in
  let target = `read (memory :> bytes32 z) (s1:riscvstate)` in
  let old = ASSUME
    `!s:riscvstate.
      MAYCHANGE [PC] s0 s ==> read (memory :> bytes32 z) s = x` in
  ignore(FRAME_READ_CONV [old;frame] target);
  let changed = ASSUME
    `!s:riscvstate.
      MAYCHANGE [PC] s0 s ==> read (memory :> bytes32 z) s = y` in
  let result = FRAME_READ_CONV [changed;frame] target in
  if rhs(concl result) <> `y:int32` ||
     exists (fun h -> h <> concl changed && h <> concl frame) (hyp result)
  then failwith "FRAME_READ_CONV reused an old value or hypothesis";;
