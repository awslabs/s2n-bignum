(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Regression checks for symbolic execution and shared context tactics. *)

needs "riscv/proofs/base.ml";;

let _ =
  let first = ASSUME `x:num = y`
  and second = ASSUME `x:num = z`
  and conjunction = ASSUME `p /\ q`
  and quantified = ASSUME `!n:num. f n = n + 1` in
  let gen = CACHED_GEN_REWRITE_CONV TOP_DEPTH_CONV
  and repeated = CACHED_CONTEXT_REWRITE_CONV
    true TOP_DEPTH_CONV basic_net in
  let check cached ordinary rules target =
    let expected = ordinary rules target
    and actual = cached rules target in
    if concl actual <> concl expected || hyp actual <> hyp expected then
      failwith "cached context rewriting changed the result or hypotheses" in
  List.iter (fun rules ->
    List.iter (fun target ->
      check gen (GEN_REWRITE_CONV TOP_DEPTH_CONV) rules target;
      check repeated REWRITE_CONV rules target)
     [`x:num`; `f 2:num`; `p /\ q`; `x + 0:num`])
   [[first;second;conjunction;quantified];
    [ASSUME(concl first);ASSUME(concl second);conjunction;quantified];
    [second;first;conjunction;quantified];
    [ADD_ASSUM `hidden:bool` first;conjunction;quantified];
    [conjunction;quantified]; []; [first;conjunction;quantified]];
  let contextual = ADD_ASSUM `hidden:bool` first in
  check gen (GEN_REWRITE_CONV TOP_DEPTH_CONV) [contextual] `x:num`;
  check gen (GEN_REWRITE_CONV TOP_DEPTH_CONV)
    [ADD_ASSUM `other:bool` first] `x:num`;
  check gen (GEN_REWRITE_CONV TOP_DEPTH_CONV) [first] `x:num`;
  check repeated REWRITE_CONV [first] `x + 0:num`;
  let saved = basic_rewrites() in
  set_basic_rewrites[];
  check repeated REWRITE_CONV [first] `x + 0:num`;
  set_basic_rewrites saved;
  check repeated REWRITE_CONV [first] `x + 0:num`;;

let CACHED_REWRITE_INSTANTIATION = prove
 (`!a:num. ?x:num. x < x + 1 /\ a = x`,
  GEN_TAC THEN X_META_EXISTS_TAC `witness:num` THEN
  ASSUME_TAC(SPEC `witness:num` (ARITH_RULE `!n. n < n + 1`)) THEN
  CONJ_TAC THENL
   [CACHED_ASM_REWRITE_TAC [];
    UNIFY_REFL_TAC]);;

(* Rewriting a separation premise to its modular form must retain the
   drivers for subregions, including their original hypotheses. *)

let _ =
  let cases =
   [`nonoverlapping (p:int32,96) (a,1024)`,
    `nonoverlapping (p:int32,96) (word_add a (word 16),16)`;
    `nonoverlapping (p:int64,96) (a,1024)`,
    `nonoverlapping (p:int64,96) (word_add a (word 16),16)`;
    `nonoverlapping (word pc:int64,96) (a,1024)`,
    `nonoverlapping (word pc:int64,96) (word_add a (word 16),16)`;
    `p:int32 = a \/ nonoverlapping (p,96) (a,1024)`,
    `nonoverlapping (p:int32,96) (word_add a (word 128),16)`;
    `p:int64 = a \/ nonoverlapping (p,96) (a,1024)`,
    `nonoverlapping (p:int64,96) (word_add a (word 128),16)`] in
  List.iter (fun (premise,target) ->
    List.iter (fun extra ->
      let original =
        if extra then ADD_ASSUM `hidden:bool` (ASSUME premise)
        else ASSUME premise in
      List.iter (fun fact ->
        let drivers = NONOVERLAPPING_DRIVERS
          [ASSUME `unused:bool`; fact;
           ASSUME `word_add (u:int64) (word 4) = v`] in
        if length drivers <> 3 then
          failwith "nonoverlap driver discarded a separation premise";
        List.iter (fun tm ->
          let proof = NONOVERLAPPING_RULE (drivers,[]) tm in
          if concl proof <> tm || hyp proof <> hyp original then
            failwith "nonoverlap driver changed premise dependencies")
          [target; rand(concl(PURE_ONCE_REWRITE_CONV
                            [NONOVERLAPPING_SYM] target))])
        [original;
         REWRITE_RULE[NONOVERLAPPING_CLAUSES_GEN] original;
         REWRITE_RULE[NONOVERLAPPING_CLAUSES] original])
      [false;true];
    if can (NONOVERLAPPING_RULE (NONOVERLAPPING_DRIVERS [],[])) target then
      failwith "nonoverlap driver proved separation without its premise")
    cases;;

let CLARIFY_DERIVED_LABEL = prove
 (`!p q. p /\ (p ==> q) ==> q`,
  REPEAT STRIP_TAC THEN
  LABEL_TAC "derived"
    (MATCH_MP (ASSUME `p ==> q`) (ASSUME `p:bool`)) THEN
  CLARIFY_TAC THEN
  USE_THEN "derived" ACCEPT_TAC);;

let CLARIFY_UNUSED_FACT = prove
 (`!p q. p /\ q ==> p`,
  REPEAT STRIP_TAC THEN CLARIFY_TAC THEN ASM_REWRITE_TAC[]);;

(* A labelled assumption is already independent. Its theorem need not be
   reapplied during justification, including after a metavariable changes. *)

let CLARIFY_ASSUMED_LABEL = prove
 (`!p:bool. p ==> p`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "assumed") THEN
  CLARIFY_TAC THEN USE_THEN "assumed" ACCEPT_TAC);;

let CLARIFY_CONJUNCTION_LABEL = prove
 (`!p q:bool. p /\ q ==> p /\ q`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "both") THEN
  CLARIFY_TAC THEN USE_THEN "both" ACCEPT_TAC);;

let CLARIFY_ASSUMED_INSTANTIATION = prove
 (`!a:num. a < 3 ==> ?x:num. x < 3 /\ a = x`,
  REPEAT STRIP_TAC THEN X_META_EXISTS_TAC `witness:num` THEN
  CLARIFY_TAC THEN CONJ_TAC THENL
   [ALL_TAC; UNIFY_REFL_TAC] THEN ASM_REWRITE_TAC[]);;

let CLARIFY_INSTANTIATION = prove
 (`!a:num. a < 3 ==> ?x:num. a = x`,
  REPEAT STRIP_TAC THEN
  META_EXISTS_TAC THEN CLARIFY_TAC THEN UNIFY_REFL_TAC);;

let CLARIFY_INSTANTIATED_FACT = prove
 (`!a:num. ?x:num. x < x + 1 /\ a = x`,
  GEN_TAC THEN X_META_EXISTS_TAC `witness:num` THEN
  LABEL_TAC "bound"
    (SPEC `witness:num` (ARITH_RULE `!n. n < n + 1`)) THEN
  CLARIFY_TAC THEN CONJ_TAC THENL
   [USE_THEN "bound" ACCEPT_TAC; UNIFY_REFL_TAC]);;

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
