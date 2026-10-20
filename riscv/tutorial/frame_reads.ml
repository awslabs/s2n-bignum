(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Guarded reads must survive frame growth requiring contextual containment. *)
needs "riscv/proofs/base.ml";;

let frame_read_mc = define_word_list "frame_read_mc"
 `[word 0x83; word 0x22; word 0x05; word 0x00;
   word 0x23; word 0xa0; word 0x55; word 0x00;
   word 0x03; word 0x23; word 0x05; word 0x00;
   word 0x83; word 0xa3; word 0x05; word 0x00]:byte list`;;

let FRAME_READ_EXEC = RISCV_MK_EXEC_RULE frame_read_mc;;

let frame_read_symbolic_statement =
 `!pc (p:int32) q x y n.
    4 <= n /\ aligned 4 p /\ aligned 4 q /\
    nonoverlapping (word pc,LENGTH frame_read_mc) (q,n) /\
    nonoverlapping (q,n) (p,4)
    ==> ensures riscv
      (\s. aligned_bytes_loaded s (word pc) frame_read_mc /\
           read PC s = word pc /\
           read A0 s = p /\ read A1 s = q /\
           read (memory :> bytes32 p) s = x /\
           read (memory :> bytes32 q) s = y)
      (\s. read PC s = word(pc + 16) /\
           read T1 s = x /\ read T2 s = x /\
           read (memory :> bytes32 q) s = x)
      (MAYCHANGE [PC;T0;T1;T2] ,,
       MAYCHANGE [memory :> bytes(q,n)] ,, MAYCHANGE [events])`;;

let frame_read_symbolic_tac promote =
  REWRITE_TAC[fst FRAME_READ_EXEC] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC ~seed_frame:true "s0" THEN
  (if promote then ENSURES_READ_ONLY_MEMORY_TAC else ALL_TAC) THEN
  MAP_EVERY (fun n ->
    RISCV_SINGLE_STEP_TAC FRAME_READ_EXEC ("s" ^ string_of_int n))
    (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let FRAME_READ_SYMBOLIC_CONTROL = prove
 (frame_read_symbolic_statement,frame_read_symbolic_tac false);;
let FRAME_READ_SYMBOLIC_PROMOTED = prove
 (frame_read_symbolic_statement,frame_read_symbolic_tac true);;

let () =
  List.iter (fun th ->
    if hyp th <> [] || concl th <> frame_read_symbolic_statement then
      failwith "Symbolic frame read changed its closed claim")
    [FRAME_READ_SYMBOLIC_CONTROL;FRAME_READ_SYMBOLIC_PROMOTED];;

(* A derived guard must retain its bound and hidden hypotheses, and must not
   be reused after the context or initial state changes. *)
let () =
  let rule = ASSUME
    `!s:riscvstate.
      MAYCHANGE [memory :> bytes(q,n)] s0 s ==>
      read (memory :> bytes32 p) s = x` in
  let frame = ASSUME
    `(MAYCHANGE [memory :> bytes(q,n)] ,,
      MAYCHANGE [memory :> bytes32 q]) (s0:riscvstate) s1` in
  let bound = ADD_ASSUM `frame_read_dependency:bool` (ASSUME `4 <= n`) in
  let target = `read (memory :> bytes32 p) (s1:riscvstate)` in
  let result = FRAME_READ_CONV [rule;frame;bound] target in
  if concl result <> mk_eq(target,`x:int32`) ||
     hyp result <> hyp(CONJ rule (CONJ frame bound)) then
    failwith "Derived frame guard lost a contextual dependency";
  if can (FRAME_READ_CONV [rule;frame]) target then
    failwith "Derived frame guard reused a missing arithmetic bound";
  let wrong = ASSUME
    `(MAYCHANGE [memory :> bytes(q,n)] ,,
      MAYCHANGE [memory :> bytes32 q]) (other:riscvstate) s1` in
  if can (FRAME_READ_CONV [rule;wrong;bound]) target then
    failwith "Derived frame guard changed the initial state";
  Printf.printf "FRAME_READ_CONTEXTUAL_SUBSUMPTION_REGRESSIONS_PASSED\n%!";;
