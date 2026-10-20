(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* No-op stores still need a current-state parent equation. *)
needs "riscv/proofs/base.ml";;

let with_snapshot_parent tac gl =
  let saved = !component_snapshot_parents in
  component_snapshot_parents :=
    [`memory:(riscvstate,int32->byte)component`];
  match tac gl with
  | result -> component_snapshot_parents := saved; result
  | exception error -> component_snapshot_parents := saved; raise error;;

let SNAPSHOT_NOOP_READ = prove
 (`!(s0:riscvstate) s1 (p:int32) a (m:int32->byte) v x.
    read memory s0 = m /\
    read (bytes32 a) m = x /\
    write (bytes32 p) v m = m /\
    write (memory :> bytes32 p) v s0 = s1
    ==> read (memory :> bytes32 a) s1 = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  with_snapshot_parent
   (W(fun (asl,_) ->
      let update = find (fun (_,th) ->
        concl th = `write (memory :> bytes32 p) v (s0:riscvstate) = s1`)
        asl |> snd in
      COMPONENT_SNAPSHOT_UPDATE_TAC update) THEN
    W(fun (asl,_) ->
      CONV_TAC(LAND_CONV(!extra_context_read_CONV(map snd asl)))) THEN
    ASM_REWRITE_TAC[]));;

let SNAPSHOT_NOOP_CONTINUATION = prove
 (`!(s0:riscvstate) s1 s2 (p:int32) (m:int32->byte) v w.
    read memory s0 = m /\
    write (bytes32 p) v m = m /\
    write (memory :> bytes32 p) v s0 = s1 /\
    write (memory :> bytes32 p) w s1 = s2
    ==> read (memory :> bytes32 p) s2 = w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  with_snapshot_parent
   (MAP_EVERY (fun update ->
      W(fun (asl,_) ->
        let th = find (fun (_,th) -> concl th = update) asl |> snd in
        COMPONENT_SNAPSHOT_UPDATE_TAC th))
     [`write (memory :> bytes32 p) v (s0:riscvstate) = s1`;
      `write (memory :> bytes32 p) w (s1:riscvstate) = s2`] THEN
    W(fun (asl,_) ->
      CONV_TAC(LAND_CONV(!extra_context_read_CONV(map snd asl)))) THEN
    ASM_REWRITE_TAC[]));;

let () =
  if hyp SNAPSHOT_NOOP_READ <> [] || hyp SNAPSHOT_NOOP_CONTINUATION <> []
  then failwith "Snapshot no-op regressions retained hypotheses";
  Printf.printf "SNAPSHOT_NOOP_CONTINUATION_REGRESSIONS_PASSED\n%!";;
