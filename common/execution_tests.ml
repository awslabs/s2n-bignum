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
