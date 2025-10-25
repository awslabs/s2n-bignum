(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(*   Tactics for proving constant-time and memory-safety properties in Arm.  *)
(* ========================================================================= *)

needs "common/consttime.ml";;

let mk_safety_spec
    ?(coda_pc_range:(int*int) option) (* when coda is used: (begin, len) *)
    (fnargs,xx,meminputs,memoutputs,memtemps)
    (subroutine_correct_th:thm) exec: term*(term list) =
  let read_sth_eq (f:term->bool):term->bool =
    fun t -> is_eq t && let l = lhs t in is_binary "read" l &&
      let l' = fst (dest_binary "read" l) in f l' in
  gen_mk_safety_spec ?coda_pc_range (fnargs,xx,meminputs,memoutputs,memtemps)
    subroutine_correct_th exec
    (read_sth_eq (fun t -> t = `SP`)) (read_sth_eq (fun t -> t = `X30`));;

let PROVE_SAFETY_SPEC ?(public_vars:term list option) exec:tactic =
  GEN_PROVE_SAFETY_SPEC ?public_vars:public_vars exec
    [ALIGNED_BYTES_LOADED_APPEND_CLAUSE]
    ARM_SINGLE_STEP_TAC;;
