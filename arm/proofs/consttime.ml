(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(*   Tactics for proving constant-time and memory-safety properties in Arm.  *)
(* ========================================================================= *)

needs "common/consttime.ml";;

(* Sanity check for architecture *)
let _ = match `:x86state`,`:armstate` with
  | (Tyvar _),(Tyapp (_, [])) -> ()
  | (Tyapp (_, [])),(Tyvar _) -> failwith "this file cannot be loaded from x86"
  | _,_ -> failwith "Unknown case";;

let mk_safety_spec
    ?(readonly_objects=([]:(term * term)list))
    ~(keep_maychanges:bool)
    (fnargs,xx,meminputs,memoutputs,memtemps)
    (subroutine_correct_th:thm) exec: term*(term list) =
  let read_sth_eq (f:term->bool):term->bool =
    fun t -> is_eq t && let l = lhs t in is_binary "read" l &&
      let l' = fst (dest_binary "read" l) in f l' in
  gen_mk_safety_spec ~readonly_objects ~keep_maychanges
    (fnargs,xx,meminputs,memoutputs,memtemps)
    subroutine_correct_th exec
    (read_sth_eq (fun t -> t = `SP`)) (read_sth_eq (fun t -> t = `X30`));;

let PROVE_SAFETY_SPEC_TAC ?(public_vars:term list option) exec:tactic =
  GEN_PROVE_SAFETY_SPEC_TAC ?public_vars:public_vars exec
    [ALIGNED_BYTES_LOADED_APPEND_CLAUSE;MODIFIABLE_SIMD_REGS;
     MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
    ARM_SINGLE_STEP_TAC;;
