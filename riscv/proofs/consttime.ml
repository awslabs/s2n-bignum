(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tactics for proving constant-time and memory-safety properties in RV32.   *)
(* ========================================================================= *)

needs "riscv/proofs/base.ml";;
needs "common/consttime.ml";;

(* Sanity check for architecture *)
let _ = match `:armstate`,`:x86state`,`:riscvstate` with
  | (Tyvar _),(Tyvar _),(Tyapp (_, [])) -> ()
  | (Tyapp (_, [])),(Tyvar _),(Tyvar _) ->
      failwith "this file cannot be loaded from arm"
  | (Tyvar _),(Tyapp (_, [])),(Tyvar _) ->
      failwith "this file cannot be loaded from x86"
  | _,_,_ -> failwith "Unknown case";;

(* Specialize the common safety-specification builder to the RV32 memory,
   event, PC, SP, and RA components. The argument tuple describes the public
   function arguments and its input, output, and temporary memory regions. *)

let mk_safety_spec
    ?(readonly_objects=([]:(term * term)list))
    ~(keep_maychanges:bool)
    (fnargs,xx,meminputs,memoutputs,memtemps)
    (subroutine_correct_th:thm) exec: term*(term list) =
  let read_sth_eq (f:term->bool):term->bool =
    fun t -> is_eq t && let l = lhs t in is_binary "read" l &&
      let l' = fst (dest_binary "read" l) in f l' in
  gen_mk_safety_spec ~readonly_objects
    ~memory_component:`memory` ~events_component:`events` ~is_read_pc
    ~keep_maychanges
    (fnargs,xx,meminputs,memoutputs,memtemps)
    subroutine_correct_th exec
    (read_sth_eq (fun t -> t = `SP`))
    (read_sth_eq (fun t -> t = `RA`));;

(* Prove a generated RV32 safety specification by symbolically executing with
   `RISCV_SINGLE_STEP_TAC`. `exec` is the result of `RISCV_MK_EXEC_RULE`; the
   optional list identifies additional public HOL variables. *)

let PROVE_SAFETY_SPEC_TAC ?(public_vars:term list option) exec:tactic =
  GEN_PROVE_SAFETY_SPEC_TAC ?public_vars:public_vars exec
    [ALIGNED_BYTES_LOADED_APPEND_CLAUSE;
     MAYCHANGE_REGS_PERMITTED_BY_ABI]
    RISCV_SINGLE_STEP_TAC;;
