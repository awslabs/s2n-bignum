(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* bstep for AArch64: see common/bstep.ml.                                   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/consttime.ml";;
needs "common/bstep.ml";;

(* The instruction at offset k, for messages.                                *)

let arm_bstep_insn (decode_ths:thm option array) k =
  match decode_ths.(k) with
    Some th -> string_of_term(rand(rand(snd(strip_forall(concl th)))))
  | None -> "no instruction";;

let arm_bstep_arch =
  { arch_name = "ARM";
    arch_step = `arm`;
    arch_state = `:armstate`;
    arch_pc = `PC`;
    arch_loaded = "aligned_bytes_loaded";
    arch_loaded_update = aligned_bytes_loaded_update;
    arch_conv = ARM_CONV;
    arch_insn = arm_bstep_insn;
    arch_alias = (fun _ -> None) };;

(* ARM_BSTEP_TAC execth (m--n) simulates the steps m..n from the goal        *)
(* `eventually arm P s` after ENSURES_INIT_TAC, leaving a goal about the     *)
(* state "s<n>".                                                             *)

let ARM_BSTEP_TAC = BSTEP_STEPS_TAC arm_bstep_arch;;

(* ARM_BSTEP_SAFETY_TAC ~public_vars execth proves a safety statement made   *)
(* by mk_safety_spec: PROVE_SAFETY_SPEC_TAC with BSTEP_SAFETY_RUN_TAC (see   *)
(* common/bstep.ml), which runs the code in blocks and forgets the data.     *)

let ARM_BSTEP_SAFETY_TAC ?public_vars exec =
  PROVE_SAFETY_SPEC_TAC ?public_vars
    ~run_tac:(BSTEP_SAFETY_RUN_TAC arm_bstep_arch exec) exec;;

(* ARM_BSTEP_CALL_TAC execth th "s<n>" goes through th: |- ensures arm ...   *)
(* (see GEN_BSTEP_CALL_TAC in common/bstep.ml).                              *)

let ARM_BSTEP_CALL_TAC = GEN_BSTEP_CALL_TAC arm_bstep_arch;;

(* ------------------------------------------------------------------------- *)
(* The wrappers of arm/proofs/arm.ml with bstep for the simulation:          *)
(* ARM_BSTEP_SIM_TAC is ARM_SIM_TAC and ARM_BSTEP_ADD_RETURN_STACK_TAC is    *)
(* ARM_ADD_RETURN_STACK_TAC, with the steps done by ARM_BSTEP_TAC, the body  *)
(* of a subroutine gone through by ARM_BSTEP_CALL_TAC and the end by         *)
(* BSTEP_FINAL_TAC.                                                          *)
(*                                                                           *)
(* The initial values of the saved registers are variables (ghosts), as in   *)
(* `word_zx (read Q8 s) = d8_init`; given as ~rewrites, they make the code   *)
(* that saves the registers store these variables. ~tweak is applied to the  *)
(* assumptions and the goal at the start of the prologue, after the saved    *)
(* registers are out of the frame (with coreth tweaked by the caller): a     *)
(* tweak that expands a precondition, such as EXPAND_CASES_CONV on 256       *)
(* elements, would otherwise make the goal that the setup and the frame      *)
(* tactics rewrite many times larger.                                        *)
(* ------------------------------------------------------------------------- *)

let ARM_BSTEP_SIM_TAC execth snums =
  ARM_SIM_TAC ~tactics:((fun execth snums -> ARM_BSTEP_TAC execth snums),
                        BSTEP_FINAL_TAC)
    execth snums;;

let ARM_BSTEP_ADD_RETURN_STACK_TAC =
  let sp_tm = `SP` and x30_tm = `X30`
  and stackpointer = `stackpointer:int64` in
  let keep c = c = sp_tm || c = x30_tm || memory_component_at stackpointer c in
  let ghosts (asl:(string * thm) list) =
    filter (fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(_,Comb(Comb(Const("read",_),_),_))),v)
          -> is_var v
      | _ -> false) (map snd asl) in
  fun ?(tweak=ALL_CONV) ?pre_post_nsteps execth coreth reglist stackoff ->
    ARM_ADD_RETURN_STACK_TAC
      ~tactics:((fun execth snums ->
                   RULE_ASSUM_TAC(CONV_RULE tweak) THEN CONV_TAC tweak THEN
                   W(fun (asl,_) ->
                   ARM_BSTEP_TAC ~rewrites:(ghosts asl) execth snums)),
                (fun execth sname -> DISCH_THEN(fun th ->
                   ARM_BSTEP_CALL_TAC ~keep execth th sname)),
                (fun execth snums -> ARM_BSTEP_TAC execth snums),
                BSTEP_FINAL_TAC)
      ?pre_post_nsteps execth coreth reglist stackoff;;
