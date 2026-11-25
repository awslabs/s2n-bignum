(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* bstep for x86: see common/bstep.ml.                                       *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/consttime.ml";;
needs "common/bstep.ml";;

(* The instruction at offset k, for messages.                                *)

let x86_bstep_instruction (decode_ths:thm option array) k =
  match decode_ths.(k) with
    Some th -> rand(rand(rand(snd(strip_forall(concl th)))))
  | None -> failwith "no instruction";;

let x86_bstep_insn (decode_ths:thm option array) k =
  try string_of_term(x86_bstep_instruction decode_ths k)
  with Failure _ -> "no instruction";;

(* The semantics of an instruction such as VMOVDQA checks the alignment of   *)
(* its memory operand and has no successor state if it is not aligned. On    *)
(* a state without facts X86_CONV cannot decide that check and does not      *)
(* stop, so bstep assumes `aligned 16 a` and `aligned 32 a` for the address  *)
(* a of each memory operand. The assumptions the semantics uses stay as      *)
(* hypotheses, and bstep turns them into side conditions of the step.        *)

let x86_bstep_conv =
  let aligned_tm = `aligned:num->int64->bool` in
  let addr = BSID_SEMANTICS_CONV THENC DEPTH_CONV WORD_NUM_RED_CONV in
  fun (decode_ths:thm option array) ths tm ->
    let s = rand(rator tm) in
    let pc_th = find (fun th -> is_eq(concl th) &&
                                is_read_rip(lhs(concl th))) ths in
    let k = match rand(rhs(concl pc_th)) with
        Comb(Comb(Const("+",_),_),kt) -> dest_small_numeral kt
      | _ -> 0 in
    let mems =
      try find_terms (fun t -> match t with
              Comb(Comb(Const("Memop",_),_),_) -> true | _ -> false)
            (x86_bstep_instruction decode_ths k)
      with Failure _ -> [] in
    let als = flat (map (fun m ->
        let a = rand(concl(addr(list_mk_icomb "bsid_semantics" [rand m;s]))) in
        map (fun n ->
               ASSUME(mk_comb(mk_comb(aligned_tm,mk_small_numeral n),a)))
            [16;32]) mems) in
    X86_CONV decode_ths (ths @ als) tm;;

(* SSE instructions write YMM0_SSE (the low half of ZMM0, keeping the top),  *)
(* and reads of YMM0_SSE are reads of YMM0: a write to YMMi_SSE gives the    *)
(* fact for YMMi.                                                            *)

let x86_bstep_alias =
  let y = `y:int256` and t = `t:x86state` in
  let rows = map (fun eq ->
      (* eq: |- !s. read YMMi_SSE s = read YMMi s                            *)
      let l,r = dest_eq(snd(dest_forall(concl eq))) in
      let sse = rand(rator l) and c = rand(rator r) in
      let tm = mk_eq(list_mk_icomb "read" [c;list_mk_icomb "write" [sse;y;t]],
                     y) in
      sse,(c,prove(list_mk_forall([y;t],tm),
        REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM eq] THEN
        CONV_TAC(LAND_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REFL_TAC)))
    READ_YMM_SSE_EQUIV in
  fun d -> try Some(assoc d rows) with Failure _ -> None;;

let x86_bstep_arch =
  { arch_name = "X86";
    arch_step = `x86`;
    arch_state = `:x86state`;
    arch_pc = `RIP`;
    arch_loaded = "bytes_loaded";
    arch_loaded_update = bytes_loaded_update;
    arch_conv = x86_bstep_conv;
    arch_insn = x86_bstep_insn;
    arch_alias = x86_bstep_alias;
    arch_base_facts = (fun _ -> []) };;

(* The frames of the ABI, which contracts and theorems use by name.          *)

bstep_frame_defs := [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                     WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI];;

(* X86_BSTEP_TAC execth (m--n) simulates the steps m..n from the goal        *)
(* `eventually x86 P s` after ENSURES_INIT_TAC, leaving a goal about the     *)
(* state "s<n>". Values the semantics leaves undefined (most flags after     *)
(* XOR, for example) become fresh variables bstep_u<k> in that goal.         *)

let X86_BSTEP_TAC = BSTEP_STEPS_TAC x86_bstep_arch;;

(* X86_BSTEP_SAFETY_TAC ~public_vars execth proves a safety statement made   *)
(* by mk_safety_spec: PROVE_SAFETY_SPEC_TAC with BSTEP_SAFETY_RUN_TAC (see   *)
(* common/bstep.ml), which runs the code in blocks and forgets the data.     *)

let X86_BSTEP_SAFETY_TAC ?public_vars exec =
  PROVE_SAFETY_SPEC_TAC ?public_vars
    ~run_tac:(BSTEP_SAFETY_RUN_TAC x86_bstep_arch exec) exec;;

(* X86_BSTEP_CALL_TAC execth th "s<n>" goes through th: |- ensures x86 ...   *)
(* (see GEN_BSTEP_CALL_TAC in common/bstep.ml).                              *)

let X86_BSTEP_CALL_TAC = GEN_BSTEP_CALL_TAC x86_bstep_arch;;

(* ------------------------------------------------------------------------- *)
(* The wrappers of x86/proofs/x86.ml with bstep for the simulation: the      *)
(* steps done by X86_BSTEP_TAC, the body of a subroutine gone through by     *)
(* X86_BSTEP_CALL_TAC and the end by BSTEP_FINAL_TAC.                        *)
(* ------------------------------------------------------------------------- *)

let x86_bstep_steps execth snums = X86_BSTEP_TAC execth snums;;

let x86_bstep_keep =
  let rsp_tm = `RSP` and stackpointer = `stackpointer:int64` in
  fun c -> c = rsp_tm || memory_component_at stackpointer c;;

let x86_bstep_wrapper_tactics =
  (x86_bstep_steps,
   (fun execth sname -> DISCH_THEN(fun th ->
      X86_BSTEP_CALL_TAC ~keep:x86_bstep_keep execth th sname)),
   x86_bstep_steps,BSTEP_FINAL_TAC);;

let X86_BSTEP_PROMOTE_RETURN_NOSTACK_TAC mc core =
  X86_PROMOTE_RETURN_NOSTACK_TAC ~tactics:(x86_bstep_steps,BSTEP_FINAL_TAC)
    mc core;;

let X86_BSTEP_PROMOTE_RETURN_STACK_TAC mc core regs off =
  X86_PROMOTE_RETURN_STACK_TAC ~tactics:x86_bstep_wrapper_tactics
    mc core regs off;;

(* word((pc + m) + n) = word(pc + k) with k = m + n, everywhere in a term;   *)
(* for a theorem about code at an offset, as in the Windows wrappers.        *)

let X86_BSTEP_PC_CONV =
  DEPTH_CONV
   (GEN_REWRITE_CONV I
     [MESON[ADD_ASSOC] `word((pc + m) + n):int64 = word(pc + m + n)`] THENC
    RAND_CONV(RAND_CONV NUM_ADD_CONV));;

(* For the Windows wrapper, the call first turns the code fact of the        *)
(* Windows code into that of the standard code inside it.                    *)

let x86_bstep_windows_tactics =
  let is_loaded = can (term_match [] `bytes_loaded s pc mc`) in
  (x86_bstep_steps,
   (fun execth subimpth sname -> DISCH_THEN(fun th ->
      W(fun (_,w) -> FIRST_ASSUM(fun cth ->
        if is_loaded (concl cth) &&
           rand(rator(rator(concl cth))) = rand w
        then ASSUME_TAC(MATCH_MP subimpth cth) else NO_TAC)) THEN
      X86_BSTEP_CALL_TAC ~keep:x86_bstep_keep execth th sname)),
   x86_bstep_steps,BSTEP_FINAL_TAC);;

let X86_BSTEP_WINDOWS_WRAP_STACK_TAC winmc stdmc coreth reglist stackoff =
  WINDOWS_X86_WRAP_STACK_TAC ~tactics:x86_bstep_windows_tactics
    winmc stdmc coreth reglist stackoff;;
