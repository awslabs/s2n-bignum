(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Simplified RV32IM execution and proof automation.                         *)
(* ========================================================================= *)

let riscv_print_log = ref false;;

(* Keep the decoded instruction relation behind a named identity. Proof
   conversions can then unfold instruction execution separately from fetch
   and PC update. *)

let riscv_execute = define
 `riscv_execute = \i:(riscvstate->riscvstate->bool). i`;;

(* One machine transition decodes the word at the current PC, advances PC by
   four bytes, and then applies the decoded instruction relation. Branch
   semantics recover the address of the instruction through
   `riscv_instruction_pc`, since PC has already advanced at that point. *)

let riscv = define
 `riscv s s' <=>
    ?instr. riscv_decode s (read PC s) instr /\
            (PC := word_add (read PC s) (word 4) ,,
             riscv_execute instr) s s'`;;

(* ------------------------------------------------------------------------- *)
(* Support for the forward symbolic-execution proof style.                   *)
(* ------------------------------------------------------------------------- *)

(* Select the decode theorem at the byte offset given by `read PC`, combine it
   with the matching code-loading fact, and expose one `riscv` transition as
   the advanced-PC update followed by the decoded instruction relation. *)

(* The instruction-pointer theorem must express the current address relative
   to a symbolic code base: `word pc` at offset zero or `word (pc + n)` at byte
   offset `n`. This is the common contract of ARM_THM, RISCV_THM and X86_THM;
   specialize the resulting execution theorem afterward for fixed addresses. *)

let RISCV_THM =
  let pth = prove
   (`read PC s = word pc ==> riscv_decode s (word pc) instr ==>
     (riscv s s' <=> (PC := word (pc + 4) ,, instr) s s')`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[riscv] THEN
    ASM_REWRITE_TAC[GSYM WORD_ADD; riscv_execute] THEN
    ASM_MESON_TAC[riscv_decode_unique]) in
  fun (execth2:thm option array) loaded_mc_th pc_th ->
    let th = MATCH_MP pth pc_th in
    let pc_ofs =
      let pc_expr = snd (dest_comb (snd (dest_eq (concl pc_th)))) in
      if is_var pc_expr then 0
      else
        try
          let _,ofs = dest_binary "+" pc_expr in
          dest_small_numeral ofs
        with Failure _ ->
          failwith
            ("RISCV_THM: cannot decompose PC expression: " ^
             string_of_term (concl pc_th)) in
    let _ =
      if !riscv_print_log then
        let opt = option_get execth2.(pc_ofs) in
        let t = snd (strip_forall (concl opt)) in
        let t = snd (dest_imp t) in
        let term = snd (dest_comb t) in
        Printf.printf "Instruction at `pc + %d (%#x)`: `%s`\n"
          pc_ofs pc_ofs (string_of_term term) in
    MATCH_MP th (MATCH_MP (option_get execth2.(pc_ofs)) loaded_mc_th);;

let RISCV_ENSURES_SUBLEMMA_TAC =
  ENSURES_SUBLEMMA_TAC o
  MATCH_MP aligned_bytes_loaded_update o CONJUNCT1;;

let RISCV_ENSURES_SUBSUBLEMMA_TAC =
  ENSURES_SUBSUBLEMMA_TAC o
  map (MATCH_MP aligned_bytes_loaded_update o CONJUNCT1);;

let is_read_pc = is_read_named_component "PC";;

let is_read_events = is_read_named_component "events";;

(* Control-flow stepping creates alignment side conditions containing the
   JALR bit-zero mask and symbolic PC additions. These lemmas and theorem
   transformers normalize those expressions before `RISCV_CONV` unfolds the
   instruction relation. *)

let RISCV_JALR_ALIGNED_MASK = prove
 (`!x:int32.
    aligned 4 x
    ==> word_and x (word_not (word 1)) = x`,
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM WORD_VAL] THEN
  let th =
    CONV_RULE (ONCE_DEPTH_CONV NUM_REDUCE_CONV)
      (ISPECL [`x:int32`; `1`]
        (CONJUNCT1 WORD_AND_NOT_MASK_WORD)) in
  REWRITE_TAC[th] THEN
  AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[aligned]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `2 divides val(x:int32)` ASSUME_TAC THENL
   [MATCH_MP_TAC
      (ISPECL [`2`; `4`; `val(x:int32)`] DIVIDES_TRANS) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC DIVIDES_CONV;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_REWRITE_TAC[GSYM DIVIDES_DIV_MULT]);;

let RISCV_JALR_ALIGNED_MASK_WORD =
  CONV_RULE (ONCE_DEPTH_CONV WORD_REDUCE_CONV)
    RISCV_JALR_ALIGNED_MASK;;

let RISCV_JALR_ALIGNED_TARGET = prove
 (`!x:int32.
    aligned 4 x
    ==> aligned 4
        (word_and (word_add x (word 0)) (word_not (word 1)))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_ADD_0; RISCV_JALR_ALIGNED_MASK]);;

let RISCV_WORD_ADD_LCANCEL_EQ = WORD_RULE
 `!a x y:N word. word_add a x = word_add a y <=> x = y`;;

let RISCV_JALR_MASK_THMS ths =
  mapfilter
    (fun th -> MATCH_MP RISCV_JALR_ALIGNED_MASK_WORD th)
    ths;;

let RISCV_JALR_READ_MASK_THMS ths =
  let mask_ths = RISCV_JALR_MASK_THMS ths in
  let int32_ty = type_of `x:int32` in
  let mask_fn = `\x:int32. word_and x (word 4294967294)` in
  mapfilter
    (fun read_th ->
      let l,r = dest_eq (concl read_th) in
      if not (is_binary "read" l) || type_of r <> int32_ty then
        failwith "not an int32 component read";
      let lifted_th =
        CONV_RULE (DEPTH_CONV BETA_CONV) (AP_TERM mask_fn read_th) in
      let masked_rhs = rhs (concl lifted_th) in
      let mask_th =
        find (fun th -> lhs (concl th) = masked_rhs) mask_ths in
      TRANS lifted_th mask_th)
    ths;;

let RISCV_NORMALIZE_PC_TH ths pc_th =
  let eq_ths = filter (fun th -> is_eq (concl th)) ths in
  let mask_ths = RISCV_JALR_MASK_THMS ths in
  CONV_RULE
   (RAND_CONV
    (PURE_REWRITE_CONV
      (eq_ths @ mask_ths @ [RISCV_WORD_ADD_LCANCEL_EQ]) THENC
     DEPTH_CONV WORD_EQ_CONV THENC
     REWRITE_CONV[]))
   pc_th;;

(* Convert one symbolic machine step to the explicit state update for the
   instruction at the current PC. `decode_ths` is the array from
   `RISCV_MK_EXEC_RULE`; `ths` must include the current `read PC` equation and
   the matching `aligned_bytes_loaded` fact; and `tm` has the form
   `riscv s s'`. For example, with `read PC s = word pc` and code beginning
   with `ADDI A0 A0 1`, the result rewrites `riscv s s'` to the PC update
   followed by the `A0` update and any generated events. *)

let RISCV_CONV (decode_ths:thm option array) (ths:thm list) tm =
  let pc_th =
    try
      find
        (fun th ->
          let c = concl th in
          is_eq c && is_read_pc (fst (dest_eq c)))
        ths
    with Failure _ ->
      failwith "RISCV_CONV: cannot find `read PC .. = ..`" in
  let pc_th = RISCV_NORMALIZE_PC_TH ths pc_th in
  let aligned_bytes_loaded_mc_ths =
    let the_mc =
      option_bind decode_ths.(0)
        (fun th ->
          let t = concl th in
          let loaded = fst (dest_imp (snd (strip_forall t))) in
          let mc = last (snd (strip_comb loaded)) in
          if is_const mc then Some mc else None) in
    let loaded_tm = `aligned_bytes_loaded` in
    let res =
      filter
        (fun th ->
          let c,args = strip_comb (concl th) in
          c = loaded_tm &&
          (the_mc = None || last args = option_get the_mc))
        ths in
    if res = [] then
      failwith "RISCV_CONV: cannot find aligned code-loading assumption"
    else
      res in
  let code_aligned_ths =
    map (MATCH_MP aligned_bytes_loaded_aligned)
      aligned_bytes_loaded_mc_ths in
  let jalr_aligned_ths =
    mapfilter
      (fun th -> MATCH_MP RISCV_JALR_ALIGNED_TARGET th)
      ths in
  let jalr_read_mask_ths = RISCV_JALR_READ_MASK_THMS ths in
  let aligned_ths = jalr_aligned_ths @ code_aligned_ths @ ths in
  let eth =
    try
      tryfind
        (fun loaded_mc_th ->
          GEN_REWRITE_CONV I
            [RISCV_THM decode_ths loaded_mc_th pc_th] tm)
        aligned_bytes_loaded_mc_ths
    with Failure _ ->
      failwith "RISCV_CONV: cannot match code loading to the current PC" in
  (K eth THENC
   REWRITE_CONV
    [riscv_execute; riscv_ADD; riscv_ADDI; riscv_SUB; riscv_SLLI;
     riscv_SRAI; riscv_LUI; riscv_MUL; riscv_MULH; riscv_LW; riscv_SW;
     riscv_BNE; riscv_JALR; read_gpr; write_gpr; riscv_addr;
     riscv_instruction_pc; riscv_branch_target; riscv_mulh;
     riscv_event_load; riscv_event_store; riscv_event_jump; SEQ] THENC
   REWRITE_CONV[LET_DEF; LET_END_DEF] THENC
   TOP_DEPTH_CONV BETA_CONV THENC
   ALIGNED_WORD_EXTENDED_CONV aligned_ths THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV [assign] THENC
   REWRITE_CONV[] THENC
   TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
   REWRITE_CONV
    [RISCV_ZERO_REGISTER; READ_RVALUE; WRITE_RVALUE; WORD_ADD_0] THENC
   WORD_REDUCE_CONV THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV jalr_read_mask_ths THENC
   ONCE_REWRITE_CONV[WORD_SUB_ADD] THENC
   ONCE_DEPTH_CONV
    (REWR_CONV (GSYM ADD_ASSOC) THENC RAND_CONV NUM_REDUCE_CONV) THENC
   ONCE_DEPTH_CONV
    (GEN_REWRITE_CONV I [GSYM WORD_ADD] THENC
     GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV) [GSYM ADD_ASSOC] THENC
     RAND_CONV NUM_REDUCE_CONV) THENC
   TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV THENC
   GEN_REWRITE_CONV (SUB_COMPONENTS_CONV o TOP_DEPTH_CONV) ths THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_VAL] THENC
   ONCE_DEPTH_CONV WORD_PC_PLUS_CONV THENC
   ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
   ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) tm;;

let RISCV_BASIC_STEP_TAC =
  GEN_BASIC_STEP_TAC "RISCV" `riscv` `:riscvstate` RISCV_CONV ALL_TAC;;

let RISCV_STEP_TAC (mc_length_th,decode_ths) subths sname
      (store_inst_term_to:term ref option)
      (strip_component_tac:thm_tactic) =
  GEN_STEP_TAC RISCV_BASIC_STEP_TAC ALL_TAC aligned_bytes_loaded_update
    (fun th thl ->
      if !riscv_print_log then begin
        Printf.printf "State update: `%s`\n" (string_of_thm th);
        List.iter
          (fun th' ->
            Printf.printf "New component: `%s`\n" (string_of_thm th'))
          thl
      end)
    (mc_length_th,decode_ths) subths sname
    store_inst_term_to strip_component_tac;;

let RISCV_VERBOSE_STEP_TAC =
  GEN_VERBOSE_STEP_TAC RISCV_STEP_TAC;;

let RISCV_VERBOSE_SUBSTEP_TAC =
  GEN_VERBOSE_SUBSTEP_TAC RISCV_STEP_TAC;;

let DISCARD_STATE_TAC =
  GEN_DISCARD_STATE_TAC `:riscvstate`;;

let DISCARD_OLDSTATE_TAC =
  GEN_DISCARD_OLDSTATE_TAC `:riscvstate` riscv_print_log;;

let RISCV_SINGLE_STEP_TAC =
  GEN_SINGLE_STEP_TAC RISCV_VERBOSE_STEP_TAC DISCARD_OLDSTATE_TAC;;

let RISCV_VACCSTEP_TAC =
  GEN_VACCSTEP_TAC RISCV_VERBOSE_STEP_TAC;;

let RISCV_XACCSTEP_TAC =
  GEN_XACCSTEP_TAC RISCV_SINGLE_STEP_TAC;;

let RISCV_GEN_ACCSTEP_TAC =
  GEN_ACCSTEP_TAC RISCV_SINGLE_STEP_TAC;;

let RISCV_ACCSTEP_TAC th aflag s =
  RISCV_GEN_ACCSTEP_TAC ALL_TAC th aflag s;;

let RISCV_VSTEPS_TAC =
  GEN_VSTEPS_TAC RISCV_VERBOSE_STEP_TAC;;

let RISCV_STEPS_TAC =
  GEN_STEPS_TAC RISCV_SINGLE_STEP_TAC;;

let RISCV_VACCSTEPS_TAC =
  GEN_VACCSTEPS_TAC RISCV_VACCSTEP_TAC;;

let RISCV_XACCSTEPS_TAC =
  GEN_XACCSTEPS_TAC RISCV_XACCSTEP_TAC;;

let RISCV_GEN_ACCSTEPS_TAC =
  GEN_ACCSTEPS_TAC RISCV_GEN_ACCSTEP_TAC;;

let RISCV_ACCSTEPS_TAC th anums snums =
  RISCV_XACCSTEPS_TAC th [`SP`] anums snums;;

let RISCV_QUICKSTEP_TAC th pats =
  let pats' =
   [`nonoverlapping_modulo a b c`; `aligned_bytes_loaded a b c`;
    `MAYCHANGE a b c`; `(a ,, b) c d`; `read PC s = x`] @ pats in
  fun s ->
    time (RISCV_VERBOSE_STEP_TAC th s) THEN
    DISCARD_NONMATCHING_ASSUMPTIONS pats' THEN
    DISCARD_OLDSTATE_TAC s THEN
    CLARIFY_TAC;;

let RISCV_QUICKSTEPS_TAC th pats snums =
  MAP_EVERY (RISCV_QUICKSTEP_TAC th pats) (statenames "s" snums);;

let RISCV_QUICKSIM_TAC execth pats snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_QUICKSTEPS_TAC execth pats snums THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
  ASM_REWRITE_TAC[];;

let RISCV_SIM_TAC ?(preprocess_tac:tactic option)
    ?(canonicalize_pc_diff=true) execth snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  (match preprocess_tac with Some t -> t | None -> ALL_TAC) THEN
  RISCV_STEPS_TAC execth snums THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  (if canonicalize_pc_diff then
    REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[]
   else
    ALL_TAC);;

let RISCV_ACCSIM_TAC execth anums snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_ACCSTEPS_TAC execth anums snums THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
  ASM_REWRITE_TAC[];;
