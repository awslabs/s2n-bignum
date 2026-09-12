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

(* ------------------------------------------------------------------------- *)
(* Simulate through a core correctness theorem.                             *)
(* ------------------------------------------------------------------------- *)

let (RISCV_BIGSTEP_TAC:(thm*thm option array)->string->tactic) =
  GEN_BIGSTEP_TAC
    "RISCV" aligned_bytes_loaded_update DISCARD_OLDSTATE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Standard RV32 ILP32 psABI helpers.                                       *)
(* ------------------------------------------------------------------------- *)

(* These definitions model the integer calling convention of the standard
   ILP32 ABI from the RISC-V ABIs Specification. They do not model ILP32E or
   floating-point argument and return registers. *)

let SOME_FLAGS = new_definition
 `SOME_FLAGS:((riscvstate,bool)component)list = []`;;

let C_ARGUMENTS = define
 `(C_ARGUMENTS [a1;a2;a3;a4;a5;a6;a7;a8] s <=>
        read A0 s = a1 /\ read A1 s = a2 /\ read A2 s = a3 /\
        read A3 s = a4 /\ read A4 s = a5 /\ read A5 s = a6 /\
        read A6 s = a7 /\ read A7 s = a8) /\
  (C_ARGUMENTS [a1;a2;a3;a4;a5;a6;a7] s <=>
        read A0 s = a1 /\ read A1 s = a2 /\ read A2 s = a3 /\
        read A3 s = a4 /\ read A4 s = a5 /\ read A5 s = a6 /\
        read A6 s = a7) /\
  (C_ARGUMENTS [a1;a2;a3;a4;a5;a6] s <=>
        read A0 s = a1 /\ read A1 s = a2 /\ read A2 s = a3 /\
        read A3 s = a4 /\ read A4 s = a5 /\ read A5 s = a6) /\
  (C_ARGUMENTS [a1;a2;a3;a4;a5] s <=>
        read A0 s = a1 /\ read A1 s = a2 /\ read A2 s = a3 /\
        read A3 s = a4 /\ read A4 s = a5) /\
  (C_ARGUMENTS [a1;a2;a3;a4] s <=>
        read A0 s = a1 /\ read A1 s = a2 /\ read A2 s = a3 /\
        read A3 s = a4) /\
  (C_ARGUMENTS [a1;a2;a3] s <=>
        read A0 s = a1 /\ read A1 s = a2 /\ read A2 s = a3) /\
  (C_ARGUMENTS [a1;a2] s <=>
        read A0 s = a1 /\ read A1 s = a2) /\
  (C_ARGUMENTS [a1] s <=>
        read A0 s = a1) /\
  (C_ARGUMENTS [] s <=>
        T)`;;

let C_RETURN = define
 `C_RETURN = read A0`;;

let PRESERVED_GPRS = define
 `PRESERVED_GPRS =
   [SP; S0; S1; S2; S3; S4; S5; S6; S7; S8; S9; S10; S11]`;;

let MODIFIABLE_GPRS = define
 `MODIFIABLE_GPRS =
   [RA; A0; A1; A2; A3; A4; A5; A6; A7;
    T0; T1; T2; T3; T4; T5; T6]`;;

let MAYCHANGE_REGS_PERMITTED_BY_ABI = REWRITE_RULE
  [MODIFIABLE_GPRS]
  (new_definition `MAYCHANGE_REGS_PERMITTED_BY_ABI =
      MAYCHANGE [PC] ,, MAYCHANGE MODIFIABLE_GPRS ,, MAYCHANGE [events]`);;

(* ------------------------------------------------------------------------- *)
(* Promote core correctness theorems to psABI subroutine theorems.          *)
(* ------------------------------------------------------------------------- *)

let RISCV_CHECK_FORALLVARS_TAC:tactic =
  GEN_CHECK_FORALLVARS_TAC
    [`read RA s`; `read events s`; `read SP s`];;

let RISCV_SWAP_FORALL = SWAP_FORALL_THM
and RISCV_SWAP_FORALL3 = SUBROUTINE_SWAP_FORALL3
and RISCV_APPEND_LEMMA = SUBROUTINE_APPEND_FORALL
and RISCV_MONO2_LEMMA = SUBROUTINE_MONO_FORALL2
and RISCV_MONO3_LEMMA = SUBROUTINE_MONO_FORALL3
and RISCV_APPEND_E2_NIL = SUBROUTINE_APPEND_PREFIX_NIL;;

(* Promote a core theorem whose postcondition stops immediately before the
   final return instruction. Schematically, the full routine is

       addi a0,a0,1       # covered by coreth
       jalr zero,ra,0     # executed by this tactic

   The promoted theorem returns to the aligned value of RA and widens the
   frame to the registers that the ILP32 ABI permits a callee to change. *)

let RISCV_ADD_RETURN_NOSTACK_TAC =
  fun execth coreth ->
    let is_coreth_safety = is_exists (concl coreth) in

    (fun (asl,w) ->
      if is_coreth_safety <> is_exists w then
        failwith "coreth must be `exists ..` iff the conclusion is"
      else ALL_TAC (asl,w)) THEN

    (if is_coreth_safety then
      ASSUME_CALLEE_SAFETY_TAC coreth "" THEN
      META_EXISTS_TAC THEN
      RISCV_CHECK_FORALLVARS_TAC THEN
      FIRST_X_ASSUM
        (fun th -> MP_TAC (ONCE_REWRITE_RULE[RISCV_APPEND_LEMMA] th)) THEN
      REPEAT
       (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[RISCV_SWAP_FORALL])) THEN
        MATCH_MP_TAC RISCV_MONO2_LEMMA THEN GEN_TAC)
     else
      RISCV_CHECK_FORALLVARS_TAC THEN
      MP_TAC coreth THEN
      REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC)) THEN

    REWRITE_TAC[MAYCHANGE_REGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS] THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
                MAYCHANGE_REGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS] THEN
    DISCH_THEN(fun th ->
      REPEAT GEN_TAC THEN
      TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    (if is_coreth_safety then
      ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN META_EXISTS_TAC
     else ALL_TAC) THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      ((ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE
       (ALIGNED_WORD_TAC THEN NO_TAC) ORELSE
       (TRY DISJ2_TAC THEN NONOVERLAPPING_TAC));
      ALL_TAC]) THEN
    DISCH_THEN(fun th ->
      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN MP_TAC th) THEN
    RISCV_BIGSTEP_TAC execth "s1" THEN
    (if is_coreth_safety then
      TRY
       (TRY(GEN_REWRITE_TAC I [RISCV_APPEND_E2_NIL]) THEN
        TRY(CONV_TAC (LAND_CONV CONS_TO_APPEND_CONV)) THEN
        BINOP_TAC THENL [UNIFY_REFL_TAC; REFL_TAC] THEN NO_TAC)
     else ALL_TAC) THEN
    RISCV_STEPS_TAC execth [2] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_SIMP_TAC[RISCV_JALR_ALIGNED_MASK_WORD];;

(* Promote a core theorem surrounded by a stack prologue and epilogue.
   Schematically,

       addi sp,sp,-16; sw s0,0(sp)    # prologue
       ...                             # covered by coreth
       lw s0,0(sp); addi sp,sp,16     # epilogue
       jalr zero,ra,0

   `reglist` names the saved registers and `stackoff` is the frame size. The
   frame size must be a multiple of 16, so adjusting an aligned incoming SP
   preserves the standard ILP32 stack alignment. The tactic executes the
   prologue and epilogue, proves that SP and the listed callee-saved registers
   are restored, and then applies the ABI frame. *)

let RISCV_ADD_RETURN_STACK_TAC =
  let sp_tm = `SP` in
  fun ?(pre_post_nsteps:(int*int) option)
      ?(core_precondition_tac = ALL_TAC)
      execth coreth reglist stackoff ->
    if stackoff mod 16 <> 0 then
      failwith
        "RISCV_ADD_RETURN_STACK_TAC: stack frame size is not 16-byte aligned";
    let is_coreth_safety = is_exists (concl coreth) in
    let regs = dest_list reglist in

    (fun (asl,w) ->
      if is_coreth_safety <> is_exists w then
        failwith "coreth must be `exists ..` iff the conclusion is"
      else ALL_TAC (asl,w)) THEN

    let pre_n,post_n =
      match pre_post_nsteps with
      | Some (a,b) -> a,b
      | None ->
          let n = length regs + 1 in
          n,n in

    (if is_coreth_safety then
      ASSUME_CALLEE_SAFETY_TAC coreth "" THEN
      META_EXISTS_TAC THEN
      RISCV_CHECK_FORALLVARS_TAC THEN
      FIRST_X_ASSUM
        (fun th -> MP_TAC (ONCE_REWRITE_RULE[RISCV_APPEND_LEMMA] th))
     else
      RISCV_CHECK_FORALLVARS_TAC THEN MP_TAC coreth) THEN

    REWRITE_TAC[MAYCHANGE_REGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
                fst execth] THEN
    (if is_coreth_safety then
      REPEAT
       (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[RISCV_SWAP_FORALL])) THEN
        MATCH_MP_TAC RISCV_MONO3_LEMMA THEN GEN_TAC) THEN
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[RISCV_SWAP_FORALL]))
     else
      REPEAT(MATCH_MP_TAC RISCV_MONO2_LEMMA THEN GEN_TAC)) THEN
    (if vfree_in sp_tm (concl coreth) then
      DISCH_THEN(fun th -> WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th) THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC
     else
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      DISCH_THEN(fun th ->
        WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th)) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; PAIRWISE; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    DISCH_THEN(fun th ->
      REPEAT GEN_TAC THEN
      TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    (if is_coreth_safety then
      ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN META_EXISTS_TAC
     else ALL_TAC) THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      ((ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE
       (ALIGNED_WORD_TAC THEN NO_TAC) ORELSE
       (TRY DISJ2_TAC THEN NONOVERLAPPING_TAC));
      ALL_TAC]) THEN
    DISCH_THEN(fun th ->
      ((ENSURES_EXISTING_PRESERVED_TAC sp_tm THEN
        MAP_EVERY
         (fun c ->
           ENSURES_PRESERVED_TAC ("init_" ^ fst(dest_const c)) c)
         regs)
       ORELSE
       FAIL_TAC
        "callee-save registers are still in MAYCHANGE, or `read SP s` is absent") THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN
      RISCV_STEPS_TAC execth (1--pre_n) THEN
      MP_TAC th) THEN
    RISCV_BIGSTEP_TAC execth ("s" ^ string_of_int(pre_n + 1)) THEN
    (if is_coreth_safety then
      TRY
       (TRY(GEN_REWRITE_TAC I [RISCV_APPEND_E2_NIL]) THEN
        TRY(CONV_TAC (LAND_CONV CONS_TO_APPEND_CONV)) THEN
        BINOP_TAC THENL [UNIFY_REFL_TAC; REFL_TAC] THEN NO_TAC)
     else ALL_TAC) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    TRY(core_precondition_tac THEN NO_TAC) THEN
    RISCV_STEPS_TAC execth
      ((pre_n + 2)--(pre_n + post_n + 2)) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_SIMP_TAC[RISCV_JALR_ALIGNED_MASK_WORD];;
