(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reasoning program equivalence for X86 programs.                           *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/relational2.ml";;

(* ------------------------------------------------------------------------- *)
(* Generic lemmas and tactics that are useful                                *)
(* ------------------------------------------------------------------------- *)

let WRITE_ELEMENT_BYTES8 = prove(
  `!loc (z:(8)word) s. write (element loc) z s = write (bytes8 loc) z s`,
  REWRITE_TAC[bytes8;WRITE_COMPONENT_COMPOSE;asword;through;write;ARITH_RULE`1=SUC 0`;bytes;WORD_ADD_0;limb] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  IMP_REWRITE_TAC[DIV_1;MOD_LT] THEN
  REWRITE_TAC[WORD_VAL;ARITH_RULE`256=2 EXP 8`;VAL_BOUND;GSYM DIMINDEX_8]);;

let READ_OVER_WRITE_BYTELIST =
  prove(`!s (loc:int64) (l:((8)word)list).
      LENGTH l < 2 EXP 64
      ==> read (bytelist (loc,LENGTH l))
        (write (bytelist (loc,LENGTH l)) l s) = l`,
    REPEAT GEN_TAC THEN
    MAP_EVERY SPEC_TAC [
      `loc:int64`,`loc:int64`;`s:(64)word->(8)word`,`s:(64)word->(8)word`;
      `l:((8)word)list`,`l:((8)word)list`] THEN
    MATCH_MP_TAC list_INDUCT THEN
    CONJ_TAC THENL [
      REWRITE_TAC[LENGTH;READ_COMPONENT_COMPOSE;bytelist_clauses];

      REPEAT GEN_TAC THEN STRIP_TAC THEN
      REWRITE_TAC[LENGTH;bytelist_clauses] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      REWRITE_TAC[CONS_11] THEN
      CONJ_TAC THENL [
        REWRITE_TAC[element;write];

        REWRITE_TAC[WRITE_ELEMENT_BYTES8] THEN
        IMP_REWRITE_TAC[READ_WRITE_ORTHOGONAL_COMPONENTS] THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ORTHOGONAL_COMPONENTS_TAC
      ]
    ]);;

let READ_OVER_WRITE_MEMORY_BYTELIST =
  prove(`!s (loc:int64) (l:((8)word)list).
      LENGTH l < 2 EXP 64
      ==> read (memory :> bytelist (loc,LENGTH l))
        (write (memory :> bytelist (loc,LENGTH l)) l s) = l`,
  let read_write_mem_th =
    ISPECL [`memory:(x86state,(64)word->(8)word)component`] READ_WRITE_VALID_COMPONENT in
  REWRITE_TAC[component_compose] THEN
  REWRITE_TAC[read;write;o_THM] THEN
  IMP_REWRITE_TAC([read_write_mem_th] @ (!valid_component_thms)) THEN
  REWRITE_TAC[READ_OVER_WRITE_BYTELIST]);;


(* ------------------------------------------------------------------------- *)
(* eventually_n_at_pc states that if pre/postconditions at pc/pc2 are        *)
(* satisfied at nth step, you can 'promote' eventually to eventually_n.      *)
(* ------------------------------------------------------------------------- *)

let eventually_n_at_pc = new_definition
  `!pc_mc pc pc2 (nth:num) (mc:((8)word)list) (s0_pred:x86state->bool).
    eventually_n_at_pc pc_mc mc pc pc2 nth s0_pred
      <=>
    (!s (P:x86state->x86state->bool).
      bytes_loaded s (word pc_mc) mc /\ read RIP s = word pc /\
      s0_pred s ==>
      eventually x86 (\s'. read RIP s' = word pc2 /\ P s s') s ==>
      eventually_n x86 nth (\s'. read RIP s' = word pc2 /\ P s s') s)`;;

let ENSURES_AND_EVENTUALLY_N_AT_PC_PROVES_ENSURES_N = prove(
  `forall Pre pc_mc mc pc n.
    eventually_n_at_pc pc_mc mc pc pc2 n Pre
    ==> forall Post R.
      ensures x86
        (\s. bytes_loaded s (word pc_mc) mc /\ read RIP s = word pc /\
             Pre s)
        (\s. read RIP s = word pc2 /\ Post s)
        R
      ==> ensures_n x86
        (\s. bytes_loaded s (word pc_mc) mc /\ read RIP s = word pc /\
             Pre s)
        (\s. read RIP s = word pc2 /\ Post s)
        R (\s. n)`,

  REPEAT GEN_TAC THEN
  REWRITE_TAC[eventually_n_at_pc;ensures;ensures_n] THEN
  INTRO_TAC "H2" THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "H1" THEN
  GEN_TAC THEN INTRO_TAC "HA HB HC" THEN
  REMOVE_THEN "H1" (fun th -> MP_TAC (SPECL [`s:x86state`] th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (LABEL_TAC "H1") THEN
  REMOVE_THEN "H2" (fun th -> MP_TAC (SPECL
    [`s:x86state`;`(\(s:x86state) (s2:x86state). Post s2 /\ R s s2)`] th)) THEN
  ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* A "barrier" instruction that makes x86 program stop.                      *)
(* ------------------------------------------------------------------------- *)

(* A "barrier" instruction that cannot be decoded in x86.
   It is UD2 (Undefined instruction). https://www.felixcloutier.com/x86/ud
   ADD1's hoare triple must hold on a program that ends with this
   barrier_inst, and this is due to an interesting property of
   the underlying theory of hoare logic for machine codes.
   https://www.cl.cam.ac.uk/~mom22/mc-hoare-logic.pdf 
*)
let barrier_inst_bytes = new_definition(`barrier_inst_bytes = [word 0x0F; word 0x0B]:((8)word)list`);;

let DECODE_TO_NONE_CONV:conv =
  REWRITE_CONV[decode;barrier_inst_bytes;APPEND] THENC
  ONCE_REWRITE_CONV[read_prefixes] THENC
  ONCE_DEPTH_CONV BITMATCH_SEQ_CONV THENC
  REWRITE_CONV[obind;read_REX_prefix] THENC
  ONCE_DEPTH_CONV BITMATCH_SEQ_CONV THENC
  ONCE_DEPTH_CONV let_CONV THENC
  REWRITE_CONV[decode_aux;read_byte_val;obind] THENC
  ONCE_DEPTH_CONV BITMATCH_SEQ_CONV THENC
  REWRITE_CONV[read_byte_val;obind] THENC
  ONCE_DEPTH_CONV BITMATCH_SEQ_CONV;;

let BARRIER_INST_DECODE_NONE = prove(`!l. decode (APPEND barrier_inst_bytes l) = NONE`,
  GEN_TAC THEN
  CONV_TAC (LAND_CONV DECODE_TO_NONE_CONV) THEN
  REFL_TAC);;

let BARRIER_INST_BYTES_LENGTH = prove(`LENGTH barrier_inst_bytes = 2`,
    REWRITE_TAC[barrier_inst_bytes;LENGTH] THEN ARITH_TAC);;

let BYTES_LOADED_BARRIER_X86_STUCK = prove(
  `!s s' pc. bytes_loaded s (word pc) barrier_inst_bytes /\
          read RIP s = word pc /\ x86 s s' ==> F`,
    REWRITE_TAC[x86;x86_decode;barrier_inst_bytes] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_THEN `read RIP s = word pc` SUBST_ALL_TAC THEN
    (* There are three cases for l: [], [15], APPEND([15;11], l') *)
    DISJ_CASES_TAC (ISPEC `l:((8)word)list` list_CASES) THENL
    (** empty list **)
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN
     UNDISCH_TAC `decode [] = SOME (instr,[])` THEN 
     CONV_TAC (LAND_CONV DECODE_TO_NONE_CONV) THEN
     REWRITE_TAC[OPTION_DISTINCT]; ALL_TAC] THEN
    (** list with >=1 elem **)
    REPEAT_N 2 (FIRST_X_ASSUM CHOOSE_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    DISJ_CASES_TAC (ISPEC `t:((8)word)list` list_CASES) THENL
    (** list with 1 elem **)
    [ FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `[word 15;word 11]:((8)word)list = APPEND [word 15] [word 11]` SUBST_ALL_TAC THENL
      [REWRITE_TAC[APPEND] THEN FAIL_TAC "unfinished"; ALL_TAC] THEN
      (* show that h is 15 *)
      RULE_ASSUM_TAC (REWRITE_RULE [bytes_loaded_append]) THEN
      SPLIT_FIRST_CONJ_ASSUM_TAC THEN
      SUBGOAL_THEN `[h]:((8)word)list = [word 15]` SUBST_ALL_TAC THENL
      [ SUBGOAL_THEN `LENGTH ([word 15]:((8)word)list) = LENGTH ([h]:((8)word)list)` ASSUME_TAC THENL
        [REWRITE_TAC[LENGTH] THEN ARITH_TAC;ALL_TAC] THEN
        ASM_MESON_TAC[bytes_loaded_unique];
        ALL_TAC] THEN
      (* now unfold decode [15] *)
      UNDISCH_TAC `decode ([word 15]:((8)word)list) = SOME (instr,[])` THEN
      CONV_TAC (LAND_CONV DECODE_TO_NONE_CONV) THEN
      REWRITE_TAC[OPTION_DISTINCT] THEN FAIL_TAC "unfinished";
      
      ALL_TAC
    ] THEN
    (** list with >=2 elems **)
    REPEAT_N 2 (FIRST_X_ASSUM CHOOSE_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(CONS h (CONS h' t')):((8)word)list = APPEND [h;h'] t'` SUBST_ALL_TAC THENL
    [ REWRITE_TAC[APPEND] THEN FAIL_TAC "unfinished"; ALL_TAC ] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [bytes_loaded_append]) THEN
    SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    SUBGOAL_THEN `[h;h']:((8)word)list = [word 15; word 11]` SUBST_ALL_TAC THENL 
    [ SUBGOAL_THEN `LENGTH ([word 15;word 11]:((8)word)list) = LENGTH ([h;h']:((8)word)list)` ASSUME_TAC THENL
      [REWRITE_TAC[LENGTH] THEN ARITH_TAC;ALL_TAC] THEN
      ASM_MESON_TAC[bytes_loaded_unique];
      ALL_TAC
    ] THEN
    UNDISCH_TAC `decode (APPEND ([word 15;word 11]:((8)word)list) t') = SOME (instr,[])` THEN
    CONV_TAC (LAND_CONV DECODE_TO_NONE_CONV) THEN
    REWRITE_TAC[OPTION_DISTINCT]
  );;


(* ------------------------------------------------------------------------- *)
(* Tactics for simulating a program whose postcondition is eventually_n.     *)
(* ------------------------------------------------------------------------- *)

(* A variant of X86_BASIC_STEP_TAC, but
   - targets eventually_n
   - preserves 'arm s sname' at assumption *)
let X86_N_BASIC_STEP_TAC =
  let x86_tm = `x86` and x86_ty = `:x86state` and one = `1:num` in
  fun decode_th sname store_inst_term_to (asl,w) ->
    (* w = `eventually_n _ {stepn} _ {sv}` *)
    let sv = rand w and sv' = mk_var(sname,x86_ty) in
    let atm = mk_comb(mk_comb(x86_tm,sv),sv') in
    let eth = X86_CONV decode_th (map snd asl) atm in
    (* store the decoded instruction at store_inst_term_to *)
    (match store_inst_term_to with | Some r -> r := rhs (concl eth) | None -> ());
    let stepn = dest_numeral(rand(rator(rator w))) in
    let stepn_decr = stepn -/ num 1 in
    (* stepn = 1+{stepn-1}*)
    let stepn_thm = GSYM (NUM_ADD_CONV (mk_binary "+" (one,mk_numeral(stepn_decr)))) in
    (GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV) [stepn_thm] THEN
      GEN_REWRITE_TAC I [EVENTUALLY_N_STEP] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC BINDER_CONV [eth] THEN
      (CONV_TAC EXISTS_NONTRIVIAL_CONV ORELSE
       (PRINT_GOAL_TAC THEN
        FAIL_TAC ("Equality between two states is ill-formed." ^
                  " Did you forget extra condition like pointer alignment?")));
      X_GEN_TAC sv' THEN GEN_REWRITE_TAC LAND_CONV [eth] THEN
      REPEAT X86_UNDEFINED_CHOOSE_TAC]) (asl,w);;

let X86_N_STEP_TAC (mc_length_th,decode_ths) subths sname =
  (*** This does the basic decoding setup ***)

  X86_N_BASIC_STEP_TAC decode_ths sname None THEN

  (*** This part shows the code isn't self-modifying ***)

  NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update mc_length_th) THEN

  (*** Attempt also to show subroutines aren't modified, if applicable ***)

  MAP_EVERY (TRY o NONSELFMODIFYING_STATE_UPDATE_TAC o
    MATCH_MP bytes_loaded_update o CONJUNCT1) subths THEN

  (*** This part produces any updated versions of existing asms ***)

  ASSUMPTION_STATE_UPDATE_TAC THEN

  (*** Produce updated "MAYCHANGE" assumption ***)

  MAYCHANGE_STATE_UPDATE_TAC THEN

  (*** This adds state component theorems for the updates ***)
  (*** Could also assume th itself but I throw it away   ***)

  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ thl) THEN
    ASSEMBLER_SIMPLIFY_TAC THEN
    STRIP_TAC);;


(* A variant of X86_STEPS_TAC but uses DISCARD_OLDSTATE_AGGRESSIVELY_TAC
   instead. *)
let X86_N_STEPS_TAC th snums stname_suffix stnames_no_discard =
  let stnames = List.map (fun s -> s ^ stname_suffix) (statenames "s" snums) in
  MAP_EVERY (fun stname ->
    time (X86_N_STEP_TAC th [] stname) THEN
          DISCARD_OLDSTATE_AGGRESSIVELY_TAC (stname::stnames_no_discard)
            false)
          stnames;;

(* ------------------------------------------------------------------------- *)
(* Definitions for stating program equivalence.                              *)
(* ------------------------------------------------------------------------- *)

(* A recursive function for defining a conjunction of equality clauses *)
let mk_equiv_regs = define
  `((mk_equiv_regs:((x86state,(N)word)component)list->x86state#x86state->bool)
      [] s = true) /\
   (mk_equiv_regs (CONS reg regs) (s1,s2) =
     (mk_equiv_regs regs (s1,s2) /\
      exists (a:(N)word). read reg s1 = a /\ read reg s2 = a))`;;

let mk_equiv_regs2 = define
  `((mk_equiv_regs2
    :((x86state,(N)word)component)list->
     ((x86state,(N)word)component)list->x86state#x86state->bool)
      [] [] s = true) /\
   (mk_equiv_regs2 (CONS reg regs) (CONS reg2 regs2) (s1,s2) =
     (mk_equiv_regs2 regs regs2 (s1,s2) /\
      exists (a:(N)word). read reg s1 = a /\ read reg2 s2 = a))`;;

let mk_equiv_bool_regs = define
  `((mk_equiv_bool_regs:((x86state,bool)component)list->x86state#x86state->bool)
      [] s = true) /\
   (mk_equiv_bool_regs (CONS reg regs) (s1,s2) =
     (mk_equiv_bool_regs regs (s1,s2) /\
      exists (a:bool). read reg s1 = a /\ read reg s2 = a))`;;

(* ------------------------------------------------------------------------- *)
(* Tactics for proving equivalence of two partially different programs.      *)
(* ------------------------------------------------------------------------- *)

let EQUIV_INITIATE_TAC input_equiv_states_th =
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  let input_pred = SPEC_ALL
      (SPECL [`s0:x86state`;`s0':x86state`] input_equiv_states_th) in
  UNDISCH_TAC (fst (dest_binary "=" (concl input_pred))) THEN
  GEN_REWRITE_TAC LAND_CONV [input_equiv_states_th] THEN
  REWRITE_TAC [C_ARGUMENTS;SOME_FLAGS;mk_equiv_regs;mk_equiv_regs2;mk_equiv_bool_regs] THEN
  STRIP_TAC;;

let X86_N_STUTTER_LEFT_TAC exec_th (snames:int list): tactic =
  W (fun (asl,w) ->
    (* get the state name of the 'right' program *)
    let t' = fst (dest_comb w) in
    let inner_eventually = snd (dest_abs (snd (dest_comb (t')))) in
    let sname = fst (dest_var (snd (dest_comb inner_eventually))) in
    STASH_ASMS_OF_READ_STATES [sname] THEN
    X86_N_STEPS_TAC exec_th snames "" [] THEN
    RECOVER_ASMS_OF_READ_STATES THEN
    CLARIFY_TAC);;

let X86_N_STUTTER_RIGHT_TAC exec_th (snames:int list) (st_suffix:string)
    : tactic =
  W (fun (asl,w) ->
    (* get the state name of the 'left' program *)
    let sname = fst (dest_var (snd (dest_comb w))) in
    MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
    STASH_ASMS_OF_READ_STATES [sname] THEN
    X86_N_STEPS_TAC exec_th snames st_suffix [] THEN
    RECOVER_ASMS_OF_READ_STATES THEN
    MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
    CLARIFY_TAC);;
