(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* bstep: symbolic execution whose cost per instruction is bounded by what   *)
(* the instruction reads and writes.                                         *)
(*                                                                           *)
(* WHAT IT DOES                                                              *)
(*                                                                           *)
(* After ENSURES_INIT_TAC "s0", a correctness goal is `eventually step P     *)
(* s0`, with the code, the PC and facts `read c s0 = v` among its            *)
(* assumptions. ARM_BSTEP_TAC execth (1--n) (arm/proofs/bstep.ml) or         *)
(* X86_BSTEP_TAC (x86/proofs/bstep.ml) simulates n instructions as one block *)
(* and leaves `eventually step P sn`, with the facts at sn, the code, the PC *)
(* and the frame fact as new assumptions (listed at BSTEP_RUN_TAC). Branches *)
(* whose condition the assumptions decide are followed; a branch on data     *)
(* stops the block with an error, and the proof script splits the cases.     *)
(* BSTEP_FINAL_TAC ends a simulation. The options, for what only the proof   *)
(* knows, are ~keep (the components whose facts the new goal needs, default  *)
(* all), ~folds (definitions to fold into new values) and ~rewrites (more    *)
(* local rewrites, such as facts the proof has derived). ~forget and ~carry  *)
(* are for the safety layer (section 9).                                     *)
(*                                                                           *)
(* COST MODEL                                                                *)
(*                                                                           *)
(* Values are terms that share their subterms: the result of an instruction  *)
(* contains its inputs as the same objects in memory. Counted as trees,      *)
(* values grow exponentially with the depth of the computation (in the       *)
(* ML-KEM NTT the state after 900 steps has 127 million nodes as a tree but  *)
(* 169 thousand distinct ones), so no step may walk a value as a tree. In    *)
(* HOL Light such walks are: substitution (INST, SPEC, BETA) walks the term  *)
(* it substitutes into, and under a binder also each term it puts in; GEN    *)
(* and ABS walk all hypotheses; rewriting and DEPTH_CONV visit every         *)
(* subterm. Cheap are INST of a small binder-free theorem with large terms   *)
(* put in, MP and TRANS (their alpha-equivalence test stops at physically    *)
(* equal subterms), AP_TERM and MK_COMB. A step is built from these only, so *)
(* it costs about the size of the instruction's semantics, the same at step  *)
(* 100 and at step 900.                                                      *)
(*                                                                           *)
(* REPRESENTATION                                                            *)
(*                                                                           *)
(*  - States are terms, not variables: s_i = write d1 y1 (... s_{i-1}), so   *)
(*    nothing is ever substituted for a state or generalized over one inside *)
(*    a block. The steps are chained in |- steps_to step s0 s_i, which does  *)
(*    not mention P: a postcondition with metavariables (safety proofs)      *)
(*    costs nothing per step.                                                *)
(*  - Each instruction address has one step theorem, made by running the     *)
(*    instruction semantics (ARM_CONV, X86_CONV) once on a state variable    *)
(*    with every value read named by a variable; a step is one INST of it    *)
(*    and one MP per antecedent (section 4).                                 *)
(*    A fact about the base pc of the code alone that the goal has, such as  *)
(*    aligned 4096 (word pc) on AArch64, may be an antecedent too, so that   *)
(*    the template is simplified with it once (the pages of ADRP).           *)
(*  - Facts |- read c s_j = v are kept in a table keyed by c, with memory    *)
(*    addresses in one normal form, and are moved to the current state only  *)
(*    when an instruction reads c, by cached read-over-write theorems        *)
(*    (section 5).                                                           *)
(*  - If the postcondition has a frame C, every write is checked against C   *)
(*    itself, with one cached theorem per component.                         *)
(*  - Values that an x86 instruction leaves undefined (most flags after XOR) *)
(*    are fresh variables bstep_u<k>. The chain is cut into segments at such *)
(*    a step, and the justification generalizes over them: the only walk of  *)
(*    the state term at a step.                                              *)
(*                                                                           *)
(* SIMPLIFICATION                                                            *)
(*                                                                           *)
(* New values are simplified along the instruction's template only           *)
(* (bstep_norm): the parts that come from the values read were simplified    *)
(* when they were made, and the template when the step theorem was made. At  *)
(* each template node a fixed set of local conversions applies               *)
(* (bstep_node_conv), with the proof's ~rewrites and ~folds. The assumptions *)
(* of the goal are not used as rewrites; they prove side conditions and      *)
(* decide conditions (of branches and of conditionals in values). So the     *)
(* simplification costs the size of the template, whatever the size of the   *)
(* values, and it does not simplify across the boundary between old and new  *)
(* parts beyond what the local conversions look at.                          *)
(*                                                                           *)
(* CALLS AND SAFETY PROOFS                                                   *)
(*                                                                           *)
(* GEN_BSTEP_CALL_TAC (ARM_BSTEP_CALL_TAC, X86_BSTEP_CALL_TAC) goes through  *)
(* a theorem |- ensures step Pre Post Frame: it proves Pre from the          *)
(* assumptions and moves the facts that the frame does not touch to the      *)
(* state after it. The subroutine wrappers (ARM_BSTEP_ADD_RETURN_STACK_TAC,  *)
(* X86_BSTEP_PROMOTE_RETURN_STACK_TAC and others) simulate the prologue and  *)
(* the epilogue as blocks and go through the core theorem with it.           *)
(* Frames given by name, such as MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI   *)
(* (bstep_frame_defs), are unfolded for the checks and composition, and the  *)
(* frame facts of the new goals are in the form of the postcondition.        *)
(* ARM_BSTEP_SAFETY_TAC is PROVE_SAFETY_SPEC_TAC with one block from the     *)
(* start to the return address (BSTEP_SAFETY_RUN_TAC).                       *)
(*                                                                           *)
(* TRUST                                                                     *)
(*                                                                           *)
(* Nothing beyond the HOL Light kernel and the existing instruction          *)
(* semantics. The lemmas are proved with prove; the only new constant,       *)
(* steps_to, comes from new_definition. There is no mk_thm, new_axiom or     *)
(* kernel change.                                                            *)
(*                                                                           *)
(* LIMITS AND FAILURES                                                       *)
(*                                                                           *)
(* A step that bstep cannot do fails with the step number, the PC offset,    *)
(* the instruction and the reason; nothing falls back to other tactics.      *)
(* Reasons include: the PC is not at a constant offset (a branch on data, or *)
(* a return), a read that partly overlaps a write, a write that the frame    *)
(* does not allow, a side condition that the assumptions do not prove, and a *)
(* write to a byte region whose length is not a numeral (x86 REP MOVSB); the *)
(* proof simulates such an instruction with another tactic, between two      *)
(* blocks.                                                                   *)
(*                                                                           *)
(* EXAMPLE                                                                   *)
(*                                                                           *)
(* The program `add x2, x0, x1; mul x3, x2, x2`:                             *)
(*                                                                           *)
(*   let tiny_mc = define_word_list "tiny_mc"                                *)
(*     `[word 0x02; word 0x00; word 0x01; word 0x8b;                         *)
(*       word 0x43; word 0x7c; word 0x02; word 0x9b]:byte list`;;            *)
(*   let TINY_EXEC = ARM_MK_EXEC_RULE tiny_mc;;                              *)
(*                                                                           *)
(*   prove                                                                   *)
(*    (`!pc a b.                                                             *)
(*        ensures arm                                                        *)
(*          (\s. aligned_bytes_loaded s (word pc) tiny_mc /\                 *)
(*               read PC s = word pc /\ read X0 s = a /\ read X1 s = b)      *)
(*          (\s. read PC s = word (pc + 8) /\                                *)
(*               read X3 s = word_mul (word_add a b) (word_add a b))         *)
(*          (MAYCHANGE [PC; X2; X3])`,                                       *)
(*     REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN                      *)
(*     ARM_BSTEP_TAC TINY_EXEC (1--2) THEN                                   *)
(*     BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN                           *)
(*     REWRITE_TAC[WORD_MUL; WORD_VAL; ADD_CLAUSES])                         *)
(*                                                                           *)
(* The two step theorems, one per address, are                               *)
(*                                                                           *)
(*   |- read PC s = word pc                                                  *)
(*      ==> aligned_bytes_loaded s (word pc) tiny_mc                         *)
(*      ==> read X1 s = bstep_r1 ==> read X0 s = bstep_r2                    *)
(*      ==> steps_to arm s                                                   *)
(*          (write X2 (word_add bstep_r2 bstep_r1)                           *)
(*          (write PC (word (pc + 4)) s))                                    *)
(*   |- read PC s = word (pc + 4)                                            *)
(*      ==> aligned_bytes_loaded s (word pc) tiny_mc                         *)
(*      ==> read X2 s = bstep_r3                                             *)
(*      ==> steps_to arm s                                                   *)
(*          (write X3 (word (0 + val bstep_r3 * val bstep_r3))               *)
(*          (write PC (word (pc + 8)) s))                                    *)
(*                                                                           *)
(* Step 1 instantiates the first with s := s0, bstep_r1 := b and bstep_r2 := *)
(* a; step 2 reads X2 from the fact made by step 1. After ARM_BSTEP_TAC the  *)
(* goal is                                                                   *)
(*                                                                           *)
(*   0 [`aligned_bytes_loaded s2 (word pc) tiny_mc`]                         *)
(*   1 [`read PC s2 = word (pc + 8)`]                                        *)
(*   2 [`MAYCHANGE [PC; X2; X3] s0 s2`]                                      *)
(*   3 [`read X0 s2 = a`]                                                    *)
(*   4 [`read X1 s2 = b`]                                                    *)
(*   5 [`read X2 s2 = word_add a b`]                                         *)
(*   6 [`read X3 s2 = word (0 + val (word_add a b) * val (word_add a b))`]   *)
(*   `eventually arm (\s'. ...) s2`                                          *)
(*                                                                           *)
(* DIFFERENCES FROM ARM_STEPS_TAC / X86_STEPS_TAC                            *)
(*                                                                           *)
(*  - One call simulates a block, not a step, and there are no intermediate  *)
(*    state variables: a proof that needs a fact about an intermediate state *)
(*    ends the block there.                                                  *)
(*  - The instruction semantics runs once per address, not once per step.    *)
(*  - Facts are moved when they are read, not at every step, and they are    *)
(*    not in the goal during a block.                                        *)
(*  - New values are simplified along the template with fixed local          *)
(*    conversions; the assumptions are not used as rewrites, facts are not   *)
(*    rewritten with each other, and the goal is not rewritten. No           *)
(*    abbreviations are needed.                                              *)
(*  - The frame is checked against the postcondition's frame per write,      *)
(*    instead of building and canonicalizing a MAYCHANGE list per step.      *)
(*  - The new goal's assumptions come in the order given at BSTEP_RUN_TAC,   *)
(*    and the facts about s0 that are not moved stay.                        *)
(*  - Undefined values are fresh variables generalized per segment, instead  *)
(*    of a CHOOSE per step.                                                  *)
(*  - The subroutine wrappers go through the core theorem with               *)
(*    GEN_BSTEP_CALL_TAC instead of a big step.                              *)
(*  - A step that it cannot do is an error.                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 1. The chain of steps.                                                    *)
(*                                                                           *)
(* `steps_to step s t`: whatever eventually holds when running from t also   *)
(* eventually holds when running from s. A deterministic step from s to t    *)
(* gives steps_to step s t, and the steps of a block are chained by          *)
(* transitivity. The relation does not mention the postcondition, and it     *)
(* hides the quantifier over it, so state terms put into these lemmas are    *)
(* never under a binder.                                                     *)
(* ------------------------------------------------------------------------- *)

let steps_to = new_definition
 `steps_to (step:S->S->bool) s t <=>
    !P. eventually step P t ==> eventually step P s`;;

let STEPS_TO_STEP = prove
 (`!(step:S->S->bool) s t. (!s'. step s s' <=> t = s') ==> steps_to step s t`,
  REWRITE_TAC[steps_to] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[eventually_CASES] THEN DISJ2_TAC THEN ASM_MESON_TAC[]);;

let STEPS_TO_REFL = prove
 (`steps_to (step:S->S->bool) s s`,
  REWRITE_TAC[steps_to]);;

let STEPS_TO_TRANS = prove
 (`steps_to (step:S->S->bool) s t ==> steps_to step t u
   ==> steps_to step s u`,
  REWRITE_TAC[steps_to] THEN MESON_TAC[]);;

let STEPS_TO_EVENTUALLY = prove
 (`steps_to (step:S->S->bool) s t
   ==> eventually step P t ==> eventually step P s`,
  REWRITE_TAC[steps_to] THEN MESON_TAC[]);;

(* A step that leaves some values undefined, such as a flag after an x86     *)
(* XOR, has a successor for every choice u of them: step s s' <=>            *)
(* ?u. W u = s'. It cannot extend a chain; instead it gives                  *)
(* (!u. eventually step P (W u)) ==> eventually step P s, and the block      *)
(* goes on from W u with u a fresh variable (see bstep_one_step).            *)

let STEPS_SOME_STEP = prove
 (`!(step:S->S->bool) s P Q.
        (!s'. step s s' <=> Q s') ==> (?s'. Q s') ==>
        (!s'. Q s' ==> eventually step P s') ==> eventually step P s`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[eventually_CASES] THEN
  DISJ2_TAC THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 2. Small utilities.                                                       *)
(* ------------------------------------------------------------------------- *)

(* The failure of a step, with what is needed to find it.                    *)

exception Bstep_failure of string;;

let bstep_fail msg = raise (Bstep_failure msg);;

(* Short descriptions of terms for messages: values and state terms can be   *)
(* very large trees, so they are never printed.                              *)

let bstep_describe tm =
  match tm with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),_) ->
      "read " ^ string_of_term c ^ " _ = _"
  | _ -> (try fst(dest_const(fst(strip_comb tm))) ^ " ..."
          with Failure _ -> "?");;

(* With bstep_verbose set, each block prints one line: its number of steps,  *)
(* its time and the number of facts it keeps.                                *)

let bstep_verbose = ref false;;

(* ------------------------------------------------------------------------- *)
(* 3. Simplifying new values along the instruction's template.               *)
(*                                                                           *)
(* bstep_norm conv pat tm, where tm is pat with values put in for its        *)
(* variables, proves |- tm = tm' by walking pat and tm together, bottom up.  *)
(* It never enters a subterm of tm that stands for a variable of pat (the    *)
(* values put in are already simplified) or a subterm that is physically     *)
(* the same as in pat (it has no variables and was simplified when the       *)
(* template was made). At each node of pat it applies conv repeatedly at     *)
(* that node only (bstep_top; more than 20 times is an error); conv may look *)
(* into its arguments as deep as its patterns go, and must return results    *)
(* that are simplified below the top. Raises Bstep_unchanged if nothing      *)
(* changes.                                                                  *)
(* ------------------------------------------------------------------------- *)

exception Bstep_unchanged;;

let bstep_top (conv:conv) tm =
  let rec go n tm acc =
    if n = 0 then failwith "bstep: the simplification of a value does not stop"
    else
    match (try Some(conv tm) with Failure _ -> None) with
      None -> acc
    | Some th ->
        let tm' = rand(concl th) in
        if tm' == tm || compare tm' tm = 0 then acc else
        let acc' = match acc with
            None -> Some th | Some a -> Some(TRANS a th) in
        go (n - 1) tm' acc' in
  go 20 tm None;;

let rec bstep_norm (conv:conv) pat tm =
  if pat == tm then raise Bstep_unchanged else
  match pat,tm with
    Comb(pf,px),Comb(tf,tx) ->
      let thf = try Some(bstep_norm conv pf tf) with Bstep_unchanged -> None
      and thx = try Some(bstep_norm conv px tx) with Bstep_unchanged -> None in
      let th0 = match thf,thx with
          None,None -> None
        | Some a,None -> Some(AP_THM a tx)
        | None,Some b -> Some(AP_TERM tf b)
        | Some a,Some b -> Some(MK_COMB(a,b)) in
      let tm1 = match th0 with None -> tm | Some th -> rand(concl th) in
      (match bstep_top conv tm1,th0 with
         None,None -> raise Bstep_unchanged
       | None,Some th -> th
       | Some th1,None -> th1
       | Some th1,Some th -> TRANS th th1)
  | _ -> raise Bstep_unchanged;;

(* The conversions applied at a node: lane extraction, reduction of terms    *)
(* whose arguments are literals, address arithmetic, the platform's extra    *)
(* word conversions, simple word rewrites, and folding of definitions.       *)

let BSTEP_WORD_THMS =
  [WORD_XOR_REFL; WORD_ADD_0; WORD_AND_REFL; WORD_OR_REFL;
   WORD_ZX_BITVAL; WORD_SUB_REFL; WORD_OR_0; WORD_ZX_0; NOT_LT;
   WORD_SX_0; SUB_EQ_0; SUB_REFL; LE_REFL; LT_REFL; NOT_LE;
   WORD_ZX_TRIVIAL; WORD_SX_TRIVIAL; COND_CLAUSES; NOT_CLAUSES;
   BITVAL_CLAUSES; AND_CLAUSES; OR_CLAUSES; REFL_CLAUSE;
   EQ_CLAUSES];;

(* The fixed set: the lane conversions first (word_subword of a word_join    *)
(* tree, word_subword of simple words, WORD_WIDTH_CONV), then reductions,    *)
(* address arithmetic, the platform's word conversions and the simple word   *)
(* rewrites, with the proof's ~rewrites and the folds of its definitions.    *)
(* A rewrite that pushes word_subword into the arguments of an operator,     *)
(* such as WORD_SUBWORD_AND, makes new word_subword nodes: they are          *)
(* simplified in turn, so that the lane of a word_and of a constant and a    *)
(* word_join tree becomes word_and (word 15) (b 0), one node per level the   *)
(* lane goes down.                                                           *)

let bstep_node_conv ?(rewrites:thm list = []) (folds:thm list) : conv =
  let rw = GEN_REWRITE_CONV I
    (BSTEP_WORD_THMS @ [WORD_SUBWORD_AND] @ rewrites @ map GSYM folds) in
  let rec conv tm =
    (WORD_JOIN_LANE_CONV ORELSEC WORD_SIMPLE_SUBWORD_CONV ORELSEC
     WORD_WIDTH_CONV ORELSEC
     MEMO_GROUND_REDUCE_CONV ORELSEC NORMALIZE_ADD_SUBTRACT_WORD_CONV ORELSEC
     apply_extra_word_convs ORELSEC push) tm
  and push tm =
    let th = rw tm in
    match rand(concl th) with
      Comb(Comb(op,a),b)
        when is_word_subword tm &&
             (is_word_subword a || is_word_subword b) ->
        TRANS th (MK_COMB(AP_TERM op (sub a),sub b))
    | _ -> th
  and sub t =
    if not(is_word_subword t) then REFL t else
    match bstep_top conv t with Some th -> th | None -> REFL t in
  conv;;

(* A memory component with its address simplified, |- c = c', or None. The   *)
(* address is put in the form of NORMALIZE_RELATIVE_ADDRESS_CONV, a base     *)
(* plus one offset (word_add a (word (16 * i + 14)) for                      *)
(* word_add (word_add a (word (16 * i))) (word 14)), so that a read finds    *)
(* the fact about the same bytes however the code computed the address. The  *)
(* results are kept for the session, unless a block has its own rewrites     *)
(* (which may depend on its assumptions): then for that block only.          *)
(*                                                                           *)
(* This state, like the other state of the block being run below (the side  *)
(* conditions, the branch rewrites and the decided conditions), is per       *)
(* domain (see common/par.ml): a block runs on one domain from start to end, *)
(* without waiting for other computations, and sets it when it starts. The  *)
(* caches for the session are per domain too.                                *)

let bstep_component_cache : unit -> thm option Termtbl.t =
  par_local (fun () -> Termtbl.create 1024);;
let bstep_component_block : unit -> thm option Termtbl.t =
  par_local (fun () -> Termtbl.create 256);;
let bstep_address_conv rewrites =
  DEPTH_CONV
   (NORMALIZE_RELATIVE_ADDRESS_CONV ORELSEC bstep_node_conv ~rewrites []);;
let bstep_component_conv =
  let default = bstep_address_conv [] in
  par_local (fun () -> ref default);;
let bstep_component_local = par_local (fun () -> ref false);;

let bstep_set_component_rewrites (rewrites:thm list) =
  Termtbl.reset (bstep_component_block ());
  bstep_component_conv () := bstep_address_conv rewrites;
  bstep_component_local () := (rewrites <> []);;

let bstep_norm_component c =
  let tbl = if !(bstep_component_local ()) then bstep_component_block ()
            else bstep_component_cache () in
  try Termtbl.find tbl c with Not_found ->
  let r = match c with
      Comb(Comb(Const(":>",_) as op,(Const("memory",_) as m)),Comb(k,a)) ->
        (match bstep_top !(bstep_component_conv ()) a with
           None -> None
         | Some th -> Some(AP_TERM (mk_comb(op,m)) (AP_TERM k th)))
    | _ -> None in
  (match r with
     Some th when hyp th <> [] -> ()
   | _ -> Termtbl.replace tbl c r);
  r;;

(* The simplification of the template of an instruction, done once per       *)
(* program address: reductions, address arithmetic and the simple word       *)
(* rewrites, so that the step theorems do not depend on a proof's rewrites;  *)
(* the lane conversions apply per step, where the values are known.          *)

let bstep_generic_conv =
  DEPTH_CONV WORD_NUM_RED_CONV THENC
  DEPTH_CONV
   (GEN_REWRITE_CONV I [BITVAL_CLAUSES] ORELSEC
    WORD_RED_CONV ORELSEC
    WORD_WIDTH_CONV ORELSEC
    NORMALIZE_ADD_SUBTRACT_WORD_CONV ORELSEC
    apply_extra_word_convs ORELSEC
    NUM_RED_CONV ORELSEC
    INT_RED_CONV) THENC
  PURE_REWRITE_CONV BSTEP_WORD_THMS;;

(* ------------------------------------------------------------------------- *)
(* 4. One step theorem per program address.                                  *)
(*                                                                           *)
(* For the instruction at offset k of the code mc loaded at word pc:         *)
(*                                                                           *)
(*   |- read PC s = word(pc + k) ==> loaded s (word pc) mc                   *)
(*      ==> read c1 s = x1 ==> ... ==> read cm s = xm ==> side conditions    *)
(*      ==> steps_to step s W                                                *)
(*                                                                           *)
(* made by running the instruction semantics on a state variable s with      *)
(* only the PC and the code as context. Every `read c s` left in the update  *)
(* is named by a variable: registers first, then memory, whose addresses     *)
(* may use the register values. A condition such as `aligned 16 (read SP s)` *)
(* that the semantics needs is assumed, and becomes a side condition in      *)
(* terms of the values. The update W is a chain of writes ending in s; its   *)
(* values are simplified once, here. A step is then one INST with the        *)
(* actual values and state, and one MP per antecedent.                       *)
(*                                                                           *)
(* Facts about the base pc of the code alone, which the architecture names   *)
(* (arch_base_facts) and the goal has as assumptions, are assumed too when   *)
(* they simplify the update: on AArch64, aligned 4096 (word pc), with which  *)
(* the page that ADRP computes, word_and (word(pc + k)) (word 0xFF..F000),   *)
(* is word_add (word pc) (word k') for the numeral k' = k - k MOD 4096.      *)
(* Such a fact becomes an antecedent of the step theorem, which is made and  *)
(* kept for the goals that have the fact, and a step proves it from the      *)
(* assumption (Req_base), at no cost that depends on the values.             *)
(* ------------------------------------------------------------------------- *)

(* What an architecture provides.                                            *)

type bstep_arch =
  { arch_name : string;                    (* for messages *)
    arch_step : term;                      (* `arm` *)
    arch_state : hol_type;                 (* `:armstate` *)
    arch_pc : term;                        (* `PC` *)
    arch_loaded : string;                  (* "aligned_bytes_loaded" *)
    arch_loaded_update : thm;              (* aligned_bytes_loaded_update *)
    arch_conv : thm option array -> thm list -> conv;
    arch_insn : thm option array -> int -> string;
                                           (* the instruction, for messages  *)
    arch_alias : term -> (term * thm) option;
       (* for a written component d that another component c reads in full   *)
       (* (x86: YMM0_SSE and YMM0), c and |- !y t. read c (write d y t) = y  *)
    arch_base_facts : term -> (term * (thm -> conv)) list;
       (* for the base `word pc` of the code, facts about pc that the step    *)
       (* theorems may assume when the goal has them, each with a conversion  *)
       (* of the template that uses it (AArch64: aligned 4096 (word pc), and  *)
       (* the pages that ADRP computes; see bstep_make_gen)                  *)
  };;

type bstep_req =
    Req_read of term * term       (* component, variable *)
  | Req_side of term              (* side condition on the variables *)
  | Req_base of term;;            (* a fact about the base of the code *)

type bstep_gen =
  { gen_th : thm;
    gen_undef : term list;            (* the undefined values, bound in    *)
                                      (* gen_th; [] for most instructions    *)
    gen_reqs : bstep_req list;
    gen_layers : (term * term) list;  (* generic (component, value) of W,   *)
                                      (* outermost first                     *)
    gen_s : term;                     (* the state variable                 *)
    gen_insn : string;
  };;

(* Numbered from 1, distinct over all domains.                              *)

let bstep_var_count = par_counter ();;

let bstep_fresh_var pre ty =
  mk_var("bstep_" ^ pre ^ string_of_int (bstep_var_count () + 1),ty);;

(* The distinct `read c s` subterms of tm, inner ones first.                 *)

let bstep_reads s tm =
  let rec go tm acc =
    match tm with
      Comb(Comb(Const("read",_),c),s') when s' = s ->
        let acc' = go c acc in
        if exists (fun t -> compare t tm = 0) acc' then acc' else tm::acc'
    | Comb(a,b) -> go a (go b acc)
    | Abs(_,b) -> go b acc
    | _ -> acc in
  rev(go tm []);;

let rec bstep_write_layers tm =
  match tm with
    Comb(Comb(Comb(Const("write",_),d),y),t) -> (d,y)::bstep_write_layers t
  | _ -> [];;

(* The postcondition variable of the step theorems with undefined values.    *)

let bstep_post_var s = mk_var("bstep_P",mk_fun_ty (type_of s) bool_ty);;

let bstep_make_gen arch decode_ths mc pcv k
    (base:(term * (thm -> conv)) list) =
  let s = mk_var("s",arch.arch_state) and s' = mk_var("s'",arch.arch_state) in
  let insn = try arch.arch_insn decode_ths k with Failure _ -> "?" in
  let fail msg =
    bstep_fail (Printf.sprintf
      "cannot make the step theorem for offset 0x%x (%s): %s" k insn msg) in
  let word_tm = mk_const("word",[`:64`,`:N`]) in
  let pctm = if k = 0 then mk_comb(word_tm,pcv) else
             mk_comb(word_tm,mk_binary "+" (pcv,mk_small_numeral k)) in
  let pc_th = ASSUME(mk_eq(list_mk_icomb "read" [arch.arch_pc;s],pctm)) in
  let ld_tm = list_mk_icomb arch.arch_loaded [s;mk_comb(word_tm,pcv);mc] in
  let ld_th = ASSUME ld_tm in
  let atm = list_mk_comb(arch.arch_step,[s;s']) in
  let conv ctx = try arch.arch_conv decode_ths ctx atm
                 with Failure msg -> fail ("the semantics failed: " ^ msg) in
  let eth0 = conv [pc_th;ld_th] in
  (* Alignment conditions on values read from s are assumed: those left in   *)
  (* the update, and those the architecture's conversion assumed itself.     *)
  let is_al t = match strip_comb t with
      Const("aligned",_),[_;x] -> vfree_in s x | _ -> false in
  let als_upd = find_terms is_al (rand(concl eth0)) in
  let als = setify(als_upd @ filter is_al (hyp eth0)) in
  let eth0 =
    if als_upd = [] then eth0 else conv ([pc_th;ld_th] @ map ASSUME als) in
  let name pre rds =
    map (fun r -> let v = bstep_fresh_var pre (type_of r) in
                  (rand(rator r),v),ASSUME(mk_eq(r,v))) rds in
  let subst facts th = if facts = [] then th else
    CONV_RULE(RAND_CONV(GEN_REWRITE_CONV TOP_DEPTH_CONV (map snd facts))) th in
  let regfacts =
    name "r" (filter (fun r -> not(mentions_memory(rand(rator r))))
                     (bstep_reads s (list_mk_conj(rand(concl eth0)::als)))) in
  let eth1 = subst regfacts eth0 in
  let alfacts = map (fun h ->
      let e = GEN_REWRITE_CONV TOP_DEPTH_CONV (map snd regfacts) h in
      rand(concl e),EQ_MP (SYM e) (ASSUME(rand(concl e)))) als in
  let eth1 = itlist (fun (_,th) acc -> PROVE_HYP th acc) alfacts eth1 in
  let memfacts =
    name "m" (filter (mentions_memory o rand o rator)
                     (bstep_reads s (rand(concl eth1)))) in
  let eth2 = subst memfacts eth1 in
  if bstep_reads s (rand(concl eth2)) <> [] then
    fail "reads of the state are left in the update" else
  (* The update is `W = s'` or, with undefined values u, `?u. W = s'`.       *)
  let rec under_ex c tm =
    if is_exists tm then BINDER_CONV (under_ex c) tm else LAND_CONV c tm in
  let eth3 = CONV_RULE(RAND_CONV(under_ex bstep_generic_conv)) eth2 in
  (* The facts about the base, where they change the update.                *)
  let eth3,base_used =
    if base = [] then eth3,[] else
    let bconv = FIRST_CONV (map (fun (t,mk) -> mk (ASSUME t)) base) in
    match (try Some(CONV_RULE(RAND_CONV(under_ex
                     (CHANGED_CONV(ONCE_DEPTH_CONV bconv) THENC
                      bstep_generic_conv))) eth3)
           with Failure _ -> None) with
      None -> eth3,[]
    | Some th ->
        th,filter (fun t -> exists (fun h -> compare h t = 0) (hyp th))
                  (map fst base) in
  let undef,weq = strip_exists(rand(concl eth3)) in
  let w = match weq with
      Comb(Comb(Const("=",_),w),s'') when s'' = s' -> w
    | _ -> fail "the update is not of the form `W = s'` or `?u. W = s'`" in
  let layers = bstep_write_layers w in
  let rec base t = match t with
      Comb(Comb(Comb(Const("write",_),_),_),t') -> base t'
    | _ -> t in
  if base w <> s then fail "the update is not a chain of writes" else
  if exists (fun (d,y) -> vfree_in s d || vfree_in s y) layers then
    fail "a written component or value mentions the state" else
  let th1 =
    if undef = [] then
      MP (ISPECL [arch.arch_step;s;w] STEPS_TO_STEP) (GEN s' eth3) else
    (* (!u. eventually step P W) ==> eventually step P s, from               *)
    (* STEPS_SOME_STEP with Q = \s'. ?u. W = s'. A successor exists: the     *)
    (* one with u = ARB; and every successor is W for some u.                *)
    let ex = rand(concl eth3) in
    let pv = bstep_post_var s in
    let ev t = list_mk_icomb "eventually" [arch.arch_step;pv;t] in
    let arbs = map (fun u -> mk_const("ARB",[type_of u,aty])) undef in
    let warb = vsubst (zip arbs undef) w in
    (* |- ?u_k .. u_m. W[ARB/u_1 .. u_(k-1)] = warb, for k = m+1 down to 1   *)
    let rec build sub us arbs' =
      match us,arbs' with
        [],[] -> REFL warb
      | u::us',a::arbs'' ->
          let th = build ((a,u)::sub) us' arbs'' in
          EXISTS (list_mk_exists(us,mk_eq(vsubst sub w,warb)),a) th
      | _ -> fail "undefined values" in
    let eth_ex = EXISTS (mk_exists(s',ex),warb) (build [] undef arbs) in
    let all_tm = list_mk_forall(undef,ev w) in
    let h = ASSUME weq in
    let th_ev =
      EQ_MP (AP_TERM (rator(ev w)) h) (SPECL undef (ASSUME all_tm)) in
    let rec choose us th =
      match us with
        [] -> th
      | u::us' ->
          let th' = choose us' th in
          let ex_tm = list_mk_exists(us,weq) in
          CHOOSE (u,ASSUME ex_tm) th' in
    let th_all = GEN s' (DISCH ex (choose undef th_ev)) in
    let lth = ISPECL [arch.arch_step;s;pv;mk_abs(s',ex)] STEPS_SOME_STEP in
    let lth = CONV_RULE(ONCE_DEPTH_CONV BETA_CONV) lth in
    DISCH all_tm (MP (MP (MP lth (GEN s' eth3)) eth_ex) th_all) in
  let ants = [concl pc_th; ld_tm] @ map (concl o snd) regfacts @
             map (concl o snd) memfacts @ map fst alfacts @ base_used in
  let th2 = itlist DISCH ants th1 in
  if hyp th2 <> [] then fail "unexpected hypotheses" else
  { gen_th = th2;
    gen_undef = undef;
    gen_reqs = map (fun ((c,v),_) -> Req_read(c,v)) (regfacts @ memfacts) @
               map (fun (c,_) -> Req_side c) alfacts @
               map (fun t -> Req_base t) base_used;
    gen_layers = layers;
    gen_s = s;
    gen_insn = insn };;

let bstep_gen_cache :
    unit -> (term * term * int * term list,bstep_gen) Hashtbl.t =
  par_local (fun () -> Hashtbl.create 1024);;

(* ------------------------------------------------------------------------- *)
(* 5. The state of a block of steps.                                         *)
(*                                                                           *)
(* State i is the term s_i = write d y (... s_{i-1}), and s_0 is the goal's  *)
(* state variable. Facts |- read c s_j = v are kept in a table keyed by the  *)
(* component c, at the state j where they were made, and are moved to the    *)
(* current state only when an instruction reads them: across register-only   *)
(* steps by one read-over-write row per write, and memory facts across the   *)
(* steps without stores at once, by one theorem per step                     *)
(* |- read memory s_i = read memory s_j (j the last store).                  *)
(* ------------------------------------------------------------------------- *)

type bstep_layer = term * term * term;;   (* component, value, state below *)

type bstep_block =
  { b_arch : bstep_arch;
    b_states : (int,term * bstep_layer list) Hashtbl.t;
       (* i -> (s_i, the writes of step i, outermost first)                  *)
    b_facts : (int * thm) Termtbl.t;     (* c -> (j, |- read c s_j = v) *)
    mutable b_keys : term list;
       (* the components of b_facts in the order they got their first        *)
       (* fact, latest first                                                 *)
    b_memsnap : (int,int * thm) Hashtbl.t;
       (* i -> (j, |- read memory s_i = read memory s_j), j the last         *)
       (* store <= i                                                         *)
    b_memory : term;
    b_code : term;                         (* the code component *)
    b_loaded_th : thm;      (* loaded s ==> read code s' = read code s     *)
    b_loaded_s : term * term;  (* ==> loaded s', with its s and s'         *)
    mutable b_n : int;
    mutable b_loaded : thm;                (* |- loaded s_n (word pc) mc *)
    mutable b_frame : (term * thm) option;  (* the frame C and |- C s0' s_n  *)
    b_post : term;                         (* the postcondition P *)
    mutable b_chain : thm;                 (* |- steps_to step t s_n, t the  *)
                                           (* start of the current segment   *)
    mutable b_start : term;                (* that start t *)
    mutable b_segs : (thm * thm) list;
       (* the earlier segments, latest first: the chain to the state s_k     *)
       (* before a step with undefined values u, and                         *)
       (* |- (!u. eventually step P s_{k+1}) ==> eventually step P s_k       *)
    b_forget : (term -> term -> bool) option;
       (* forget c v: the value v written to the component c is forgotten   *)
    b_vars : unit Termtbl.t;
       (* the variables that the run introduced: undefined and forgotten    *)
       (* values                                                            *)
    b_base : (term * thm) list;
       (* the facts about the base of the code that the step theorems may   *)
       (* assume, with their assumptions                                    *)
  };;

let bstep_state blk i = Hashtbl.find blk.b_states i;;

let bstep_put blk c jth =
  if not(Termtbl.mem blk.b_facts c) then blk.b_keys <- c :: blk.b_keys;
  Termtbl.replace blk.b_facts c jth;;

(* Rows and read-over-write theorems (common/components.ml), with their      *)
(* failures as step failures.                                                *)

let bstep_row c d y t =
  try read_write_row c d y t with Failure msg -> bstep_fail msg;;

let bstep_same d y t =
  try read_write_same d y t
  with Failure msg -> bstep_fail (msg ^ ": there is no fact for it");;

(* |- read c s_m = read c s_{m-1} across the writes of step m.               *)

let bstep_row_step blk c m =
  let _,layers = bstep_state blk m in
  end_itlist TRANS (map (fun (d,y,t) ->
      if compare c d = 0 then bstep_fail ("`" ^ string_of_term c ^
         "` is written at step " ^ string_of_int m) else
      bstep_row c d y t) layers);;

(* Move |- read (memory :> d) s_j = v to state n: across the stores in       *)
(* (j,n] one at a time, and across the other steps by the snapshots.         *)

let rec bstep_move_mem blk c d j th n =
  if j = n then th else
  let m,snapn = Hashtbl.find blk.b_memsnap n in
  if m <= j then
    let _,snapj = Hashtbl.find blk.b_memsnap j in
    TRANS (read_compose_lift blk.b_memory d (TRANS snapn (SYM snapj))) th
  else
    let th1 = bstep_move_mem blk c d j th (m - 1) in
    let th2 = TRANS (bstep_row_step blk c m) th1 in
    if m = n then th2 else TRANS (read_compose_lift blk.b_memory d snapn) th2;;

(* |- read c s_n = read c s_j, moving th: |- read c s_j = v.                 *)

let bstep_move blk c j th =
  let n = blk.b_n in
  if j = n then th else
  match c with
    Comb(Comb(Const(":>",_),Const("memory",_)),d) ->
      bstep_move_mem blk c d j th n
  | _ ->
      let rec go m th =
        if m > n then th else go (m + 1) (TRANS (bstep_row_step blk c m) th) in
      go (j + 1) th;;

(* The fact for c at the current state, moved there and stored again. A      *)
(* component without a fact starts from |- read c s_0 = read c s_0.          *)

let bstep_get_fact blk c =
  let j,th =
    try Termtbl.find blk.b_facts c with Not_found ->
    let th = REFL(list_mk_icomb "read" [c;fst(bstep_state blk 0)]) in
    bstep_put blk c (0,th); 0,th in
  if j = blk.b_n then th else
  let th' = bstep_move blk c j th in
  Termtbl.replace blk.b_facts c (blk.b_n,th');
  th';;

(* The state term with the memory addresses of its writes simplified,        *)
(* |- w = w', down to the previous state st.                                 *)

let rec bstep_norm_spine st tm =
  if tm == st then None else
  match tm with
    Comb(Comb(Comb(Const("write",_) as wr,d),y),t) ->
      let et = bstep_norm_spine st t and ed = bstep_norm_component d in
      (match ed,et with
         None,None -> None
       | Some e,None -> Some(AP_THM (AP_THM (AP_TERM wr e) y) t)
       | None,Some e -> Some(AP_TERM (mk_comb(mk_comb(wr,d),y)) e)
       | Some e1,Some e2 -> Some(MK_COMB(AP_THM (AP_TERM wr e1) y,e2)))
  | _ -> bstep_fail "the update is not a chain of writes";;

let rec bstep_layers st tm =
  match tm with
    Comb(Comb(Comb(Const("write",_),d),y),t) ->
      if t == st then [d,y,t] else (d,y,t)::bstep_layers st t
  | _ -> if tm == st then []
         else bstep_fail "the update is not a chain of writes";;

(* The side conditions of a step for the actual values, alignments such as   *)
(* aligned 16 (word_add stackpointer (word 64)), from the static facts.      *)

let bstep_side_cache : unit -> thm Termtbl.t =
  par_local (fun () -> Termtbl.create 64);;

let bstep_side c =
  let bstep_side_cache = bstep_side_cache () in
  try Termtbl.find bstep_side_cache c with Not_found ->
  let th =
    try EQT_ELIM(ALIGNED_WORD_CONV (component_assumptions ()) c)
    with Failure _ ->
      bstep_fail ("cannot prove the side condition " ^
                  string_of_small_term c) in
  Termtbl.replace bstep_side_cache c th; th;;

(* ------------------------------------------------------------------------- *)
(* 6. One step.                                                              *)
(* ------------------------------------------------------------------------- *)

(* The fact for a component that an instruction reads, |- read c s = v at    *)
(* the current state s = st, with the address of c in normal form.           *)
(*                                                                           *)
(* A memory component c that has a fact (or none: then it starts from the    *)
(* state s_0) is moved to s across the stores since, one row per write. That *)
(* does not work if a store d covers only part of c, or c is part of d (the  *)
(* components are not orthogonal, and neither contains the other as a fact). *)
(* The shapes of c and of the stores since the fact decide what to do, and   *)
(* nothing is tried and caught; the latest such store d, with c and d of     *)
(* constant sizes at the same base, gives one of two rules:                  *)
(*                                                                           *)
(*  - d is strictly inside c, and c is a read of 16, 8, 4, 2 or 1 byte pairs *)
(*    (bytes256 to bytes16) whose halves contain d or are disjoint from it:  *)
(*    c is read as the two halves, with READ_MEMORY_BYTESIZED_SPLIT,         *)
(*      |- read (m :> bytes128 a) s =                                        *)
(*         word_join (read (m :> bytes64 (word_add a (word 8))) s)           *)
(*                   (read (m :> bytes64 a) s)                               *)
(*    for example after stp x0, x1, [sp, #288] and then ldr q3, [sp, #288].  *)
(*                                                                           *)
(*  - c is strictly inside d, and the component P of twice the size of c     *)
(*    that holds c and is aligned as d is, lies in d: c is the subword of P, *)
(*      |- read (m :> bytes64 a) s =                                         *)
(*         word_subword (read (m :> bytes128 a) s) (0,64)                    *)
(*    for example after str q0, [sp, #288] and then ldr x3, [sp, #288].      *)
(*                                                                           *)
(* Each part is read by the same rule, so that a part may be split or        *)
(* widened in turn; a component that is being read is not read again within  *)
(* itself. If no rule applies, the fact is moved as before, and a store that *)
(* overlaps c in another way fails the step with the message of the row.     *)
(* The fact made by a rule is kept for c like any other fact.                *)

let bstep_split_info =
  [("bytes256",16,"bytes128",128); ("bytes128",8,"bytes64",64);
   ("bytes64",4,"bytes32",32); ("bytes32",2,"bytes16",16);
   ("bytes16",1,"bytes8",8)];;

(* The position of the split lemma of a component name.                      *)

let bstep_split_index pn =
  let rec idx n l =
    match l with
      (p,_,_,_)::rest -> if p = pn then n else idx (n + 1) rest
    | [] -> failwith "bstep_split_index" in
  idx 0 bstep_split_info;;

(* c = |- read (m :> c a) s = word_subword (read (m :> p a) s) (0,bits) and  *)
(* the same for the part at word_add a (word half), for each split lemma.    *)

let bstep_subword_lemmas =
  let splits = CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT in
  let mk (pn,half,cn,bits) =
    let i = bstep_split_index pn in
    let th = el i splits in
    let tac =
      REWRITE_TAC[th] THEN
      SIMP_TAC[WORD_SUBWORD_JOIN_UPPER; WORD_SUBWORD_JOIN_LOWER;
               DIMINDEX_256; DIMINDEX_128; DIMINDEX_64; DIMINDEX_32;
               DIMINDEX_16; DIMINDEX_8; ARITH] THEN
      CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
      SIMP_TAC[WORD_SUBWORD_TRIVIAL; DIMINDEX_256; DIMINDEX_128; DIMINDEX_64;
               DIMINDEX_32; DIMINDEX_16; DIMINDEX_8; LE_REFL] in
    let hi = parse_term (Printf.sprintf
      "!m (x:A word) s. read (m :> %s (word_add x (word %d))) s = \
       word_subword (read (m :> %s x) s) (%d,%d)" cn half pn bits bits)
    and lo = parse_term (Printf.sprintf
      "!m (x:A word) s. read (m :> %s x) s = \
       word_subword (read (m :> %s x) s) (0,%d)" cn pn bits) in
    prove(hi,REPEAT GEN_TAC THEN tac),prove(lo,REPEAT GEN_TAC THEN tac) in
  map mk bstep_split_info;;

type bstep_cut = Cut_inside | Cut_around;;

(* The latest store since the state s_j whose range cuts that of c, as the   *)
(* kind of cut and the range of the store; None if there is none.            *)

let bstep_cut blk c j =
  match memory_byte_range c with
    None -> None
  | Some(b,ofs,n) ->
      let rec look ls =
        match ls with
          [] -> None
        | (d,_,_)::rest ->
            (match memory_byte_range d with
               Some(b2,ofs2,n2)
                 when compare b b2 = 0 && (ofs2,n2) <> (ofs,n) ->
                 if ofs <= ofs2 && ofs2 + n2 <= ofs + n
                 then Some(Cut_inside,ofs2,n2)
                 else if ofs2 <= ofs && ofs + n <= ofs2 + n2
                 then Some(Cut_around,ofs2,n2)
                 else look rest
             | _ -> look rest) in
      let rec scan m =
        let m',_ = Hashtbl.find blk.b_memsnap m in
        if m' <= j then None else
        match look (snd(bstep_state blk m')) with
          Some r -> Some r
        | None -> scan (m' - 1) in
      scan blk.b_n;;

let bstep_address_term b ofs =
  if ofs = 0 then b else
  let aty = hd(snd(dest_type(type_of b))) in
  let word_add_tm = inst [aty,`:A`] `word_add:A word->A word->A word`
  and word_tm = inst [aty,`:A`] `word:num->A word` in
  mk_comb(mk_comb(word_add_tm,b),mk_comb(word_tm,mk_small_numeral ofs));;

let rec bstep_read_fact blk st active ci =
  match bstep_norm_component ci with
    None -> bstep_read_normal blk st active ci
  | Some e ->
      let th0 = bstep_read_normal blk st active (rand(concl e)) in
      let rd = rator(rator(lhs(concl th0))) in
      TRANS (AP_THM (AP_TERM rd e) st) th0

and bstep_read_normal blk st active c =
  let j = try fst(Termtbl.find blk.b_facts c) with Not_found -> 0 in
  let cut = if j = blk.b_n then None else bstep_cut blk c j in
  let active' = c :: active in
  let fresh x = not(exists (fun y -> compare x y = 0) active') in
  let mem_comp =
    match c with
      Comb(Comb(Const(":>",_),m),Comb(Const(nm,_),a)) -> Some(m,nm,a)
    | _ -> None in
  match cut,mem_comp,memory_byte_range c with
    Some(Cut_inside,ofs2,n2),Some(m,nm,a),Some(b,ofs,n)
      when mem nm (map (fun (p,_,_,_) -> p) bstep_split_info) &&
           (ofs2 + n2 <= ofs + n / 2 || ofs + n / 2 <= ofs2) ->
      let i = bstep_split_index nm in
      let sth =
        ISPECL [m;a;st] (el i (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)) in
      let rhs = rand(concl sth) in
      let wj = rator(rator rhs) in
      let hi_c = rand(rator(rand(rator rhs)))
      and lo_c = rand(rator(rand rhs)) in
      let hi_th = bstep_read_fact blk st active' hi_c in
      let lo_th = bstep_read_fact blk st active' lo_c in
      let th = TRANS sth (MK_COMB(AP_TERM wj hi_th,lo_th)) in
      bstep_put blk c (blk.b_n,th); th
  | Some(Cut_around,ofs2,n2),Some(m,nm,a),Some(b,ofs,n)
      when exists (fun (_,_,cn,_) -> cn = nm) bstep_split_info &&
           (let rel = (ofs - ofs2) mod (2 * n) in rel = 0 || rel = n) &&
           (let pofs = if (ofs - ofs2) mod (2 * n) = 0 then ofs else ofs - n in
            ofs2 <= pofs && pofs + 2 * n <= ofs2 + n2) ->
      let pofs = if (ofs - ofs2) mod (2 * n) = 0 then ofs else ofs - n in
      let pn,_,_,_ = find (fun (_,h,_,_) -> h = n) bstep_split_info in
      let i = bstep_split_index pn in
      let aty = hd(snd(dest_type(type_of a))) in
      let split = el i (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT) in
      let pconst = inst [aty,`:A`]
        (find_term (fun t -> is_const t && fst(dest_const t) = pn)
           (concl split)) in
      let pa = bstep_address_term b pofs in
      let pc = list_mk_icomb ":>" [m;mk_comb(pconst,pa)] in
      let hi_lemma,lo_lemma = el i bstep_subword_lemmas in
      let sth = ISPECL [m;pa;st] (if pofs = ofs then lo_lemma else hi_lemma) in
      let c' = rand(rator(lhs(concl sth))) in
      let e = bstep_norm_component c' in
      let cn = match e with None -> c' | Some e -> rand(concl e) in
      if compare cn c <> 0 || not(fresh pc) then bstep_get_fact blk c else
      let sth' = match e with
          None -> sth
        | Some e ->
            let rd = rator(rator(lhs(concl sth))) in
            TRANS (SYM(AP_THM (AP_TERM rd e) st)) sth in
      let p_th = bstep_read_fact blk st active' pc in
      let th1 = SUBS [p_th] sth' in
      let conv = bstep_node_conv [] in
      let th = match bstep_top conv (rand(concl th1)) with
          None -> th1 | Some e -> TRANS th1 e in
      bstep_put blk c (blk.b_n,th); th
  | _ -> bstep_get_fact blk c


let bstep_mp what ith th =
  try MP ith th with Failure _ ->
    bstep_fail (what ^ ": `" ^
                (try bstep_describe(lhand(concl ith)) with Failure _ -> "?") ^
                "` does not match `" ^ bstep_describe(concl th) ^ "`");;

let bstep_eventually =
  lemma_instance STEPS_TO_EVENTUALLY ["step";"s";"t";"P"] [];;
let bstep_trans = lemma_instance STEPS_TO_TRANS ["step";"s";"t";"u"] [];;
let bstep_refl = lemma_instance STEPS_TO_REFL ["step";"s"] [];;

(* A branch whose condition the simplification of the new value did not      *)
(* decide: the condition alone is simplified again with reductions and the   *)
(* assumptions of the goal that are not facts about its state (bounds, case  *)
(* splits made by the proof script). The assumptions come first, so that an  *)
(* assumption ~(n <= x) decides the condition ~(n <= x) before NOT_LE turns  *)
(* it into x < n. Since values have comparisons in the forms NOT_LE and      *)
(* NOT_LT give, an assumption that is a comparison or an equivalence of      *)
(* comparisons is also used in those forms: n <= x as x < n = F, ~(n <= x)   *)
(* as x < n, and (n <= x <=> p) as (x < n <=> ~p). The condition is usually  *)
(* small; a large one is an error. If the condition is still not decided,    *)
(* the PC fact keeps the simplified condition, and the next step fails.      *)

let bstep_branch_conv = par_local (fun () -> ref (lazy (ALL_CONV,ALL_CONV)));;

let bstep_branch_forms =
  let neg = GEN_REWRITE_CONV I [NOT_LE; NOT_LT]
  and pos = GEN_REWRITE_CONV I [GSYM NOT_LE; GSYM NOT_LT] in
  let is_cmp t = is_binary "<=" t || is_binary "<" t
  and not_tm = `(~)` in
  fun th ->
    let c = concl th in
    try
      if is_cmp c then [EQF_INTRO(CONV_RULE pos th)]
      else if is_neg c && is_cmp(rand c) then [EQT_INTRO(CONV_RULE neg th)]
      else if is_iff c && is_cmp(lhand c) then
        [CONV_RULE (BINOP_CONV(TRY_CONV neg)) (AP_TERM not_tm th)]
      else []
    with Failure _ -> [];;

let bstep_set_branch_rewrites (ths:thm list) =
  bstep_branch_conv () :=
    lazy (let ths = ths @ flat(map bstep_branch_forms ths) in
          REWRITE_CONV ths,REWRITE_CONV(BSTEP_WORD_THMS @ ths));;

(* A conditional in a new value whose condition the same assumptions         *)
(* decide, as in a jump event, is decided too: |- COND c a b = a or b. The   *)
(* decisions are kept for the block; a condition larger than 2000 nodes as   *)
(* a tree is not tried.                                                      *)

let bstep_cond_memo : unit -> thm option Termtbl.t =
  par_local (fun () -> Termtbl.create 256);;

let bstep_decide c =
  let red = DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV ORELSEC
                       INT_RED_CONV) in
  let rw0,rw = Lazy.force !(bstep_branch_conv ()) in
  (red THENC rw0 THENC rw THENC red THENC rw) c;;

let bstep_cond_conv cth =
  RATOR_CONV(RATOR_CONV(RAND_CONV(K cth))) THENC
  TRY_CONV(GEN_REWRITE_CONV I [COND_CLAUSES]);;

let BSTEP_COND_CONV tm =
  match tm with
    Comb(Comb(Comb(Const("COND",_),c),_),_) ->
      let r =
        let bstep_cond_memo = bstep_cond_memo () in
        try Termtbl.find bstep_cond_memo c with Not_found ->
        let r =
          try if term_size_exceeds 2000 c then None else
              let th = bstep_decide c in
              match rand(concl th) with
                Const(("T"|"F"),_) -> Some th
              | _ -> None
          with Failure _ -> None in
        Termtbl.replace bstep_cond_memo c r; r in
      (match r with
         Some th -> bstep_cond_conv th tm
       | None -> failwith "BSTEP_COND_CONV")
  | _ -> failwith "BSTEP_COND_CONV";;

let bstep_decide_branch pc_th =
  match rand(concl pc_th) with
    Comb(Comb(Comb(Const("COND",_),c),_),_) as pc ->
      if term_size_exceeds 20000 c then
        bstep_fail "a branch on a condition of more than 20000 nodes" else
      TRANS pc_th (bstep_cond_conv (bstep_decide c) pc)
  | _ -> pc_th;;

(* The offset k of a PC value word(pc + k) or word pc, for code at word pc.  *)

let bstep_pc_offset pcv tm =
  match tm with
    Comb(Const("word",_),Comb(Comb(Const("+",_),p),kt))
      when p = pcv && is_numeral kt -> Some(dest_small_numeral kt)
  | Comb(Const("word",_),p) when p = pcv -> Some 0
  | _ -> None;;

(* The PC value of the last block run on this domain that stopped because   *)
(* its PC was not at a constant offset in the code, such as a branch on a     *)
(* condition that the facts do not decide (None if the last block did not    *)
(* stop so): a tactic that runs a block can then decide the condition itself  *)
(* and run the block again, without parsing the message of the failure.     *)
(* Per domain, as the other state of a block.                                *)

let bstep_stopped_pc : unit -> term option ref =
  par_local (fun () -> ref None);;

(* A PC value word_add (word pc) (word k), as from a register that holds an  *)
(* address that ADRP computed in the code, is word(pc + k).                  *)

let bstep_pc_norm =
  let conv = REWR_CONV(GSYM WORD_ADD) in
  fun pcv pc_th ->
    match rand(concl pc_th) with
      Comb(Comb(Const("word_add",_),Comb(Const("word",_),p)),
           Comb(Const("word",_),kt)) as t when p = pcv && is_numeral kt ->
        TRANS pc_th (conv t)
    | _ -> pc_th;;

let bstep_one_step blk (gen:int -> bstep_gen) (conv:conv) pcv =
  let i = blk.b_n + 1 in
  let st,_ = bstep_state blk blk.b_n in
  let pc_th = bstep_get_fact blk blk.b_arch.arch_pc in
  let pc_th = bstep_pc_norm pcv (bstep_decide_branch pc_th) in
  let k = match bstep_pc_offset pcv (rand(concl pc_th)) with
      Some k -> k
    | None ->
        bstep_stopped_pc () := Some(rand(concl pc_th));
        bstep_fail ("the PC is not at a constant offset in the code: " ^
                    string_of_small_term(rand(concl pc_th))) in
  let g = gen k in
  (* 1. The instance of the step theorem, with the facts it reads. Undefined *)
  (* values get fresh names, so that each step has its own.                  *)
  let gth,undef =
    if g.gen_undef = [] then g.gen_th,[] else
    let fresh = map (fun u -> bstep_fresh_var "u" (type_of u)) g.gen_undef in
    let env = zip (map (fst o dest_var) fresh)
                  (map (fst o dest_var) g.gen_undef) in
    let c = concl g.gen_th in
    EQ_MP (ALPHA c (deep_alpha env c)) g.gen_th,fresh in
  let theta = ref ((st,g.gen_s) ::
                   if undef = [] then [] else [blk.b_post,bstep_post_var st])
  and ths = ref [blk.b_loaded; pc_th] in
  List.iter (fun r ->
      match r with
        Req_side c -> ths := bstep_side (vsubst !theta c) :: !ths
      | Req_base t -> ths := assoc t blk.b_base :: !ths
      | Req_read(c,v) ->
          let ci = vsubst !theta c in
          let th = bstep_read_fact blk st [] ci in
          theta := (rand(concl th),v) :: !theta; ths := th :: !ths)
    g.gen_reqs;
  let ith = INST !theta gth in
  let ith = rev_itlist (fun f th -> bstep_mp "step" th f) (rev !ths) ith in
  (* A value for which the ~forget of the run says so is forgotten: it      *)
  (* becomes a fresh variable x, and the step is cut like a step with        *)
  (* undefined values, with the segment                                      *)
  (* |- (!x. eventually step P w') ==> eventually step P st, where w' has x  *)
  (* for the value y. What holds for every x holds for y. A proof that needs *)
  (* the value then fails, as at a branch on data.                           *)
  let ith,undef =
    match blk.b_forget with
      None -> ith,undef
    | Some _ when undef <> [] -> ith,undef
    | Some forget ->
    let w0 = rand(concl ith) in
    let vars = ref [] in
    let rec go tm =
      if tm == st then tm else
      match tm with
        Comb(Comb(Comb(Const("write",_) as wr,d),y),t) ->
          let t' = go t in
          if forget d y then begin
            let x = bstep_fresh_var "u" (type_of y) in
            vars := (x,y) :: !vars;
            mk_comb(mk_comb(mk_comb(wr,d),x),t')
          end else if t' == t then tm
          else mk_comb(mk_comb(mk_comb(wr,d),y),t')
      | _ -> bstep_fail "the update is not a chain of writes" in
    let w0' = go w0 in
    if !vars = [] then ith,undef else
    let xs = map fst !vars and ys = map snd !vars in
    let all_tm = list_mk_forall(xs,list_mk_icomb "eventually"
                                [blk.b_arch.arch_step;blk.b_post;w0']) in
    let est = fst(bstep_eventually
                    [blk.b_arch.arch_step; st; w0; blk.b_post]) in
    DISCH all_tm (MP (MP est ith) (SPECL ys (ASSUME all_tm))),xs in
  List.iter (fun u -> Termtbl.replace blk.b_vars u ()) undef;
  (* The state after the step: from |- steps_to step st w, or with undefined *)
  (* values u from |- (!u. eventually step P w) ==> eventually step P st,    *)
  (* where u is free in w and a new segment of the chain starts at w.        *)
  let w0 = if undef = [] then rand(concl ith)
           else rand(snd(strip_forall(lhand(concl ith)))) in
  let w,eqo = match bstep_norm_spine st w0 with
      None -> w0,None
    | Some eq -> rand(concl eq),Some eq in
  let layers = bstep_layers st w in
  Hashtbl.replace blk.b_states i (w,layers);
  blk.b_n <- i;
  (* 2. Facts for the components written; the outermost write wins.          *)
  let rec walk outer gl ll seen =
    match gl,ll with
      (_,yg)::gl',((d,y,t) as lay)::ll' ->
        let seen' =
          if exists (fun e -> compare e d = 0) seen then seen else begin
            let th1 =
              itlist (fun (d',y',t') th -> TRANS (bstep_row d d' y' t') th)
                outer (bstep_same d y t) in
            let th2 = try TRANS th1 (bstep_norm conv yg y)
                      with Bstep_unchanged -> th1 in
            bstep_put blk d (i,th2);
            (* The component that reads d in full gets the same value.       *)
            (match blk.b_arch.arch_alias d with
               None -> ()
             | Some(c,ath) ->
                 let th3 = itlist (fun (d',y',t') th ->
                     TRANS (bstep_row c d' y' t') th)
                   outer (ISPECL [y;t] ath) in
                 bstep_put blk c (i,TRANS th3 (TRANS (SYM th1) th2)));
            d::seen
          end in
        walk (outer @ [lay]) gl' ll' seen'
    | [],[] -> ()
    | _ -> bstep_fail "the update does not match the step theorem" in
  walk [] g.gen_layers layers [];
  (* 3. The memory snapshot and the code.                                    *)
  let snap =
    if exists (fun (d,_,_) -> mentions_memory d) layers
    then (i,REFL(list_mk_icomb "read" [blk.b_memory;w])) else
    let j,th = Hashtbl.find blk.b_memsnap (i - 1) in
    j,TRANS (bstep_row_step blk blk.b_memory i) th in
  Hashtbl.replace blk.b_memsnap i snap;
  let cth = end_itlist TRANS
    (map (fun (d,y,t) -> bstep_row blk.b_code d y t) layers) in
  let ls,ls' = blk.b_loaded_s in
  let lth = INST [st,ls; w,ls'] blk.b_loaded_th in
  blk.b_loaded <- bstep_mp "code" (bstep_mp "code" lth blk.b_loaded) cth;
  (* 4. The frame.                                                           *)
  (match blk.b_frame with
     None -> ()
   | Some(ct,fth) ->
       let fth' = itlist (fun (d,y,t) th ->
           let lth,s0v,tv,yv =
             try maychange_write_theorem ct d with Failure _ ->
               bstep_fail ("the write to `" ^ string_of_term d ^
                           "` is not allowed by the frame") in
           MP (INST [rand(rator(concl th)),s0v; t,tv; y,yv] lth) th)
         layers fth in
       blk.b_frame <- Some(ct,fth'));
  (* 5. The chain.                                                           *)
  let step_to th = match eqo with
      None -> th
    | Some eq -> EQ_MP (AP_TERM (rator(concl th)) eq) th in
  if undef = [] then begin
    let tth = fst(bstep_trans [blk.b_arch.arch_step; blk.b_start; st; w]) in
    blk.b_chain <-
      bstep_mp "chain" (bstep_mp "chain" tth blk.b_chain) (step_to ith)
  end else begin
    blk.b_segs <- (blk.b_chain,ith) :: blk.b_segs;
    blk.b_start <- w0;
    blk.b_chain <- step_to (fst(bstep_refl [blk.b_arch.arch_step; w0]))
  end;
  ();;

(* ------------------------------------------------------------------------- *)
(* 7. A block of steps as a tactic.                                          *)
(* ------------------------------------------------------------------------- *)

(* The components c of the reads `read c s` in tm, if those are the only     *)
(* occurrences of s and every c is closed; None otherwise.                   *)

let bstep_reads_only s tm =
  let tbl = Hashtbl.create 256 in
  let rec go tm acc =
    match tm with
      Comb(Comb(Const("read",_),c),s') when s' = s ->
        if vfree_in s c then raise Not_found else
        if exists (fun d -> compare c d = 0) acc then acc else c::acc
    | Var(_,_) -> if tm = s then raise Not_found else acc
    | Const(_,_) -> acc
    | _ -> if phys_seen tbl tm then acc else begin
             phys_add tbl tm;
             match tm with
               Comb(a,b) -> go a (go b acc)
             | Abs(v,b) -> if v = s then acc else go b acc
             | _ -> acc
           end in
  try Some(go tm []) with Not_found -> None;;

(* Move a fact that reads the state s only through `read c s`, such as       *)
(* bignum_from_memory (a,k) s = n or a precondition on all the elements of   *)
(* an array, !i. i < 256 ==> read (memory :> bytes16 (...)) s = x i, to      *)
(* another state, by the equations |- read c s = read c s' that move c       *)
(* gives. Quantifiers are stripped to fresh variables (avoiding the terms    *)
(* in avoid) and antecedents are added to the component assumptions, for     *)
(* the orthogonality of the addresses; then the fact is put back together.   *)
(* Fails if an antecedent mentions s or a component cannot be moved.         *)

let bstep_move_general s (avoid:term list Lazy.t) (move:term -> thm) th =
  let rec strip th ops used =
    match concl th with
      Comb(Const("!",_),Abs(x,_)) ->
        let used = match used with Some u -> u | None -> Lazy.force avoid in
        let x' = variant used x in
        strip (SPEC x' th) ((true,x') :: ops) (Some(x'::used))
    | Comb(Comb(Const("==>",_),a),_) ->
        strip (UNDISCH th) ((false,a) :: ops) used
    | _ -> th,ops in
  let th2,ops = strip th [] None in
  let ants = mapfilter (fun (g,a) -> if g then failwith "" else a) ops in
  if exists (shared_occurs s) ants then failwith "bstep_move_general" else
  let cs = match bstep_reads_only s (concl th2) with
      Some cs when cs <> [] -> cs
    | _ -> failwith "bstep_move_general" in
  let old = component_assumptions () in
  if ants <> [] then
    set_component_assumptions (flat(map (CONJUNCTS o ASSUME) ants) @ old);
  let eqs = try Some(map move cs) with Failure _ | Bstep_failure _ -> None in
  if ants <> [] then set_component_assumptions old;
  match eqs with
    None -> failwith "bstep_move_general"
  | Some eqs ->
      rev_itlist (fun (g,t) th -> if g then GEN t th else DISCH t th)
        ops (GEN_REWRITE_RULE ONCE_DEPTH_CONV eqs th2);;

(* tm with every `read c t` replaced by `read c s`, for t the term old       *)
(* (found by physical identity first).                                       *)

let rec bstep_retarget s old tm =
  match tm with
    Comb(Comb(Const("read",_) as r,c),t) when t == old || compare t old = 0 ->
      mk_comb(mk_comb(r,c),s)
  | Comb(a,b) -> mk_comb(bstep_retarget s old a,bstep_retarget s old b)
  | Abs(v,b) -> mk_abs(v,bstep_retarget s old b)
  | _ -> tm;;

(* The instance of `loaded s pc mc ==> read code s' = read code s ==>        *)
(* loaded s' pc mc`, without binders, for this code; for relocated code the  *)
(* length theorem is matched to the code term first.                         *)

let bstep_loaded_rule arch mc_length_th mc_tm base_w =
  let sv = mk_var("s",arch.arch_state)
  and sv' = mk_var("s'",arch.arch_state) in
  let lth = try PART_MATCH (rand o lhs) mc_length_th mc_tm
            with Failure _ -> mc_length_th in
  let th = UNDISCH(SPECL [sv;base_w] (MATCH_MP arch.arch_loaded_update lth)) in
  let th' = DISCH (hd(hyp th)) (SPEC sv' th) in
  let code = rand(rator(lhs(lhand(rand(concl th'))))) in
  th',(sv,sv'),code;;

(* Run a block of at most count steps from the goal `eventually step P s0`,  *)
(* stopping early before a step whose PC satisfies stop. The new goal is     *)
(* `eventually step P sn`, sn named sname, with these assumptions, in this   *)
(* order (the first is the oldest):                                          *)
(*                                                                           *)
(*  1. the assumptions that are not moved, as they are and in their order:   *)
(*     those that do not mention s0, and the facts about s0 that are not     *)
(*     moved (because their component is not kept, a write overlaps part of  *)
(*     it, or they are not of a form that bstep moves);                      *)
(*  2. the code and the PC at sn, and the frame `C s0' sn` if the            *)
(*     postcondition has one;                                                *)
(*  3. `read c sn = v` for each component c with keep c that has a fact at   *)
(*     the end of the block (it had one at s0, or was written or read in the *)
(*     block), in the order the components first got a fact: those at s0     *)
(*     in the order of their assumptions, then the others as the steps made  *)
(*     them;                                                                 *)
(*  4. the other facts about s0 that mention it only in reads `read c s0`    *)
(*     with keep c, moved to sn, in their order.                             *)
(*                                                                           *)
(* A fact made in the block for a component that a later write overlaps in   *)
(* part is not in the new goal. Values are not changed when moved: a value   *)
(* that reads s0 still reads s0. The postcondition is not changed. ~rewrites *)
(* are used at template nodes and on memory addresses, and ~folds are        *)
(* folded into new values (see bstep_node_conv).                             *)

let bstep_mono = lemma_instance SUBSUMED_MP ["R";"s";"s'";"C"] [];;

(* Named frames. A frame may be a constant defined as a frame of MAYCHANGE   *)
(* lists, such as MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI on AArch64, or   *)
(* have such constants among its clauses; the architecture lists their       *)
(* definitions |- C = R in bstep_frame_defs. bstep works with the frames     *)
(* unfolded (bstep_frame_unfold, |- R0 = R0' with every named frame in R0    *)
(* unfolded, None if there is none) and gives the frame facts of the new     *)
(* goal in the form of the postcondition, which BSTEP_FINAL_TAC matches.     *)

let bstep_frame_defs = ref ([]:thm list);;

let bstep_frame_unfold =
  let cache =
    par_local (fun () -> (Termtbl.create 64 : thm option Termtbl.t)) in
  fun r ->
    if !bstep_frame_defs = [] then None else
    let cache = cache () in
    try Termtbl.find cache r with Not_found ->
    let res =
      match (try Some(PURE_REWRITE_CONV !bstep_frame_defs r)
             with Failure _ -> None) with
        Some th when compare (rand(concl th)) r <> 0 -> Some th
      | _ -> None in
    Termtbl.replace cache r res; res;;

(* tm is `R x s` for a frame R of MAYCHANGE lists, ,, and named frames       *)
(* (checked at the head only).                                               *)

let bstep_is_frame tm =
  is_maychange_frame tm ||
  match tm with
    Comb(Comb(Comb(Const(_,_) as r,_),_),_) ->
      exists (fun th -> compare (lhs(concl th)) r = 0) !bstep_frame_defs
  | Comb(Comb(Const(_,_) as r,_),_) ->
      exists (fun th -> compare (lhs(concl th)) r = 0) !bstep_frame_defs
  | _ -> false;;

(* From |- R x s, |- R' x s with the named frames of R unfolded; and back,   *)
(* from |- R' x s and the R of the original form.                            *)

let bstep_frame_expand th =
  match concl th with
    Comb(Comb(r,x),s) ->
      (match bstep_frame_unfold r with
         None -> th
       | Some eq -> EQ_MP (AP_THM (AP_THM eq x) s) th)
  | _ -> th;;

let bstep_frame_fold r th =
  match bstep_frame_unfold r,concl th with
    Some eq,Comb(Comb(_,x),s) -> EQ_MP (SYM(AP_THM (AP_THM eq x) s)) th
  | _ -> th;;

(* Metavariables. In a safety proof the postcondition holds metavariables,   *)
(* and in a loop body the assumptions too (the events of the invariant).     *)
(* They are instantiated when the proof is finished, and the theorems        *)
(* that the justifications get have instantiated hypotheses; so the          *)
(* theorems made at tactic time from the assumptions are instantiated        *)
(* too, as INSTANTIATE_ALL does, but only those that mention a               *)
(* metavariable, looked for over shared terms.                               *)

let bstep_instantiator ((_,tmin,tyin) as i:instantiation) =
  if tmin = [] && tyin = [] then (fun th -> th),(fun tm -> tm) else
  if tyin <> [] then INSTANTIATE_ALL i,instantiate i else
  let mvs = map snd tmin in
  let has = shared_occurs_var (fun v -> mem v mvs) in
  (fun th ->
     let hs = filter has (hyp th) in
     if hs = [] && not(has(concl th)) then th else
     funpow (length hs) UNDISCH (INSTANTIATE i (rev_itlist DISCH hs th))),
  (fun tm -> if has tm then instantiate i tm else tm);;

let BSTEP_RUN_TAC (arch:bstep_arch)
    ?(keep:term -> bool = fun _ -> true)
    ?(folds:thm list = []) ?(rewrites:thm list = [])
    ?(stop:term -> bool = fun _ -> false) ?(first:int = 1)
    ?forget ?carry
    ((mc_length_th,decode_ths):thm * thm option array)
    (count:int) (sname:string) : tactic =
  fun (asl,w) ->
  let t0 = Sys.time() in
  bstep_stopped_pc () := None;
  let fail msg = failwith (arch.arch_name ^ "_BSTEP_TAC: " ^ msg) in
  let s0,p_tm = match w with
      Comb(Comb(Comb(Const("eventually",_),st),p),s0)
        when compare st arch.arch_step = 0 -> s0,p
    | _ -> fail "the goal is not `eventually step P s`" in
  if not(is_var s0) then fail "the state of the goal is not a variable" else
  if count <= 0 then ALL_TAC (asl,w) else
  (* Sort the assumptions: facts `read c s0 = v`, the code, frames, other    *)
  (* facts about s0, and static ones.                                        *)
  let is_read_fact th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s)),_) ->
        s = s0 && not(vfree_in s0 c)
    | _ -> false in
  let is_loaded th = match strip_comb(concl th) with
      Const(c,_),[s;_;_] -> c = arch.arch_loaded && s = s0
    | _ -> false in
  let is_frame th = bstep_is_frame(concl th) && rand(concl th) = s0 in
  (* A flag fact `read c s0` or `~read c s0` is the fact read c s0 = T or F, *)
  (* and the conjuncts of a conjunction of facts are facts too.              *)
  let flag_fact th = match concl th with
      Comb(Comb(Const("read",_),c),s) when s = s0 && not(vfree_in s0 c) ->
        Some(EQT_INTRO th)
    | Comb(Const("~",_),Comb(Comb(Const("read",_),c),s))
        when s = s0 && not(vfree_in s0 c) -> Some(EQF_INTRO th)
    | _ -> None in
  let is_flag th = match flag_fact th with Some _ -> true | None -> false in
  let seeds_of th =
    if is_read_fact th then [th] else
    match flag_fact th with
      Some th' -> [th']
    | None -> if is_conj(concl th) then filter is_read_fact (CONJUNCTS th)
              else [] in
  let read_facts = flat(map (seeds_of o snd) (rev asl)) in
  let rest = filter (fun (_,th) -> not(is_read_fact th) && not(is_flag th))
               asl in
  let ld_th = try snd(find (is_loaded o snd) rest)
              with Failure _ -> fail "no code fact" in
  let frames = map snd (filter (is_frame o snd) rest) in
  let rest =
    filter (fun (_,th) -> not(th == ld_th) && not(is_frame th)) rest in
  let in_s0 = shared_occurs s0 in
  let static_asl,others_asl =
    partition (fun (_,th) -> not(in_s0 (concl th))) rest in
  let static = map snd static_asl in
  let generals = mapfilter (fun (_,th) ->
      match bstep_reads_only s0 (concl th) with
        Some cs when forall keep cs -> (th,cs)
      | _ -> failwith "") others_asl in
  set_component_assumptions static;
  bstep_set_branch_rewrites (static @ map snd others_asl);
  Termtbl.reset (bstep_side_cache ());
  (* The code, its base address and the code component.                      *)
  let base_w,mc_tm = match snd(strip_comb(concl ld_th)) with
      [_;b;m] -> b,m | _ -> fail "code fact" in
  let pcv = rand base_w in
  if not(is_var pcv) then fail "the code is not loaded at `word pc`" else
  let loaded_th,loaded_s,code =
    bstep_loaded_rule arch mc_length_th mc_tm base_w in
  (* The facts about the base of the code that the goal has.                 *)
  let base_convs = filter (fun (t,_) ->
      exists (fun th -> compare (concl th) t = 0) static)
    (arch.arch_base_facts base_w) in
  let base = map (fun (t,_) ->
      t,find (fun th -> compare (concl th) t = 0) static) base_convs in
  (* The frame of the postcondition, if it has one.                          *)
  let frame_conj =
    try let bv,bod = dest_abs p_tm in
        Some(find (fun c -> (maychange_term c || bstep_is_frame c) &&
                            rand c = bv) (conjuncts bod))
    with Failure _ -> None in
  (* The frame and the assumption are used with their named frames          *)
  (* unfolded (bstep_frame_unfold); the frame fact of the new goal is folded *)
  (* back into the form of the postcondition.                                *)
  let frame_post = match frame_conj with
      Some cj -> Some(rator(rator cj)) | None -> None in
  let frame,frame0 = match frame_conj with
      None -> None,None
    | Some cj ->
        let ct0 = rator(rator cj) and x = rand(rator cj) in
        let ct = match bstep_frame_unfold ct0 with
            Some eq -> rand(concl eq) | None -> ct0 in
        let fth0 =
          try find (fun th -> compare (rand(rator(concl th))) x = 0) frames
          with Failure _ -> fail "no MAYCHANGE assumption for the frame" in
        let fth = bstep_frame_expand fth0 in
        let r = rator(rator(concl fth)) in
        if compare r ct = 0 then Some(ct,fth),Some fth0 else
        let sub =
          try subsumed_theorem r ct with Failure _ ->
            fail ("the MAYCHANGE assumption " ^ string_of_small_term r ^
                  " is not within the frame " ^ string_of_small_term ct) in
        Some(ct,MP (MP (fst(bstep_mono [r;x;s0;ct])) fth) sub),Some fth0 in
  (* The block.                                                              *)
  let blk =
    { b_arch = arch;
      b_states = Hashtbl.create 2048;
      b_facts = Termtbl.create 1024;
      b_keys = [];
      b_memsnap = Hashtbl.create 2048;
      b_memory = rand(rator code);
      b_code = code;
      b_loaded_th = loaded_th;
      b_loaded_s = loaded_s;
      b_n = 0;
      b_loaded = ld_th;
      b_frame = frame;
      b_post = p_tm;
      b_chain = fst(bstep_refl [arch.arch_step; s0]);
      b_start = s0;
      b_segs = [];
      b_forget = forget;
      b_vars = Termtbl.create 64;
      b_base = base } in
  Hashtbl.replace blk.b_states 0 (s0,[]);
  Hashtbl.replace blk.b_memsnap 0
    (0,REFL(list_mk_icomb "read" [blk.b_memory;s0]));
  if not(exists (fun th -> rand(rator(lhs(concl th))) = arch.arch_pc)
                read_facts)
  then fail "no PC fact" else
  let gen k =
    let key = (mc_tm,pcv,k,map fst base) in
    let cache = bstep_gen_cache () in
    try Hashtbl.find cache key with Not_found ->
    let g = bstep_make_gen arch decode_ths mc_tm pcv k base_convs in
    Hashtbl.add cache key g; g in
  Termtbl.reset (bstep_cond_memo ());
  let conv = BSTEP_COND_CONV ORELSEC bstep_node_conv ~rewrites folds in
  bstep_set_component_rewrites rewrites;
  (* The facts at s0, keyed by their components in the normal form that      *)
  (* reads use (memory addresses simplified as at the steps). A later        *)
  (* assumption about the same component wins.                               *)
  let seed_key : term Termtbl.t = Termtbl.create 64 in
  List.iter (fun th ->
      let c0 = rand(rator(lhs(concl th))) in
      let c,th = match bstep_norm_component c0 with
          None -> c0,th
        | Some e ->
            let rd = rator(rator(lhs(concl th))) in
            rand(concl e),TRANS (SYM(AP_THM (AP_TERM rd e) s0)) th in
      Termtbl.replace seed_key c0 c;
      bstep_put blk c (0,th)) read_facts;
  (* A component that the value of a fact at s0 reads, as in                 *)
  (* read RAX s0 = read (memory :> bytes64 a) s0, is read at s0 too, so      *)
  (* that the new goal relates it to sn if the block does not change it.     *)
  let seen = Hashtbl.create 1024 in
  let rec val_reads v acc =
    match v with
      Comb(Comb(Const("read",_),c),s) when s = s0 ->
        if vfree_in s0 c || exists (fun d -> compare c d = 0) acc then acc
        else c::acc
    | Var(_,_) | Const(_,_) -> acc
    | _ -> if phys_seen seen v then acc else begin
             phys_add seen v;
             match v with
               Comb(a,b) -> val_reads a (val_reads b acc)
             | Abs(_,b) -> val_reads b acc
             | _ -> acc
           end in
  let vcs = itlist (fun th acc -> val_reads (rand(concl th)) acc)
              (rev read_facts) [] in
  List.iter (fun c0 ->
      let c = match bstep_norm_component c0 with
          None -> c0 | Some e -> rand(concl e) in
      if not(Termtbl.mem blk.b_facts c) then ignore(bstep_get_fact blk c))
    (rev vcs);
  (* The steps.                                                              *)
  let rec run () =
    if blk.b_n >= count then () else
    let pc = rand(concl(bstep_get_fact blk arch.arch_pc)) in
    if stop pc then () else begin
      let where () =
        Printf.sprintf "step %d, %s" (first + blk.b_n)
          (match bstep_pc_offset pcv pc with
             Some k -> Printf.sprintf "PC offset 0x%x, `%s`" k
                         (try arch.arch_insn decode_ths k
                          with Failure _ -> "?")
           | None -> "PC not constant") in
      (try bstep_one_step blk gen conv pcv
       with Bstep_failure msg | Failure msg ->
         bstep_set_component_rewrites []; fail (where () ^ ": " ^ msg));
      run ()
    end in
  run ();
  let n = blk.b_n in
  bstep_set_component_rewrites [];
  if n = 0 then ALL_TAC (asl,w) else
  (* The facts of the new goal.                                              *)
  let wn = fst(bstep_state blk n) in
  let gvars = shared_vars (w :: map (concl o snd) asl) in
  let sn = variant gvars (mk_var(sname,arch.arch_state)) in
  let pc_th = bstep_get_fact blk arch.arch_pc in
  let pc_th = try bstep_pc_norm pcv (bstep_decide_branch pc_th)
              with Failure _ | Bstep_failure _ -> pc_th in
  (* 3. The read facts, in the order their components first got a fact.      *)
  (* With ~carry, a component that is not kept has its fact in the new goal  *)
  (* if carry c v holds for its value v and v has none of the variables the  *)
  (* run introduced (a fact with such a variable cannot leave the block: the *)
  (* justification generalizes it). The facts of the other components that   *)
  (* are not kept are dropped, and so are their facts at s0.                 *)
  let carried c =
    match carry with
      None -> false
    | Some p ->
        (try let v = rand(concl(snd(Termtbl.find blk.b_facts c))) in
             p c v && not(exists (Termtbl.mem blk.b_vars) (frees v))
         with Not_found -> false) in
  let keys = filter (fun c ->
      compare c arch.arch_pc <> 0 && (keep c || carried c))
    (rev blk.b_keys) in
  let kept =
    mapfilter (fun c -> try c,bstep_get_fact blk c
                        with Bstep_failure _ -> failwith "") keys in
  (* 4. The other facts about s0 (bstep_move_general). Their moved form      *)
  (* has the final state under the binders, which the justification walks    *)
  (* once.                                                                   *)
  let move c =
    SYM(bstep_move blk c 0 (REFL(list_mk_icomb "read" [c;s0]))) in
  let moved_pairs =
    mapfilter (fun (th,_) ->
        th,bstep_move_general s0 (Lazy.from_val gvars) move th)
      (rev generals) in
  let moved_generals = map snd moved_pairs in
  let frame_ths = match blk.b_frame,frame_post with
      Some(_,f),Some ct0 -> [bstep_frame_fold ct0 f]
    | _ -> [] in
  let fin = [blk.b_loaded; pc_th] @ frame_ths @ map snd kept @
            moved_generals in
  let retarget th =
    let tm = concl th in
    if th == blk.b_loaded then
      (match strip_comb tm with
         f,[_;b;m] -> list_mk_comb(f,[sn;b;m])
       | _ -> fail "code fact")
    else if exists (fun f -> f == th) frame_ths then mk_comb(rator tm,sn)
    else match tm with
      Comb(Comb(Const("=",_) as e,Comb(Comb(Const("read",_) as r,c),_)),v)
        when not(exists (fun g -> g == th) moved_generals) ->
        mk_comb(mk_comb(e,mk_comb(mk_comb(r,c),sn)),v)
    | _ -> bstep_retarget sn wn tm in
  let fin_tms = map retarget fin in
  (* 1. The assumptions that stay: all but the code, the frame used, the     *)
  (* facts about s0 whose component has a fact at sn (the PC included), and  *)
  (* the moved general facts.                                                *)
  let kept_tbl : unit Termtbl.t = Termtbl.create 256 in
  List.iter (fun (c,_) -> Termtbl.replace kept_tbl c ()) kept;
  let moved_comp c =
    let c = try Termtbl.find seed_key c with Not_found -> c in
    compare c arch.arch_pc = 0 || Termtbl.mem kept_tbl c ||
    (carry <> None && not(keep c)) in
  let moved th =
    th == ld_th ||
    (match frame0 with Some f -> f == th | None -> false) ||
    exists (fun (th0,_) -> th0 == th) moved_pairs ||
    (match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s)),_)
         when s = s0 && is_read_fact th -> moved_comp c
     | Comb(Comb(Const("read",_),c),s) when is_flag th -> moved_comp c
     | Comb(Const("~",_),Comb(Comb(Const("read",_),c),s)) when is_flag th ->
         moved_comp c
     | _ -> false) in
  let stays = filter (fun (_,th) -> not(moved th)) asl in
  let newasl = rev_itlist (fun tm l -> ("",ASSUME tm)::l) fin_tms stays in
  if !bstep_verbose then
    Printf.printf "%s_BSTEP_TAC: %d steps to %s, %.2f s, %d facts kept, %d assumptions\n%!"
      arch.arch_name n (fst(dest_var sn)) (Sys.time() -. t0) (length fin)
      (length newasl);
  let chain = blk.b_chain and segs = blk.b_segs in
  let w' = mk_comb(rator w,sn) in
  let just i ths =
    match ths with
      [th] ->
        let ith,itm = bstep_instantiator i in
        let wn' = itm wn in
        let th1 = INST [wn',sn] (itlist (DISCH o itm) fin_tms th) in
        let th2 = rev_itlist (fun f th -> MP th (ith f)) fin th1 in
        let p = rand(rator(concl th2)) in
        let back chain t th =
          let chain = ith chain in
          let s = lhand(concl chain) in
          MP (MP (fst(bstep_eventually [arch.arch_step; s; t; p])) chain) th in
        (* Back through the segments: at a step with undefined values u,     *)
        (* the theorem holds for every u, and the step's theorem applies.    *)
        (* Like the facts, the final state, the chains and the step          *)
        (* theorems are made at tactic time, and are instantiated            *)
        (* (bstep_instantiator): the state holds the events, which may hold  *)
        (* metavariables.                                                    *)
        rev_itlist (fun (chain',nth) r ->
            let nth = ith nth in
            let us = fst(strip_forall(lhand(concl nth))) in
            let r' = MP nth (GENL us r) in
            back chain' (rand(concl r')) r')
          segs (back chain wn' th2)
    | _ -> failwith "BSTEP_RUN_TAC: justification" in
  (null_meta,[newasl,w'],just);;

(* The step tactics of the architectures: BSTEP_STEPS_TAC arch execth (m--n) *)
(* runs the steps m..n as one block, leaving a goal about the state "s<n>".  *)

let BSTEP_STEPS_TAC (arch:bstep_arch) ?keep ?folds ?rewrites ?forget execth
    snums =
  if snums = [] then ALL_TAC else
  let m = hd snums and n = last snums in
  if snums <> (m--n) then
    failwith (arch.arch_name ^ "_BSTEP_TAC: the steps are not m--n") else
  BSTEP_RUN_TAC arch ?keep ?folds ?rewrites ?forget ~first:m execth
    (length snums) ("s" ^ string_of_int n);;

(* ------------------------------------------------------------------------- *)
(* 8. Working with the final facts without walking their values.             *)
(* ------------------------------------------------------------------------- *)

(* tm with the subterm old (found by physical identity) replaced by a        *)
(* variable: a template for bstep_norm. Walks tm only down to old.           *)

let bstep_abstract_at old tm =
  let v = genvar(type_of old) in
  let rec go tm =
    if tm == old then v else
    match tm with
      Comb(f,x) -> let f' = go f and x' = go x in
                   if f' == f && x' == x then tm else mk_comb(f',x')
    | _ -> tm in
  go tm;;

(* BSTEP_MEMORY_SPLIT_TAC n p replaces each assumption                       *)
(* read (memory :> bytes128 a) s = V with p (memory :> bytes128 a) by the    *)
(* facts for its 64-bit (n = 1), 32-bit (n = 2) or 16-bit (n = 3) parts, as  *)
(* READ_MEMORY_SPLIT_CONV does, and takes the lanes out of V without         *)
(* walking into V.                                                           *)

let BSTEP_MEMORY_SPLIT_RULE =
  let conv = bstep_node_conv [] in
  fun n th ->
    let v = rand(concl th) in
    map (fun t ->
        let r = rand(concl t) in
        try TRANS t (bstep_norm conv (bstep_abstract_at v r) r)
        with Bstep_unchanged -> t)
      (CONJUNCTS(CONV_RULE (READ_MEMORY_SPLIT_CONV n) th));;

let BSTEP_MEMORY_SPLIT_TAC n (p:term -> bool) : tactic =
  fun (asl,w) ->
    let sel,rest = partition (fun (_,th) ->
        match concl th with
          Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),_) -> p c
        | _ -> false) asl in
    let newths =
      itlist (fun (_,th) acc -> BSTEP_MEMORY_SPLIT_RULE n th @ acc) sel [] in
    null_meta,[map (fun th -> "",ASSUME(concl th)) (rev newths) @ rest,w],
    (fun i ths -> match ths with
        [th] -> let ith,_ = bstep_instantiator i in
                itlist (PROVE_HYP o ith) newths th
      | _ -> failwith "BSTEP_MEMORY_SPLIT_TAC");;

(* ------------------------------------------------------------------------- *)
(* 9. Safety proofs.                                                         *)
(*                                                                           *)
(* The goal is `exists f_events. forall e ... ensures step                   *)
(* (\s. ... read events s = e) (\s. read PC s = dest /\ exists e2.           *)
(* read events s = APPEND e2 e /\ e2 = f_events ... /\ memaccess_inbounds    *)
(* e2 ...) ...`. f_events becomes a metavariable; the code is run until the  *)
(* PC reaches dest, keeping the events and the components the postcondition  *)
(* reads; the trace is abbreviated once and f_events is found by             *)
(* unification at the end. The chain of steps does not mention the           *)
(* postcondition, so the metavariable costs nothing per step.                *)
(*                                                                           *)
(* The engine knows nothing of this policy. BSTEP_RUN_TAC has two hooks:     *)
(* ~forget c v generalizes the value v written to the component c at the    *)
(* step: it becomes a fresh variable x and the step is cut like a step with  *)
(* undefined values, with |- (!x. eventually step P w') ==> eventually step  *)
(* P st (a proof for all x is a proof for the value, and one that needs the  *)
(* value fails, as at a branch on data). ~carry c v takes the fact of a      *)
(* component that is not kept to the new goal; a fact whose value has a      *)
(* variable that the run introduced (undefined or forgotten) never is.      *)
(*                                                                           *)
(* The data of the code, such as the digits in a multiplication, do not      *)
(* matter for a safety proof, but their values do: in a carry chain each     *)
(* value contains the earlier ones twice, so as a tree it grows              *)
(* exponentially with the number of steps, and the kernel walks values as    *)
(* trees where a step is cut (undefined flags such as those of x86 MUL) and  *)
(* when the justification instantiates. The safety layer, below, forgets     *)
(* the data and runs in blocks, so that the state of a block is a chain of   *)
(* the writes of the block, not of all the steps before. A new block starts  *)
(* with the facts of the components that are not kept and are small (the     *)
(* pointers) and with the events, abbreviated by a variable and an           *)
(* assumption (the events grow with the steps, and walks of them would be    *)
(* quadratic); at the end the events are expanded once and the facts of the  *)
(* other components are dropped.                                             *)
(* ------------------------------------------------------------------------- *)

(* The policy: a value of more than bstep_data_size nodes as a tree is data  *)
(* and is forgotten if its component is not kept, and the run goes in       *)
(* blocks of bstep_block_length steps. The sizes were chosen from the        *)
(* measured safety proofs of x86 P-521 point addition and scalar             *)
(* multiplication; the values of pointers and addresses, as in the stack     *)
(* and the loop counters, are much smaller than the digits of an             *)
(* arithmetic, so the same numbers do for the proofs of other code.         *)

let bstep_data_size = 400;;
let bstep_block_length = 256;;

let bstep_forget_data (keep:term -> bool) = fun c v ->
  not(keep c) && term_size_exceeds bstep_data_size v;;

let BSTEP_SAFETY_RUN_TAC (arch:bstep_arch) exec (dest_pc:term) : tactic =
  W(fun (asl,w) ->
    let bv,bod = dest_abs(rand(rator w)) in
    let post_reads = mapfilter (fun t -> match t with
        Comb(Comb(Const("read",_),c),s) when s = bv -> c
      | _ -> fail()) (find_terms (fun t -> match t with
        Comb(Comb(Const("read",_),_),s) -> s = bv | _ -> false) bod) in
    let keep c = (match c with Const("events",_) -> true | _ -> false) ||
                 exists (fun d -> compare c d = 0) post_reads in
    let forget = bstep_forget_data keep
    and carry = fun _ v -> not(term_size_exceeds bstep_data_size v) in
    let reached (asl,w) =
      exists (fun (_,th) ->
         let c = concl th in
         is_eq c && is_binary "read" (lhs c) &&
         compare (lhand(lhs c)) arch.arch_pc = 0 &&
         rand(lhs c) = rand w && compare (rhs c) dest_pc = 0) asl in
    (* The value of the events grows with the steps, and the kernel walks   *)
    (* it as a tree in each step with undefined or forgotten values. So     *)
    (* after each block it is abbreviated, by a variable and an assumption  *)
    (* `value = variable` (the value has the previous variable in it, and   *)
    (* is small); the end expands them again, once.                         *)
    let ev_vars = ref [] in
    let is_ev_var v = is_var v && mem v !ev_vars in
    let is_events_fact sn th =
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
             Const("events",_)),s)),_) -> s = sn
      | _ -> false in
    let abbrev_events (asl,w as g) =
      match (try Some(find (fun (_,th) -> is_events_fact (rand w) th) asl)
             with Failure _ -> None) with
        Some(_,th) when not(is_var(rand(concl th))) ->
          let v = rand(concl th) in
          let e = bstep_fresh_var "ev" (type_of v) in
          ev_vars := e :: !ev_vars;
          ABBREV_TAC (mk_eq(e,v)) g
      | _ -> ALL_TAC g in
    let expand_events (asl,w as g) =
      let eqs = mapfilter (fun (_,th) ->
          let c = concl th in
          if is_eq c && is_ev_var(rhs c) then SYM th else failwith "") asl in
      if eqs = [] then ALL_TAC g else
      (RULE_ASSUM_TAC (fun th ->
          if is_events_fact (rand w) th then REWRITE_RULE eqs th else th) THEN
       DISCARD_ASSUMPTIONS_TAC (fun th ->
          let c = concl th in is_eq c && is_ev_var(rhs c))) g in
    (* At the end, the facts about the components that are not kept are of  *)
    (* no use to what follows; the many assumptions slow it down.           *)
    let drop_facts (asl,w as g) =
      let sn = rand w in
      DISCARD_ASSUMPTIONS_TAC (fun th ->
          match concl th with
            Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s)),_) ->
              s = sn && compare c arch.arch_pc <> 0 && not(keep c)
          | _ -> false) g in
    let rec blocks () =
      BSTEP_RUN_TAC arch ~keep ~forget ~carry
        ~stop:(fun pc -> compare pc dest_pc = 0)
        exec bstep_block_length "s_end" THEN
      (fun g -> if reached g then (expand_events THEN drop_facts) g
                else (abbrev_events THEN blocks ()) g) in
    blocks ()) THEN
  W(fun (asl,w) ->
    if exists (fun (_,th) ->
         let c = concl th in
         is_eq c && is_binary "read" (lhs c) &&
         compare (lhand(lhs c)) arch.arch_pc = 0 &&
         rand(lhs c) = rand w && compare (rhs c) dest_pc = 0) asl
    then ALL_TAC
    else failwith (arch.arch_name ^ "_BSTEP_SAFETY_TAC: did not reach " ^
                   "the PC `" ^ string_of_term dest_pc ^ "`"));;

(* ------------------------------------------------------------------------- *)
(* 10. Contracts: going through an ensures theorem.                          *)
(*                                                                           *)
(* A callee (or a part of the code proved separately) is used through its    *)
(* theorem |- ensures step Pre Post Frame. From the goal `eventually step R  *)
(* s` with s a variable, GEN_BSTEP_CALL_TAC proves Pre s from the            *)
(* assumptions and leaves `eventually step R s'` for a new state variable    *)
(* s' about which the assumptions are: the conjuncts of Post s', the facts   *)
(* about s whose components the frame does not touch, the code, and the      *)
(* MAYCHANGE facts extended by the frame. The callee may end in many         *)
(* states, so s' is a universally quantified variable: its justification is  *)
(* a GEN over s', which looks at the values of the facts that cross the      *)
(* call, once.                                                               *)
(* ------------------------------------------------------------------------- *)

let BSTEP_CALL_LEMMA = prove
 (`ensures (step:S->S->bool) P Q C
   ==> P s /\ (!s'. Q s' /\ C s s' ==> eventually step R s')
   ==> eventually step R s`,
  MESON_TAC[ENSURES_IMP_EVENTUALLY]);;

let bstep_seq = lemma_instance SEQ_INTRO ["R";"x";"s";"C";"s'"] [];;

let GEN_BSTEP_CALL_TAC (arch:bstep_arch) ?(keep:term -> bool = fun _ -> true)
    ((mc_length_th,_):thm * thm option array)
    (coreth:thm) (sname:string) : tactic =
  fun (asl,w) ->
  let fail msg = failwith (arch.arch_name ^ "_BSTEP_CALL_TAC: " ^ msg) in
  let s = match w with
      Comb(Comb(Comb(Const("eventually",_),_),_),s) when is_var s -> s
    | _ -> fail "the goal is not `eventually step P s` for a variable s" in
  let in_s = shared_occurs s in
  let static = filter (fun (_,th) -> not(in_s (concl th))) asl in
  let s' = variant (shared_vars (w :: map (concl o snd) asl))
                   (mk_var(sname,type_of s)) in
  let lth = try MATCH_MP BSTEP_CALL_LEMMA coreth
            with Failure _ -> fail "the theorem is not `ensures ...`" in
  (* After the call: the new assumptions, as theorems with the hypothesis    *)
  (* Post s' /\ Frame s s', which DISCH_THEN discharges. In order: the       *)
  (* assumptions that are not moved, as they are; the facts about s that     *)
  (* the frame does not touch, the code and the frames, moved to s', in      *)
  (* their order; the conjuncts of Post s', in their order.                  *)
  let gvars = lazy(shared_vars (w :: map (concl o snd) asl)) in
  let after qth (asl,w) =
    let cj = CONJUNCTS qth in
    let fth = last cj in
    let posts = if bstep_is_frame(concl fth) then butlast cj else cj in
    let fr = rator(rator(concl fth)) in
    (* The callee's frame with its named frames unfolded, for the components *)
    (* that it keeps.                                                        *)
    let fthx = bstep_frame_expand fth in
    let frx = rator(rator(concl fthx)) in
    let rec move th =
      let tm = concl th in
      match tm with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s1)),_)
          when s1 = s && keep c ->
          (try TRANS (MP (SPECL [s;s'] (frame_keeps c frx)) fthx) th
           with Failure _ -> failwith "")
      | Comb(Comb(Comb(Const(ld,_),s1),base),mc)
          when ld = arch.arch_loaded && s1 = s ->
          let lrule,(sv,sv'),code =
            bstep_loaded_rule arch mc_length_th mc base in
          (try
             let kth = MP (SPECL [s;s'] (frame_keeps code frx)) fthx in
             MP (MP (INST [s,sv; s',sv'] lrule) th) kth
           with Failure _ -> failwith "")
      | Comb(Comb(r,x),s1) when s1 = s && bstep_is_frame tm ->
          (* (r ,, fr) x s', and r x s' if every component of fr is within   *)
          (* a clause of r (maychange_absorb, which must then succeed). The  *)
          (* named frames of r and fr are unfolded for that (rx and frx),    *)
          (* and the result has r as it is.                                  *)
          let th1 = MP (MP (fst(bstep_seq [r;x;s;fr;s'])) th) fth in
          let rx = match bstep_frame_unfold r with
              Some eq -> rand(concl eq) | None -> r in
          let within =
            match (try Some(maychange_components rx,maychange_components frx)
                   with Failure _ -> None) with
              Some(rs,fs) ->
                forall (fun d -> exists (component_may_contain d) rs) fs
            | None -> false in
          if not within then th1 else
          let sub =
            try maychange_absorb rx frx with Failure msg ->
              bstep_fail ("the callee's frame `" ^ string_of_small_term fr ^
                    "` is not absorbed into `" ^ string_of_small_term r ^
                    "`: " ^ msg) in
          let sub =
            if rx == r && frx == fr then sub else
            let tm = list_mk_icomb "subsumed" [list_mk_icomb ",," [r;fr]; r] in
            EQ_MP (SYM(PURE_REWRITE_CONV !bstep_frame_defs tm)) sub in
          MP (MP (fst(bstep_mono [rator(rator(concl th1));x;s';r])) th1) sub
      | _ when in_s tm -> general th
      | _ -> failwith ""
    (* A fact that reads s only through components that the frame does not   *)
    (* touch (bstep_move_general).                                           *)
    and general th =
      bstep_move_general s gvars (fun c ->
          if keep c then SYM(MP (SPECL [s;s'] (frame_keeps c fr)) fth)
          else failwith "") th in
    let moved =
      if posts == cj then [] else
      mapfilter (fun (_,th) -> th,move th) asl in
    let stays = filter (fun (_,th) ->
        not(exists (fun (th0,_) -> th0 == th) moved)) asl in
    null_meta,
    [map (fun th -> "",th) (rev posts) @ map (fun (_,th) -> "",th) moved @
     stays,w],
    (fun i ths -> match ths with [th] -> th | _ -> fail "justification") in
  let after qth g =
    set_component_assumptions (map snd static);
    try after qth g with Bstep_failure msg -> fail msg in
  (* X_GEN_TAC s' without its check that s' is new, which walks every        *)
  (* assumption as a tree: s' was chosen new above, walking them as shared   *)
  (* terms.                                                                  *)
  let gen_s' (asl,w) =
    let x,bod = dest_forall w in
    null_meta,[asl,vsubst[s',x] bod],
    (fun i ths -> match ths with
       [th] -> CONV_RULE(GEN_ALPHA_CONV x) (GEN s' th)
     | _ -> fail "justification") in
  (* Existential conjuncts of the postcondition, such as the events of a     *)
  (* safety theorem, are chosen, as new variables bstep_e<k>: a variant of   *)
  (* the bound name, such as e2', could be the name that a later             *)
  (* META_EXISTS_TAC gives its metavariable.                                 *)
  let is_ex_post (_,th) = is_exists(concl th) && vfree_in s' (concl th) in
  (MATCH_MP_TAC lth THEN CONJ_TAC THENL
    [BETA_TAC THEN
     W(fun (asl,w) -> ACCEPT_TAC
         (try prove_from_assumptions asl w
          with Failure msg -> fail msg));
     gen_s' THEN BETA_TAC THEN DISCH_THEN after THEN
     REPEAT(W(fun (asl,w) ->
       match filter is_ex_post asl with
         (_,th)::_ ->
           let x = fst(dest_exists(concl th)) in
           UNDISCH_THEN (concl th)
            (X_CHOOSE_THEN (bstep_fresh_var "e" (type_of x)) STRIP_ASSUME_TAC)
       | [] -> NO_TAC))])
  (asl,w);;

(* ------------------------------------------------------------------------- *)
(* 11. The end of a simulation.                                              *)
(*                                                                           *)
(* BSTEP_FINAL_TAC turns `eventually step P s` into P s and proves the frame *)
(* conjuncts of P s that are assumptions.                                    *)
(* ------------------------------------------------------------------------- *)

let BSTEP_FINAL_TAC : tactic =
  W(fun (asl,w) ->
    let sn = rand w in
    let frames = filter (fun th -> bstep_is_frame(concl th) &&
                                   rand(concl th) = sn) (map snd asl) in
    GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ1_TAC THEN
    GEN_REWRITE_TAC TRY_CONV [BETA_THM] THEN REWRITE_TAC frames);;
