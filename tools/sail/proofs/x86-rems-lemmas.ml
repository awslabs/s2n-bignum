(* Normalization and flag facts for REMS x86 register forms.

   REMS instruction bodies take a decoded instruction, read and write
   GPRs through read_gpr/write_gpr, keep the arithmetic flags in a packed
   32-bit rflags register and advance RIP. The exports bind rflags to the
   low half of HOL rflags and rip to HOL RIP; each theorem names these
   components. Normalization evaluates the selected body by value, keeping
   registers, flags and state symbolic, then relates REMS's integer flag
   tests to the existing shina intermediate bit forms. The shina facts
   then give s2n-bignum's flag expressions.

   These are support facts, not instruction claims. They interpret no
   instruction: every rewrite is a proved word, integer or state identity. *)
needs "tools/sail/proofs/x86-gpr-lemmas.ml";;
needs "tools/sail/proofs/x86-gpr-claims.ml";;
needs "tools/sail/proofs/tuple-apply-conv.ml";;

(* REMS bodies advance RIP past the instruction; s2n-bignum's core
   relations do not. This observation restores the entry RIP after the
   exported computation. It hides only the final RIP value: reads of RIP,
   faults and every other state component remain observed. *)
let sail_hl_x86_core = new_definition
 `sail_hl_x86_core (R:x86state->x86state->bool) s t <=>
    ?u. R s u /\ t = write RIP (read RIP s) u`;;

let SAIL_HL_X86_RIP_TWICE = prove
 (`!a b (x:x86state). write RIP a (write RIP b x) = write RIP a x`,
  REPEAT GEN_TAC THEN SPEC_TAC(`x:x86state`,`x:x86state`) THEN
  REWRITE_TAC[GSYM FORALL_X86STATE; x86state_COMPONENTS]);;

(* One-bit fields of the packed REMS flags, below bit 32, are the HOL
   Boolean flag components. Writes preserve the other 63 bits of rflags. *)
let SAIL_HL_X86_REMS_FLAG_READ = prove
 (`!k s. k < 32
         ==> word_subword (read (rflags :> bottom_32) s:32 word) (k,1):1 word =
             word(bitval(read (rflags :> bitelement k) s))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bottom_32; bottomhalf; READ_SUBWORD;
              READ_BITELEMENT] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_BITVAL] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let SAIL_HL_X86_REMS_FLAG_WRITE = prove
 (`!k (v:1 word) s. k < 32
         ==> write (rflags :> bottom_32)
               (word_insert (read (rflags :> bottom_32) s:32 word) (k,1) v) s =
             write (rflags :> bitelement k) (bit 0 v) s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE; READ_COMPONENT_COMPOSE] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[bottom_32; bottomhalf; READ_SUBWORD] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; WRITE_SUBWORD_BITWISE] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM READ_BITELEMENT; READ_WRITE_BITELEMENT_GEN] THEN
  REWRITE_TAC[READ_BITELEMENT; BIT_WORD_INSERT; BIT_WORD_SUBWORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SUB_0; LE_0; ADD_CLAUSES] THEN
  ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[SUB_REFL; LE_REFL] THENL
   [ASM_SIMP_TAC[ARITH_RULE `k < 32 ==> k < 64 /\ k < k + 1`];
    SUBGOAL_THEN `~(k <= i /\ i < k + 1)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;

(* CF, PF, AF, ZF, SF and OF are bits 0, 2, 4, 6, 7 and 11. *)
let SAIL_HL_X86_REMS_FLAG_BITS = [0;2;4;6;7;11];;

let sail_hl_x86_rems_flag_instances theorem =
  map (fun k ->
    let th = SPEC_ALL (SPEC (mk_small_numeral k) theorem) in
    GEN_ALL (MP th (EQT_ELIM (NUM_REDUCE_CONV (lhand (concl th))))))
  SAIL_HL_X86_REMS_FLAG_BITS;;

let SAIL_HL_X86_REMS_FLAG_READS =
  sail_hl_x86_rems_flag_instances SAIL_HL_X86_REMS_FLAG_READ;;
let SAIL_HL_X86_REMS_FLAG_WRITES =
  sail_hl_x86_rems_flag_instances SAIL_HL_X86_REMS_FLAG_WRITE;;

let SAIL_HL_X86_REMS_BIT0_COND = prove
 (`!c. (bit 0 (if c then word 1 else word 0:1 word) <=> c) /\
       (bit 0 (if c then word 0 else word 1:1 word) <=> ~c)`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_REDUCE_CONV);;

let SAIL_HL_X86_REMS_BIT1 = prove
 (`!b. (word (bitval b):1 word = word 1) <=> b`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* write_user_rflags rewrites every flag; INC and DEC write CF's own
   initial value. Such a write leaves the state unchanged when no earlier
   write in the chain changed that flag. *)
let SAIL_HL_X86_REMS_KEEP = prove
 (`!k s:x86state.
     write (rflags :> bitelement k) (read (rflags :> bitelement k) s) s = s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WRITE_COMPONENT_COMPOSE; READ_COMPONENT_COMPOSE] THEN
  SUBGOAL_THEN `!w:int64. write (bitelement k) (read (bitelement k) w) w = w`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN X_GEN_TAC `i:num` THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM READ_BITELEMENT; READ_WRITE_BITELEMENT_GEN] THEN
    MESON_TAC[];
    SPEC_TAC(`s:x86state`,`s:x86state`) THEN
    REWRITE_TAC[GSYM FORALL_X86STATE; x86state_COMPONENTS]]);;

let SAIL_HL_X86_REMS_KEEP_CONV tm =
  match tm with
  | Comb(Comb(Comb(Const("write",_) as w,c),
              (Comb(Comb(Const("read",_) as r,c'),s0) as v)),x)
      when c = c' ->
      if x = s0 then PART_MATCH lhs SAIL_HL_X86_REMS_KEEP tm else
      let read_x = DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV
        (mk_comb(mk_comb(r,c),x)) in
      if rand(concl read_x) <> v then failwith "SAIL_HL_X86_REMS_KEEP_CONV";
      let th = AP_THM (AP_TERM (mk_comb(w,c)) (SYM read_x)) x in
      TRANS th (PART_MATCH lhs SAIL_HL_X86_REMS_KEEP (rand(concl th)))
  | _ -> failwith "SAIL_HL_X86_REMS_KEEP_CONV";;

(* The bodies rebuild a register number from REX.R/B and a ModR/M field. *)
let SAIL_HL_X86_REMS_REGISTER_INDEX = prove
 (`!r:4 word. (if bit 3 r then word_or (word 8) (word_zx (word_subword r (0,3):3 word))
               else word_zx (word_subword r (0,3):3 word)) = r`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_4] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_ZX; BIT_WORD_SUBWORD; DIMINDEX_4; DIMINDEX_3] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[BIT_WORD] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP
    (ARITH_RULE `i < 4 ==> i = 0 \/ i = 1 \/ i = 2 \/ i = 3`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[DIMINDEX_4] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[]);;

(* Evaluation of a generated model by value.

   The compset holds the model's own function equations, the case
   eliminator of its result type, and the standard numeral, integer and
   word evaluators. Conditionals are lazy, so an untaken branch with a
   symbolic guard is not unfolded. Simple lets beta-reduce directly; paired
   lets reduce once their value is a pair. A few proved conversions keep
   decoding symbolic but small: bits and slices of joined words, the
   recovered register number and iword(&(val x)) at the same width. *)
let SAIL_HL_X86_REMS_LET = prove
 (`!f:A->B. !x. LET f x = f x`, REWRITE_TAC[LET_DEF]);;

(* A paired lambda's body is the rest of the instruction, which
   GEN_BETA_CONV traverses several times per binding. The tuple
   application conversion inserts the body into a small proved schema and
   leaves a curried application for evaluation to reduce. *)
let SAIL_HL_X86_REMS_GABS_CONV =
  let tuple_beta = SAIL_HL_TUPLE_APPLY_CONV () ORELSEC GEN_BETA_CONV in
  fun tm ->
    match tm with
    | Comb(Comb(Const("GABS",_),_),x) when is_pair x -> tuple_beta tm
    | _ -> failwith "SAIL_HL_X86_REMS_GABS_CONV";;

(* The REX byte is a join of the 0100 marker with register bits; its
   comparison with zero decides on the marker. *)
let SAIL_HL_X86_REMS_JOIN_ZERO = prove
 (`!a:M word. !b:N word. dimindex(:P) = dimindex(:M) + dimindex(:N)
     ==> (word_join a b:P word = word 0 <=> a = word 0 /\ b = word 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; VAL_WORD_JOIN] THEN
  SUBGOAL_THEN `(2 EXP dimindex(:N) * val(a:M word) + val(b:N word)) MOD
                2 EXP dimindex(:P) = 2 EXP dimindex(:N) * val a + val b`
   SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[EXP_ADD] THEN
    MP_TAC(ISPEC `a:M word` VAL_BOUND) THEN MP_TAC(ISPEC `b:N word` VAL_BOUND) THEN
    SPEC_TAC(`2 EXP dimindex(:N)`,`q:num`) THEN
    SPEC_TAC(`2 EXP dimindex(:M)`,`p:num`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    TRANS_TAC LTE_TRANS `q * (val(a:M word) + 1)` THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC];
    REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ]]);;

let SAIL_HL_X86_REMS_ENUM_EQ_CONV distinct =
  let facts = map EQF_INTRO (CONJUNCTS distinct) in
  let facts = facts @ map (EQF_INTRO o GSYM o EQF_ELIM) facts in
  let bit1 = GEN_REWRITE_CONV I [SAIL_HL_X86_REMS_BIT1] in
  let join tm =
    let th = PART_MATCH (lhand o rand) SAIL_HL_X86_REMS_JOIN_ZERO tm in
    MP th (EQT_ELIM
      ((DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) (lhand (concl th)))) in
  fun tm -> match tm with
    | Comb(Comb(Const("=",_),l),r) when is_const l && is_const r ->
        if l = r then EQT_INTRO (REFL l)
        else find (fun th -> lhs(concl th) = tm) facts
    | _ -> try bit1 tm with Failure _ -> join tm;;

let SAIL_HL_X86_REMS_BIT_CONV =
  let rewrite = GEN_REWRITE_CONV I
    [BIT_WORD_JOIN; BIT_WORD_SUBWORD; BIT_WORD_BITVAL; BIT_WORD_ZX] in
  let reduce = DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV THENC
    SAIL_HL_X86_REWRITE_CONV[COND_CLAUSES; AND_CLAUSES] in
  fun tm -> match tm with
    | Comb(Comb(Const("bit",_),k),w) when is_numeral k && not (is_var w) ->
        (rewrite THENC reduce) tm
    | _ -> failwith "SAIL_HL_X86_REMS_BIT_CONV";;

let SAIL_HL_X86_REMS_SUBWORD_CONV tm =
  match tm with
  | Comb(Comb(Const("word_subword",_),w),_) when not (is_var w) ->
      WORD_SIMPLE_SUBWORD_CONV tm
  | _ -> failwith "SAIL_HL_X86_REMS_SUBWORD_CONV";;

let SAIL_HL_X86_REMS_IWORD_CONV tm =
  match tm with
  | Comb(Const("iword",_),Comb(Const("int_of_num",_),Comb(Const("val",_),x)))
      when type_of x = type_of tm ->
      (GEN_REWRITE_CONV I [GSYM WORD_IWORD] THENC
       GEN_REWRITE_CONV I [WORD_VAL]) tm
  | _ -> failwith "SAIL_HL_X86_REMS_IWORD_CONV";;

let sail_hl_x86_rems_prefix p s =
  String.length s >= String.length p && String.sub s 0 (String.length p) = p;;

(* Definitions are stored as abstractions; evaluation needs equations
   with every argument applied. Datatype constructors, their recursion
   theorems and the case eliminator's definition are not equations. *)
let sail_hl_x86_rems_equations definitions =
  let applied th =
    let rec go th = match rand(concl th) with
      | Abs(v,_) ->
          let v' = variant (frees(concl th)) v in
          let ap = AP_THM th v' in go (TRANS ap (BETA_CONV (rand(concl ap))))
      | _ -> th in
    GEN_ALL (go th) in
  mapfilter (fun th ->
    let name = fst(dest_const(fst(strip_comb(lhs(concl th))))) in
    if sail_hl_x86_rems_prefix "sail_hl" name &&
       not (sail_hl_x86_rems_prefix "sail_hl_ctor_" name) &&
       not (sail_hl_x86_rems_prefix "sail_hl_type_" name) &&
       not (sail_hl_x86_rems_prefix "sail_hl_case_" name)
    then applied th else failwith "not a model equation") definitions;;

let SAIL_HL_X86_REMS_COMPSET definitions case distinct =
  let cs = Compute.new_compset (map Compute.lazyfy_thm
    [COND_CLAUSES; COND_ID; NOT_CLAUSES; AND_CLAUSES; OR_CLAUSES;
     IMP_CLAUSES; EQ_CLAUSES]) in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  Compute.add_conv (`GABS:(A->bool)->A`, 2, SAIL_HL_X86_REMS_GABS_CONV) cs;
  Compute.add_conv (`(=):A->A->bool`, 2, SAIL_HL_X86_REMS_ENUM_EQ_CONV distinct) cs;
  Compute.add_conv (`dimindex:(A->bool)->num`, 1, DIMINDEX_CONV) cs;
  Compute.add_conv (`bit:num->N word->bool`, 2, SAIL_HL_X86_REMS_BIT_CONV) cs;
  Compute.add_conv
    (`word_subword:M word->num#num->N word`, 2, SAIL_HL_X86_REMS_SUBWORD_CONV) cs;
  Compute.add_conv (`COND:bool->A->A->A`, 3,
    GEN_REWRITE_CONV I [SAIL_HL_X86_REMS_REGISTER_INDEX]) cs;
  Compute.add_conv (`iword:int->N word`, 1, SAIL_HL_X86_REMS_IWORD_CONV) cs;
  num_compute_add_convs cs;
  int_compute_add_convs cs;
  word_compute_add_convs cs;
  Compute.add_thms ([SAIL_HL_X86_REMS_LET; LET_END_DEF; FST; SND; OUTL; OUTR;
    NUM_OF_INT_OF_NUM; case] @ sail_hl_x86_rems_equations definitions) cs;
  cs;;

(* Conditionals stay lazy during evaluation, so a branch chosen by a
   symbolic condition is not yet evaluated. Evaluate both branches of each
   conditional between final states, assuming the condition in one and its
   negation in the other. Then rejoin the two state chains by write: when
   both branches write the same components in the same order, the
   condition moves into the written values. *)
let SAIL_HL_X86_REMS_COND_CONG = prove
 (`!c (a:A) a' b b'. (c ==> a = a') /\ (~c ==> b = b')
     ==> (if c then a else b) = (if c then a' else b')`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* A term takes part in the state computation if it has a type built
   from x86state, a state, a value paired with a state or a continuation
   producing one, or mentions the final state. *)
let sail_hl_x86_rems_stateful u tm =
  let rec has_state ty = ty = `:x86state` ||
    (is_type ty && exists has_state (snd(dest_type ty))) in
  has_state (type_of tm) || free_in u tm;;

(* facts are the conditions assumed by enclosing branches. Evaluation can
   expose a state choice on such a condition again; it is then decided by
   its assumption, not split a second time. Each branch is rewritten only
   with its own new condition. Unchanged subterms are compared with
   compare, which stops at shared subterms. *)
let rec sail_hl_x86_rems_branch_conv cs u facts tm =
  let recurse = sail_hl_x86_rems_branch_conv cs u facts in
  let stateful = sail_hl_x86_rems_stateful u in
  let symbolic_cond t = is_cond t && not (is_const (rand(rator(rator t)))) in
  let decide fact =
    if is_neg (concl fact) then EQF_INTRO fact else EQT_INTRO fact in
  let evaluate facts = Compute.CBV_CONV cs THENC
    SAIL_HL_X86_REWRITE_CONV[] THENC sail_hl_x86_rems_branch_conv cs u facts in
  if not (stateful tm) then REFL tm else
  match tm with
  | Comb(Const(("?" | "!"),_) as q, Abs(v,body)) ->
      AP_TERM q (ABS v (recurse body))
  | Abs(_,_) | Comb(Const("GABS",_),_) ->
      (* Continuations are applied by evaluation once their argument is
         known; their bodies are not split here. *)
      REFL tm
  | Comb(Comb(Comb(Const("COND",_),c),a),b) when not (is_const c) ->
      (match List.find_opt (fun fact -> let p = concl fact in
                aconv p c || (is_neg p && aconv (rand p) c)) facts with
       | Some fact ->
           let th = (RATOR_CONV(RATOR_CONV(RAND_CONV(K (decide fact)))) THENC
                     GEN_REWRITE_CONV I [COND_CLAUSES]) tm in
           TRANS th (evaluate facts (rand(concl th)))
       | None ->
           let branch fact x =
             let assumed = ASSUME fact in
             DISCH fact ((PURE_REWRITE_CONV[decide assumed] THENC
                          evaluate (assumed :: facts)) x) in
           let tha = branch c a and thb = branch (mk_neg c) b in
           MATCH_MP (ISPECL [c;a;rand(concl(UNDISCH tha));b;rand(concl(UNDISCH thb))]
             SAIL_HL_X86_REMS_COND_CONG) (CONJ tha thb))
  | Comb(f,(Comb(Comb(Comb(Const("COND",_),c),a),b) as x))
      when not (is_const c) && stateful x ->
      (* A result chosen by the condition: apply its consumer in each branch. *)
      let th = ISPECL [c;f;a;b] COND_RAND in
      TRANS th (recurse (rand(concl th)))
  | Comb((Comb(Comb(Comb(Const("COND",_),c),f),g)),x) when not (is_const c) ->
      (* A continuation chosen by the condition: apply each to the value. *)
      let th = ISPECL [c;f;g;x] COND_RATOR in
      TRANS th (recurse (rand(concl th)))
  | Comb(f,x) ->
      let th = MK_COMB(recurse f, recurse x) in
      let r = rand(concl th) in
      (match r with
       | Comb(f',x') when compare r tm <> 0 &&
           (symbolic_cond f' || (symbolic_cond x' && stateful x')) ->
           TRANS th (recurse r)
       | _ -> th)
  | _ -> REFL tm;;

let SAIL_HL_X86_REMS_BRANCH_CONV cs u = sail_hl_x86_rems_branch_conv cs u [];;

(* Rejoin the branches of `if c then a else b` where they agree: push the
   condition through applications with the same head and the same number
   of arguments, down to the subterms that differ. Numerals, constants and
   variables are leaves. *)
let SAIL_HL_X86_REMS_COND_APP = prove
 (`!c (f:A->B) g x y.
     (if c then f x else g y) = (if c then f else g) (if c then x else y)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let SAIL_HL_X86_REMS_COND_EQ = prove
 (`!c a b (u:A). (if c then a = u else b = u) <=> (if c then a else b) = u`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let rec SAIL_HL_X86_REMS_MERGE_CONV tm =
  match tm with
  | Comb(Comb(Comb(Const("COND",_),c),a),b) ->
      if compare a b = 0 then ISPECL [c;a] COND_ID else
      let ha,xa = strip_comb a and hb,xb = strip_comb b in
      let literal t = is_numeral t ||
        (is_comb t && is_numeral (rand t) && is_const (rator t)) in
      if literal a || literal b || xa = [] || xb = [] ||
         ha <> hb || length xa <> length xb || is_cond a || is_cond b
      then REFL tm else
      let th = ISPECL [c; rator a; rator b; rand a; rand b] SAIL_HL_X86_REMS_COND_APP in
      let r = rand(concl th) in
      TRANS th (MK_COMB(SAIL_HL_X86_REMS_MERGE_CONV (rator r),
                        SAIL_HL_X86_REMS_MERGE_CONV (rand r)))
  | _ -> REFL tm;;

let SAIL_HL_X86_REMS_JOIN_CONV =
  SAIL_HL_X86_REWRITE_CONV[SAIL_HL_X86_REMS_COND_EQ] THENC
  TOP_DEPTH_CONV (fun tm -> if is_cond tm && type_of tm = `:x86state` then
    CHANGED_CONV SAIL_HL_X86_REMS_MERGE_CONV tm else failwith "not a state choice");;

(* Packed flag writes become Boolean component writes; constant one-bit
   results become their Boolean conditions. *)
let SAIL_HL_X86_REMS_BIT0_CHOICE = prove
 (`(!c x y:1 word. bit 0 (if c then x else y) <=> if c then bit 0 x else bit 0 y) /\
   (bit 0 (word 1:1 word) <=> T) /\ (bit 0 (word 0:1 word) <=> F) /\
   (!p. (if p then T else F) <=> p) /\ (!p. (if p then F else T) <=> ~p)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

let SAIL_HL_X86_REMS_STATE_CONV =
  SAIL_HL_X86_REWRITE_CONV (SAIL_HL_X86_REMS_FLAG_WRITES @
    [SAIL_HL_X86_REMS_BIT0_COND; SAIL_HL_X86_REMS_BIT0_CHOICE; BIT_WORD_BITVAL]);;

let SAIL_HL_X86_REMS_NUM_CONV =
  SAIL_HL_X86_REWRITE_CONV[NUM_OF_INT_OF_NUM] THENC DEPTH_CONV DIMINDEX_CONV THENC
  NUM_REDUCE_CONV THENC INT_REDUCE_CONV THENC
  SAIL_HL_X86_REWRITE_CONV[NUM_OF_INT_OF_NUM] THENC NUM_REDUCE_CONV;;

(* REMS forms raw results with bits_of_int of an integer sum. These are
   the modular word sums at every result width. *)
let SAIL_HL_X86_REMS_UNSIGNED_SUM = prove
 (`!x:N word. !y:N word. !c.
     iword(&(val x) + &(val y) + &(bitval c)):M word =
     word_add (word_add (word_zx x) (word_zx y)) (word(bitval c))`,
  REWRITE_TAC[INT_OF_NUM_ADD; GSYM WORD_IWORD; WORD_ADD; word_zx;
              WORD_ADD_ASSOC]);;

let SAIL_HL_X86_REMS_UNSIGNED_SUM0 = prove
 (`!x:N word. !y:N word.
     iword(&(val x) + &(val y)):M word = word_add (word_zx x) (word_zx y)`,
  REWRITE_TAC[INT_OF_NUM_ADD; GSYM WORD_IWORD; WORD_ADD; word_zx]);;

let SAIL_HL_X86_REMS_SIGNED_SUM = prove
 (`!x:N word. !y:N word. !c.
     iword(ival x + ival y + &(bitval c)):M word =
     word_add (word_add (word_sx x) (word_sx y)) (word(bitval c))`,
  REWRITE_TAC[IWORD_INT_ADD; GSYM WORD_IWORD; word_sx; WORD_ADD_ASSOC]);;

let SAIL_HL_X86_REMS_SIGNED_SUM0 = prove
 (`!x:N word. !y:N word.
     iword(ival x + ival y):M word = word_add (word_sx x) (word_sx y)`,
  REWRITE_TAC[IWORD_INT_ADD; word_sx]);;

let SAIL_HL_X86_REMS_SIGNED_DIFF = prove
 (`!x:N word. !y:N word.
     iword(ival x - ival y):M word = word_sub (word_sx x) (word_sx y)`,
  REWRITE_TAC[IWORD_INT_SUB; word_sx]);;

(* gpr_sub_spec computes CF as unsigned(dst) < unsigned(src). *)
let SAIL_HL_X86_REMS_BORROW = prove
 (`!x y:N word. &(val x):int < &(val y) <=>
                ~(&(val x) - &(val y):int = &(val(word_sub x y)))`,
  REWRITE_TAC[CARRY_WORD_SUB; INT_OF_NUM_LT]);;

(* sub_af_spec tests the sign of the 5-bit nybble difference. *)
let SAIL_HL_X86_REMS_NYBBLE_BORROW = prove
 (`!a b:4 word. ival(iword(&(val a) - &(val b)):5 word) < &0 <=>
                ~(&(val a) - &(val b):int = &(val(word_sub a b)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CARRY_WORD_SUB; GSYM INT_OF_NUM_LT] THEN
  MP_TAC(ISPEC `a:4 word` VAL_BOUND) THEN MP_TAC(ISPEC `b:4 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_4; GSYM INT_OF_NUM_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(INST_TYPE [`:5`,`:N`]
    (SPEC `&(val(a:4 word)) - &(val(b:4 word)):int` IVAL_IWORD)) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  INT_ARITH_TAC);;

(* gpr_sbb_spec first forms the signed sum of src and the incoming carry
   in N+1 bits, which cannot overflow, then subtracts it in N+2 bits. Its
   CF compares dst with the unsigned sum of src and the carry, and its AF
   tests the sign of the integer nybble difference. *)
let SAIL_HL_X86_REMS_SIGNED_CARRY_IN = prove
 (`!y:N word. !c. dimindex(:M) = dimindex(:N) + 1
     ==> ival(iword(ival y + &(bitval c)):M word) = ival y + &(bitval c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
  MP_TAC(ISPEC `y:N word` IVAL_BOUND) THEN MP_TAC(SPEC `c:bool` BITVAL_BOUND) THEN
  ASM_REWRITE_TAC[ADD_SUB] THEN MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN
  SPEC_TAC(`dimindex(:N)`,`n:num`) THEN INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN
  REWRITE_TAC[SUC_SUB1; INT_POW; GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

let SAIL_HL_X86_REMS_SIGNED_BORROW_DIFF = prove
 (`!x:N word. !y:N word. !c.
     iword(ival x - (ival y + &(bitval c))):M word =
     word_sub (word_sub (word_sx x) (word_sx y)) (word(bitval c))`,
  REWRITE_TAC[INT_ARITH `x - (y + z):int = (x - y) - z`] THEN
  REWRITE_TAC[IWORD_INT_SUB; word_sx; GSYM WORD_IWORD]);;

let SAIL_HL_X86_REMS_BORROW_IN = prove
 (`!x y:N word. !c. dimindex(:M) = dimindex(:N) + 1
     ==> (&(val x):int < &(val(iword(&(bitval c) + &(val y)):M word)) <=>
          ~(&(val x) - (&(val y) + &(bitval c)):int =
            &(val(word_sub x (word_add y (word(bitval c)))))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CARRY_WORD_SBB] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; GSYM WORD_IWORD; VAL_WORD; INT_OF_NUM_LT] THEN
  SUBGOAL_THEN `(bitval c + val(y:N word)) MOD 2 EXP dimindex(:M) =
                bitval c + val y` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[EXP_ADD; EXP_1] THEN
    MP_TAC(ISPEC `y:N word` VAL_BOUND) THEN MP_TAC(SPEC `c:bool` BITVAL_BOUND) THEN
    MP_TAC(SPECL [`2`; `dimindex(:N)`] EXP_EQ_0) THEN REWRITE_TAC[ARITH_EQ] THEN
    ARITH_TAC;
    BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC]);;

let SAIL_HL_X86_REMS_NYBBLE_BORROW_IN = prove
 (`!a b:N word. !c. &(val a) - (&(val b) + &(bitval c)):int < &0 <=>
     ~(&(val a) - (&(val b) + &(bitval c)):int =
       &(val(word_sub a (word_add b (word(bitval c))))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CARRY_WORD_SBB] THEN
  BOOL_CASES_TAC `c:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES; INT_ADD_RID; INT_SUB_LT; INT_OF_NUM_LT;
              INT_OF_NUM_ADD] THEN
  ARITH_TAC);;

(* INC and DEC call the same specifications with the constant source 1. *)
let SAIL_HL_X86_REMS_UNSIGNED_INC = prove
 (`!x:N word. iword(&(val x) + &1):M word = word_add (word_zx x) (word 1)`,
  REWRITE_TAC[INT_OF_NUM_ADD; GSYM WORD_IWORD; WORD_ADD; word_zx]);;

let SAIL_HL_X86_REMS_SIGNED_INC = prove
 (`!x:N word. iword(ival x + &1):M word = word_add (word_sx x) (word 1)`,
  REWRITE_TAC[IWORD_INT_ADD; word_sx; GSYM WORD_IWORD]);;

let SAIL_HL_X86_REMS_SIGNED_DEC = prove
 (`!x:N word. iword(ival x - &1):M word = word_sub (word_sx x) (word 1)`,
  REWRITE_TAC[IWORD_INT_SUB; word_sx; GSYM WORD_IWORD]);;

let SAIL_HL_X86_REMS_NYBBLE_DEC = CONV_RULE
  (DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV)
  (GEN `a:4 word` (SPECL [`a:4 word`; `word 1:4 word`]
    SAIL_HL_X86_REMS_NYBBLE_BORROW));;

(* NEG subtracts from the constant 0; its CF compares the 128-bit operand
   with zero. *)
let SAIL_HL_X86_REMS_SIGNED_NEG = prove
 (`!x:N word. iword(&0 - ival x):M word = word_neg (word_sx x)`,
  REWRITE_TAC[INT_SUB_LZERO; IWORD_INT_NEG; word_sx]);;

let SAIL_HL_X86_REMS_NYBBLE_NEG = prove
 (`!a:4 word. ival(iword(&0 - &(val a)):5 word) < &0 <=>
              ~(-- &(val a):int = &(val(word_neg a)))`,
  GEN_TAC THEN
  MP_TAC(SPECL [`word 0:4 word`; `a:4 word`] SAIL_HL_X86_REMS_NYBBLE_BORROW) THEN
  REWRITE_TAC[VAL_WORD_0; INT_SUB_LZERO; WORD_SUB_LZERO]);;

let SAIL_HL_X86_REMS_ZX_ZERO = prove
 (`!x:N word. dimindex(:N) <= dimindex(:M)
     ==> ((word_zx x:M word = word 0 <=> x = word 0) /\
          (word 0 = word_zx x:M word <=> x = word 0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; VAL_WORD_ZX_GEN] THEN
  SUBGOAL_THEN `val(x:N word) MOD 2 EXP dimindex(:M) = val x` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `x:N word` VAL_BOUND) THEN
    MP_TAC(SPECL [`2`; `dimindex(:N)`; `dimindex(:M)`] LE_EXP) THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC;
    ARITH_TAC]);;

(* mul_spec and imul_spec form the double-width product with bits_of_int
   and slice its halves. *)
let SAIL_HL_X86_REMS_UNSIGNED_PRODUCT = prove
 (`!x:N word. !y:P word. iword(&(val x) * &(val y)):M word = word(val x * val y)`,
  REWRITE_TAC[INT_OF_NUM_MUL; GSYM WORD_IWORD]);;

(* A product of two signed N-bit values fits in 2N bits; imul_spec's
   overflow test asks whether the low half alone already has its value. *)
let SAIL_HL_X86_REMS_SIGNED_PRODUCT = prove
 (`!x:N word. !y:N word. dimindex(:M) = 2 * dimindex(:N)
     ==> ival(iword(ival x * ival y):M word) = ival x * ival y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `x:N word` IVAL_BOUND) THEN MP_TAC(ISPEC `y:N word` IVAL_BOUND) THEN
  MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN
  SPEC_TAC(`ival(x:N word)`,`a:int`) THEN SPEC_TAC(`ival(y:N word)`,`b:int`) THEN
  SPEC_TAC(`dimindex(:N)`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[ARITH; SUC_SUB1; ARITH_RULE `2 * SUC n - 1 = (n + n) + 1`;
    INT_POW_ADD; INT_POW_1] THEN
  REPEAT GEN_TAC THEN MP_TAC(ISPECL [`&2:int`; `n:num`] INT_POW_LT) THEN
  CONV_TAC INT_REDUCE_CONV THEN SPEC_TAC(`(&2:int) pow n`,`p:int`) THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`abs a:int`; `p:int`; `abs b:int`; `p:int`] INT_LE_MUL2) THEN
  REWRITE_TAC[INT_ABS_POS; GSYM INT_ABS_MUL] THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:int`; `p:int`] INT_LT_MUL) THEN ASM_REWRITE_TAC[] THEN
  ASM_INT_ARITH_TAC);;

let SAIL_HL_X86_REMS_SIGNED_PRODUCT_FIT = prove
 (`!x:N word. !y:N word. dimindex(:M) = 2 * dimindex(:N)
     ==> ((word_sx (word_zx (iword(ival x * ival y):M word):N word):M word =
           iword(ival x * ival y)) <=>
          (ival x * ival y = ival(word_zx (iword(ival x * ival y):M word):N word)))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM IVAL_EQ] THEN
  W(fun (_,w) -> MP_TAC(PART_MATCH (lhand o rand) IVAL_WORD_SX (lhand(lhand w)))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[SAIL_HL_X86_REMS_SIGNED_PRODUCT] THEN MESON_TAC[]);;

(* The low half of the signed product is the truncated product. *)
let SAIL_HL_X86_REMS_IWORD_NARROW = prove
 (`!z. dimindex(:N) <= dimindex(:M) ==> word_zx (iword z:M word):N word = iword z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_zx; WORD_IWORD; IWORD_EQ] THEN
  MP_TAC(ISPEC `iword z:M word` VAL_IVAL) THEN
  MP_TAC(ISPEC `z:int` (INST_TYPE [`:M`,`:N`] IVAL_IWORD_CONG)) THEN
  ABBREV_TAC `p = dimindex(:M) - dimindex(:N)` THEN
  SUBGOAL_THEN `dimindex(:M) = dimindex(:N) + p` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_POW_ADD] THEN
  SPEC_TAC(`ival(iword z:M word)`,`a:int`) THEN
  SPEC_TAC(`&(val(iword z:M word)):int`,`b:int`) THEN
  SPEC_TAC(`&(bitval (bit ((dimindex (:N) + p) - 1) (iword z:M word))):int`,`c:int`) THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGER_RULE);;

let SAIL_HL_X86_REMS_TRUNCATED_PRODUCT = prove
 (`!x y:N word. dimindex(:N) <= dimindex(:M)
     ==> word_zx (iword(ival x * ival y):M word):N word = word_mul x y`,
  SIMP_TAC[SAIL_HL_X86_REMS_IWORD_NARROW; IWORD_INT_MUL; IWORD_IVAL]);;

let SAIL_HL_X86_REMS_SUMS =
  [SAIL_HL_X86_REMS_UNSIGNED_PRODUCT; SAIL_HL_X86_REMS_SIGNED_NEG; SAIL_HL_X86_REMS_NYBBLE_NEG;
   SAIL_HL_X86_REMS_UNSIGNED_INC; SAIL_HL_X86_REMS_SIGNED_INC;
   SAIL_HL_X86_REMS_SIGNED_DEC; SAIL_HL_X86_REMS_NYBBLE_DEC;
   SAIL_HL_X86_REMS_UNSIGNED_SUM; SAIL_HL_X86_REMS_UNSIGNED_SUM0;
   SAIL_HL_X86_REMS_SIGNED_SUM; SAIL_HL_X86_REMS_SIGNED_SUM0;
   SAIL_HL_X86_REMS_SIGNED_DIFF; SAIL_HL_X86_REMS_BORROW;
   SAIL_HL_X86_REMS_NYBBLE_BORROW; SAIL_HL_X86_REMS_SIGNED_BORROW_DIFF;
   SAIL_HL_X86_REMS_NYBBLE_BORROW_IN];;

(* cf_spec: unsigned_byte_p(N, unsigned(raw)) for an (N+1)-bit raw result
   is the clear top bit. *)
let SAIL_HL_X86_REMS_UNSIGNED_FITS = prove
 (`!z:M word. dimindex(:M) = dimindex(:N) + 1
     ==> (&(val z):int < &(2 EXP dimindex(:N)) <=> ~bit (dimindex(:N)) z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_OF_NUM_LT] THEN
  MP_TAC(ISPEC `z:M word` MSB_VAL) THEN ASM_REWRITE_TAC[ADD_SUB] THEN
  DISCH_THEN SUBST1_TAC THEN ARITH_TAC);;

(* of_spec: signed_byte_p(N, signed(raw)) holds exactly when the low N
   bits of raw already have its signed value. *)
let SAIL_HL_X86_REMS_IVAL_NARROW = prove
 (`!z:M word. dimindex(:N) <= dimindex(:M) /\
     --(&2 pow (dimindex(:N) - 1)) <= ival z /\
     ival z < &2 pow (dimindex(:N) - 1)
     ==> ival(word_zx z:N word) = ival z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_zx (z:M word):N word = iword(ival(z:M word))`
   SUBST1_TAC THENL
   [REWRITE_TAC[word_zx; WORD_IWORD; IWORD_EQ] THEN
    MP_TAC(ISPEC `z:M word` VAL_IVAL) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP
      (ARITH_RULE `n <= m ==> m = n + (m - n)`)) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC
      (LAND_CONV o RAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[INT_POW_ADD] THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC INTEGER_RULE;
    MATCH_MP_TAC IVAL_IWORD THEN ASM_REWRITE_TAC[]]);;

let SAIL_HL_X86_REMS_SIGNED_NARROW = prove
 (`!z:M word. dimindex(:N) <= dimindex(:M)
     ==> ((--(&2 pow (dimindex(:N) - 1)) <= ival z /\
           ival z < &2 pow (dimindex(:N) - 1)) <=>
          ival(word_zx z:N word) = ival z)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC SAIL_HL_X86_REMS_IVAL_NARROW THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IVAL_BOUND]]);;

let SAIL_HL_X86_REMS_MOD_ADD_LEFT = prove
 (`!a b n. (a MOD n + b) MOD n = (a + b) MOD n`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM MOD_ADD_MOD] THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN REWRITE_TAC[MOD_ADD_MOD]);;

let SAIL_HL_X86_REMS_MOD_SELF = prove
 (`!a n. ~(n = 0) ==> (a = a MOD n <=> a < n)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [ONCE_ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[MOD_LT_EQ];
    ASM_SIMP_TAC[MOD_LT]]);;

(* add_af_spec and adc_af_spec add the low nybbles in a 5- or 6-bit word
   and test the result against 15. *)
let SAIL_HL_X86_REMS_NYBBLE_CARRY m =
  let tm = inst [mk_finty(num m),`:M`]
   `!a b:4 word. !c.
      &15:int < &(val(word_add (word_add (word_zx a:M word) (word_zx b))
                               (word(bitval c)))) <=>
      ~(val a + val b + bitval c =
        val(word_add (word_add a b) (word(bitval c))))` in
  prove(tm,
   REPEAT GEN_TAC THEN
   REWRITE_TAC[INT_OF_NUM_LT; VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD_BITVAL] THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
   MP_TAC(ISPEC `a:4 word` VAL_BOUND) THEN MP_TAC(ISPEC `b:4 word` VAL_BOUND) THEN
   MP_TAC(SPEC `c:bool` BITVAL_BOUND) THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
   SPEC_TAC(`val(a:4 word)`,`p:num`) THEN SPEC_TAC(`val(b:4 word)`,`q:num`) THEN
   SPEC_TAC(`bitval c`,`k:num`) THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `p < 32 /\ q < 32 /\ p + q < 32 /\ p + q + k < 32 /\
                 p < 64 /\ q < 64 /\ p + q < 64 /\ p + q + k < 64`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[MOD_LT] THEN
   REWRITE_TAC[SAIL_HL_X86_REMS_MOD_ADD_LEFT; GSYM ADD_ASSOC] THEN
   ASM_SIMP_TAC[MOD_LT] THEN
   SIMP_TAC[SAIL_HL_X86_REMS_MOD_SELF; ARITH_EQ] THEN ASM_ARITH_TAC);;

let SAIL_HL_X86_REMS_ZX_ZX = prove
 (`!x:N word. dimindex(:N) <= dimindex(:M)
     ==> word_zx (word_zx x:M word):N word = x`,
  SIMP_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL]);;

(* The bodies widen operands to 128 bits, operate, and truncate. These
   facts remove a widening followed by a narrowing to the original width. *)
let SAIL_HL_X86_REMS_ZX_LOGIC = prove
 (`(!x:N word. dimindex(:N) <= dimindex(:M)
      ==> word_zx (word_not (word_zx x:M word)):N word = word_not x) /\
   (!x y:N word. dimindex(:N) <= dimindex(:M)
      ==> word_zx (word_and (word_zx x:M word) (word_zx y)):N word = word_and x y) /\
   (!x y:N word. dimindex(:N) <= dimindex(:M)
      ==> word_zx (word_or (word_zx x:M word) (word_zx y)):N word = word_or x y) /\
   (!x y:N word. dimindex(:N) <= dimindex(:M)
      ==> word_zx (word_xor (word_zx x:M word) (word_zx y)):N word = word_xor x y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[BIT_WORD_ZX; BIT_WORD_NOT; BIT_WORD_AND; BIT_WORD_OR;
                  BIT_WORD_XOR] THEN
  SUBGOAL_THEN `i < dimindex(:M)` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

let SAIL_HL_X86_REMS_ZX_NARROW = prove
 (`!x:P word. dimindex(:N) <= dimindex(:M)
     ==> word_zx (word_zx x:M word):N word = word_zx x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

let SAIL_HL_X86_REMS_ZX_SX_NARROW = prove
 (`!x:P word. dimindex(:N) <= dimindex(:P) /\ dimindex(:P) <= dimindex(:M)
     ==> word_zx (word_sx x:M word):N word = word_zx x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[BIT_WORD_ZX; BIT_WORD_SX] THEN
  SUBGOAL_THEN `i < dimindex(:M) /\ i < dimindex(:P) /\
                MIN i (dimindex(:P) - 1) = i` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

(* The low part of a byte slice, as in the nybble of a legacy high byte. *)
let SAIL_HL_X86_REMS_ZX_SUBWORD = prove
 (`!x:N word. !p k. k = dimindex(:M) /\ dimindex(:P) <= k
     ==> word_zx (word_subword x (p,k):M word):P word =
         word_subword x (p,dimindex(:P))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[BIT_WORD_ZX; BIT_WORD_SUBWORD; MIN; LE_REFL] THEN
  SUBGOAL_THEN `i < dimindex(:M)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(* A product half: the slice is the shifted product truncated to the
   half's width. Only products are rewritten this way. *)
let SAIL_HL_X86_REMS_PRODUCT_HALF = prove
 (`!z:M word. !k n. n = dimindex(:N)
     ==> word_subword z (k,n):N word = word_zx (word_ushr z k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[BIT_WORD_ZX; BIT_WORD_SUBWORD; BIT_WORD_USHR; MIN; LE_REFL] THEN
  REWRITE_TAC[ADD_SYM]);;

(* Apply a width-conditional rewrite once its width condition reduces to
   true. A term net selects the rules whose left-hand side can match, as
   for an ordinary rewrite, and they are tried in their listed order;
   these conversions run at every subterm. *)
let sail_hl_x86_rems_conditional_conv rules =
  let pattern rule = if is_imp(snd(strip_forall(concl rule)))
                     then lhand o rand else lhs in
  let net = itlist (fun (index,rule) -> enter []
    (pattern rule (snd(strip_forall(concl rule))),
     (index, PART_MATCH (pattern rule) rule)))
    (zip (0--(length rules - 1)) rules) empty_net in
  fun tm ->
  let candidates = sort (fun (i,_) (j,_) -> i < j) (lookup tm net) in
  let th = tryfind (fun (_,part) -> part tm) candidates in
  if not (is_imp (concl th)) then th else
  CONV_RULE (RAND_CONV (DEPTH_CONV DIMINDEX_CONV)) (MP th (EQT_ELIM
    ((DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV THENC SAIL_HL_X86_REWRITE_CONV[])
     (lhand (concl th)))));;

let SAIL_HL_X86_REMS_NARROW_CONV =
  let zero = UNDISCH (SPEC_ALL SAIL_HL_X86_REMS_ZX_ZERO) in
  sail_hl_x86_rems_conditional_conv
   (SAIL_HL_X86_REMS_ZX_ZX :: SAIL_HL_X86_REMS_ZX_NARROW ::
    SAIL_HL_X86_REMS_ZX_SX_NARROW :: SAIL_HL_X86_REMS_ZX_SUBWORD ::
    CONJUNCTS SAIL_HL_X86_REMS_ZX_LOGIC @
    map (fun th -> GEN_ALL (DISCH_ALL th)) [CONJUNCT1 zero; CONJUNCT2 zero]);;

let SAIL_HL_X86_REMS_PRODUCT_CONV =
  let rule = sail_hl_x86_rems_conditional_conv [SAIL_HL_X86_REMS_PRODUCT_HALF] in
  fun tm -> match tm with
    | Comb(Comb(Const("word_subword",_),z),_)
        when (match z with
              | Comb(Const("word",_),Comb(Comb(Const("*",_),_),_)) -> true
              | Comb(Const("iword",_),Comb(Comb(Const("int_mul",_),_),_)) -> true
              | _ -> false) -> rule tm
    | _ -> failwith "SAIL_HL_X86_REMS_PRODUCT_CONV";;

(* Truncation distributes over the operations computing a result. The
   claims use this to compare the low bytes and nybbles that the two
   models extract from results of different widths. *)
let SAIL_HL_X86_REMS_LOW_CONV =
  sail_hl_x86_rems_conditional_conv
   [WORD_ZX_ADD; WORD_ZX_SUB; WORD_ZX_NEG; WORD_ZX_NOT; WORD_ZX_AND;
    WORD_ZX_OR; WORD_ZX_XOR];;

let sail_hl_x86_rems_reduce = CONV_RULE
  (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV THENC INT_REDUCE_CONV);;

let sail_hl_x86_rems_at types theorem =
  let th = sail_hl_x86_rems_reduce (SPEC_ALL (INST_TYPE types theorem)) in
  GEN_ALL (if is_imp (concl th) then MP th (EQT_ELIM
             ((DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) (lhand (concl th))))
           else th);;

(* Specialize an incoming carry to false, as for ADD beside ADC and SUB
   beside SBB. *)
let sail_hl_x86_rems_no_carry theorem =
  let th = SPEC_ALL theorem in
  let c = find (fun v -> type_of v = bool_ty) (frees (concl th)) in
  GEN_ALL (REWRITE_RULE[BITVAL_CLAUSES; ADD_CLAUSES; INT_ADD_RID; WORD_ADD_0;
                        WORD_SUB_0] (INST [`F`,c] th));;

(* REMS's integer tests on an (N+1)-bit raw result as the shina bit forms,
   the shina facts giving s2n-bignum's flags, and the narrowing rewrites
   that recover the N-bit result and its low nybble, for one width N. *)
let SAIL_HL_X86_REMS_FACTS width =
  let n = mk_finty(num width) and w = mk_finty(num(width + 1)) in
  let half = string_of_num (power_num (num 2) (num (width - 1))) in
  let unsigned_fits =
    sail_hl_x86_rems_at [w,`:M`; n,`:N`] SAIL_HL_X86_REMS_UNSIGNED_FITS in
  let narrow =
    sail_hl_x86_rems_at [w,`:M`; n,`:N`] SAIL_HL_X86_REMS_SIGNED_NARROW in
  let wide_overflow =
    let sx = sail_hl_x86_rems_reduce (INST_TYPE [n,`:M`; w,`:N`] IVAL_WORD_SX) in
    prove(parse_term(Printf.sprintf
      "!z:%d word. (bit %d z <=> bit %d z) <=> ival(word_zx z:%d word) = ival z"
      (width + 1) width (width - 1) width),
     GEN_TAC THEN GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM sx] THEN
     REWRITE_TAC[IVAL_EQ] THEN BITBLAST_TAC) in
  let signed_fits = prove(parse_term(Printf.sprintf
      "!z:%d word. (if --(&%s) <= ival z then ival z < &%s else F) <=>
                   (bit %d z <=> bit %d z)"
      (width + 1) half half width (width - 1)),
     GEN_TAC THEN REWRITE_TAC[TAUT `(if p then q else F) <=> p /\ q`] THEN
     REWRITE_TAC[wide_overflow; GSYM narrow] THEN
     CONV_TAC(DEPTH_CONV INT_REDUCE_CONV) THEN REWRITE_TAC[]) in
  let v = mk_finty(num(width + 2)) in
  let carry_in = map (sail_hl_x86_rems_at [w,`:M`; n,`:N`])
    [SAIL_HL_X86_REMS_SIGNED_CARRY_IN; SAIL_HL_X86_REMS_BORROW_IN] in
  let sign_at extra =
    let sign = sail_hl_x86_rems_reduce (INST_TYPE [n,`:N`] MSB_IVAL) in
    prove(parse_term(Printf.sprintf
      "!z:%d word. bit %d z <=> ival(word_zx z:%d word) < &0"
      (width + extra) (width - 1) width),
     GEN_TAC THEN REWRITE_TAC[GSYM sign; BIT_WORD_ZX] THEN
     CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV) in
  let low op source target = sail_hl_x86_rems_at [source,`:M`; target,`:N`] op in
  let sx_low extra = prove(parse_term(Printf.sprintf
      "!x:%d word. word_zx(word_sx x:%d word):%d word = x"
      width (width + extra) width), BITBLAST_TAC) in
  (* SBB's N+2-bit difference: its overflow test reads the low N+1 bits. *)
  let wide_sx = prove(parse_term(Printf.sprintf
      "!x:%d word. word_zx(word_sx x:%d word):%d word = word_sx x"
      width (width + 2) (width + 1)), BITBLAST_TAC) in
  let shina = SAIL_HL_X86_GPR_FLAG_REWRITES width @
    SAIL_HL_X86_GPR_SUB_REWRITES width in
  let shina_overflow op = find (fun th ->
    can (term_match [] (mk_neg(mk_iff(
      mk_comb(mk_comb(`bit:num->M word->bool`, `k:num`),
        list_mk_comb(op, [list_mk_comb(op, [`word_sx (x:N word):M word`;
                                             `word_sx (y:N word):M word`]);
                          `word(bitval c):M word`])),
      `b:bool`))))
      (lhand (snd (strip_forall (concl th))))) shina in
  let carry_overflow = shina_overflow `word_add:M word->M word->M word`
  and borrow_overflow = shina_overflow `word_sub:M word->M word->M word` in
  (* INC and DEC: the same facts with the source operand the constant 1. *)
  let reduce = CONV_RULE (DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) in
  let overflows = map sail_hl_x86_rems_no_carry [carry_overflow; borrow_overflow] in
  let one th =
    let x = mk_var("x",mk_type("word",[n])) in
    let th = SPEC_ALL th in
    let y = find (fun v -> v <> x && type_of v = type_of x) (frees(concl th)) in
    GEN x (reduce (INST [inst [n,`:N`] `word 1:N word`, y] th)) in
  (* NEG: the subtraction facts with the constant 0 as the first operand. *)
  let neg_overflow =
    let y = mk_var("y",mk_type("word",[n])) in
    let th = SPECL [inst [n,`:N`] `word 0:N word`; y] (el 1 overflows) in
    GEN y (REWRITE_RULE[WORD_SUB_LZERO; INT_SUB_LZERO] (reduce th)) in
  let carries = map SAIL_HL_X86_REMS_NYBBLE_CARRY [5;6] in
  let nybble_one = map (fun th -> GEN `a:4 word` (reduce (SPECL
    [`a:4 word`; `word 1:4 word`] (sail_hl_x86_rems_no_carry th)))) carries in
  let nybble = carries @ map sail_hl_x86_rems_no_carry carries @ nybble_one @
    [SAIL_HL_X86_LOW_SUBWORD `:4`; SAIL_HL_X86_LOW_ADD n `:4`;
     SAIL_HL_X86_LOW_SUB n `:4`; low WORD_ZX_NEG n `:4`] in
  [unsigned_fits; signed_fits; low WORD_ZX_SUB v w; wide_sx; WORD_ZX_BITVAL] @
  carry_in,
  shina @ overflows @ map one overflows @ [neg_overflow],
  let double = mk_finty(num(2 * width)) in
  let products = map (sail_hl_x86_rems_at [n,`:N`; double,`:M`])
    [SAIL_HL_X86_REMS_SIGNED_PRODUCT_FIT] in
  products @
  [sign_at 1; sign_at 2; low WORD_ZX_ADD w n; low WORD_ZX_SUB w n;
   low WORD_ZX_NEG w n;
   low WORD_ZX_SUB v n; sx_low 1; sx_low 2; WORD_ZX_BITVAL; VAL_WORD_BITVAL;
   WORD_ZX_TRIVIAL;
   WORD_RULE `word_sub (word_sub x y) z:N word = word_sub x (word_add y z)`] @
  nybble;;

(* Two-operand IMUL keeps only the low half of the product; s2n-bignum
   states it as word_mul. One-operand IMUL keeps both halves, so its
   facts must leave the product whole. *)
let SAIL_HL_X86_REMS_TRUNCATED_FACTS width (unsigned, shina, narrowing) =
  let n = mk_finty(num width) and double = mk_finty(num(2 * width)) in
  unsigned, shina,
  sail_hl_x86_rems_at [n,`:N`; double,`:M`] SAIL_HL_X86_REMS_TRUNCATED_PRODUCT ::
  narrowing;;

(* REMS computes PF from logcount of the low result byte, which evaluation
   unrolls into a bounded recursion. Prove that circuit equal to
   word_evenparity once for all 256 bytes, then reuse it at every width. *)
let SAIL_HL_X86_REMS_BYTE_CASES = prove
 (`!P. (!b:byte. P b) <=> (!n. n < 256 ==> P (word n:byte))`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `b:byte` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `val(b:byte)`) THEN
  REWRITE_TAC[WORD_VAL] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let sail_hl_x86_rems_parity = ref ([]:(term*thm) list);;

let SAIL_HL_X86_REMS_PARITY_CONV cs tm =
  let bytes = setify (map rand (find_terms (fun t ->
    try fst(dest_const(rator t)) = "val" && type_of (rand t) = `:byte`
    with Failure _ -> false) tm)) in
  if length bytes <> 1 then failwith "PF needs exactly one byte";
  let byte = hd bytes in
  let b = genvar `:byte` in
  let circuit = subst [b,byte] tm in
  if free_in byte circuit then failwith "PF depends on more than one byte";
  let lemma =
    try snd(find (fun (t,_) -> aconv t (mk_abs(b,circuit))) !sail_hl_x86_rems_parity)
    with Failure _ ->
      let th = prove(mk_forall(b, mk_iff(circuit, mk_comb(`word_evenparity:byte->bool`, b))),
        REWRITE_TAC[SAIL_HL_X86_REMS_BYTE_CASES] THEN CONV_TAC EXPAND_CASES_CONV THEN
        CONV_TAC(Compute.CBV_CONV cs) THEN NO_TAC) in
      sail_hl_x86_rems_parity :=
        (mk_abs(b,circuit), th) :: !sail_hl_x86_rems_parity;
      th in
  SPEC byte lemma;;

(* Lift a choice that does not depend on a byte value, such as a legacy
   operand's register selection, out of a parity circuit:
   P[if c then a else b] = if c then P[a] else P[b]. *)
let SAIL_HL_X86_REMS_LIFT_CHOICE_CONV tm =
  let byte_value t =
    try fst(dest_const(rator t)) = "val" && type_of(rand t) = `:byte`
    with Failure _ -> false in
  let outer = frees tm in
  (* A condition on a variable bound inside the circuit is part of it. *)
  let choice t =
    is_cond t && subset (frees t) outer &&
    not(can (find_term byte_value) (rand(rator(rator t)))) in
  let c = find_term choice tm in
  if c = tm then failwith "SAIL_HL_X86_REMS_LIFT_CHOICE_CONV" else
  let x = genvar (type_of c) in
  let body = subst [x,c] tm in
  if not(vfree_in x body) then failwith "SAIL_HL_X86_REMS_LIFT_CHOICE_CONV" else
  let p = mk_abs(x, body) in
  let condition,(a,b) = dest_cond c in
  CONV_RULE (LAND_CONV BETA_CONV THENC
             RAND_CONV (RATOR_CONV(RAND_CONV BETA_CONV) THENC
                        RAND_CONV BETA_CONV))
    (ISPECL [condition; p; a; b] COND_RAND);;

(* Rewrite each value written to PF that is a circuit on one byte. A
   legacy byte form chooses between such circuits on different bytes. *)
let SAIL_HL_X86_REMS_PF_CONV cs =
  let pf = `rflags :> bitelement 2` in
  let rec value tm =
    try SAIL_HL_X86_REMS_PARITY_CONV cs tm with Failure _ ->
      if is_cond tm then
        (RATOR_CONV(RAND_CONV value) THENC RAND_CONV value) tm
      else try (match tm with
        | Comb(f,x) -> AP_TERM f (value x)
        | _ -> failwith "not a parity circuit")
      with Failure _ -> (SAIL_HL_X86_REMS_LIFT_CHOICE_CONV THENC value) tm in
  ONCE_DEPTH_CONV (fun tm ->
    match tm with
    | Comb(Comb(Comb(Const("write",_) as w,c),v),rest) when c = pf ->
        AP_THM (AP_TERM (mk_comb(w,c)) (value v)) rest
    | _ -> failwith "not a PF write");;

(* REMS's undef_flg takes one bit of a nonnegative unknown integer. That
   choice admits both Boolean values, and each call has its own unknown. *)
let SAIL_HL_X86_REMS_UNDEFINED_BIT = prove
 (`!P. (?v:int. if &0 <= v then P (bit 0 (iword v:1 word)) else F) <=> (?b. P b)`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `v:int` MP_TAC) THEN COND_CASES_TAC THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `bit 0 (iword v:1 word)` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `b:bool`) THEN EXISTS_TAC `&(bitval b):int` THEN
    REWRITE_TAC[INT_POS; GSYM WORD_IWORD; BIT_WORD_BITVAL] THEN
    ASM_REWRITE_TAC[]]);;

let SAIL_HL_X86_REMS_UNDEFINED_CONV tm =
  match tm with
  | Comb(Const("?",_),Abs(v,Comb(Comb(Comb(Const("COND",_),
      Comb(Comb(Const("int_le",_),zero),v')),body),f)))
      when v = v' && zero = `&0:int` && f = `F` ->
      let x = mk_comb(`bit 0:1 word->bool`, mk_comb(`iword:int->1 word`, v)) in
      let b = variant (frees tm) (mk_var("b",bool_ty)) in
      let p = subst [b,x] body in
      if free_in v p then failwith "unknown integer used beyond one bit";
      let th = CONV_RULE (DEPTH_CONV BETA_CONV)
        (ISPEC (mk_abs(b,p)) SAIL_HL_X86_REMS_UNDEFINED_BIT) in
      TRANS (ALPHA tm (lhs(concl th))) th
  | _ -> failwith "SAIL_HL_X86_REMS_UNDEFINED_CONV";;

(* Each branch of a REMS body chooses its own undefined values. Move every
   unknown to the branch that uses it, eliminate it there, and then share
   the resulting Boolean choices between the two branches again. *)
let SAIL_HL_X86_REMS_EXISTS_COND = prove
 (`(!c P Q. (?v:int. if c then P v else Q v) <=>
            if c then (?v. P v) else (?v. Q v)) /\
   (!c P Q. (if c then (?b:bool. P b) else (?b. Q b)) <=>
            (?b. if c then P b else Q b))`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* After an inner unknown has become a Boolean choice, an outer unknown's
   guard can sit below that choice: ?v b. if &0 <= v then P else F. *)
let SAIL_HL_X86_REMS_UNKNOWN_INWARD_CONV tm =
  match tm with
  | Comb(Const("?",_),Abs(v,Comb(Const("?",_),Abs(b,_))))
      when type_of v = `:int` && type_of b = bool_ty ->
      GEN_REWRITE_CONV I [SWAP_EXISTS_THM] tm
  | _ -> failwith "SAIL_HL_X86_REMS_UNKNOWN_INWARD_CONV";;

let SAIL_HL_X86_REMS_UNDEFINED_VALUES_CONV =
  SAIL_HL_X86_REWRITE_CONV[CONJUNCT1 SAIL_HL_X86_REMS_EXISTS_COND] THENC
  TOP_DEPTH_CONV (SAIL_HL_X86_REMS_UNDEFINED_CONV ORELSEC
                  SAIL_HL_X86_REMS_UNKNOWN_INWARD_CONV) THENC
  SAIL_HL_X86_REWRITE_CONV[CONJUNCT2 SAIL_HL_X86_REMS_EXISTS_COND] THENC
  SAIL_HL_X86_REMS_JOIN_CONV;;

(* Normalize an applied REMS root `R s u` to writes to s, possibly under
   existentially chosen undefined flags, with s2n-bignum's flag
   expressions. *)
let SAIL_HL_X86_REMS_NORMALIZE cs (unsigned, shina, narrowing) root =
  let flags =
    SAIL_HL_X86_REWRITE_CONV (SAIL_HL_X86_REMS_FLAG_READS @
      [VAL_WORD_BITVAL; WORD_ZX_BITVAL; BIT_WORD_BITVAL]) THENC
    SAIL_HL_X86_REMS_NUM_CONV THENC
    SAIL_HL_X86_REWRITE_CONV (BIT_WORD_SUBWORD :: SAIL_HL_X86_REMS_SUMS @ unsigned) THENC
    SAIL_HL_X86_REMS_NUM_CONV THENC
    TOP_DEPTH_CONV SAIL_HL_X86_REMS_NARROW_CONV THENC
    SAIL_HL_X86_REWRITE_CONV (NOT_CLAUSES :: shina) THENC
    SAIL_HL_X86_REWRITE_CONV narrowing THENC
    TOP_DEPTH_CONV (SAIL_HL_X86_REMS_NARROW_CONV ORELSEC
                    SAIL_HL_X86_REMS_PRODUCT_CONV ORELSEC
                    GEN_REWRITE_CONV I [WORD_USHR_ZERO]) THENC
    SAIL_HL_X86_REWRITE_CONV (INT_OF_NUM_EQ :: WORD_USHR_ZERO :: narrowing) THENC
    DEPTH_CONV WORD_RED_CONV THENC
    TOP_DEPTH_CONV SAIL_HL_X86_REMS_KEEP_CONV THENC
    SAIL_HL_X86_REMS_PF_CONV cs THENC
    SAIL_HL_X86_REWRITE_CONV[SAIL_HL_X86_REMS_BIT0_CHOICE;
                 GSYM CF; GSYM PF; GSYM AF; GSYM ZF; GSYM SF; GSYM OF] in
  let th = Compute.CBV_CONV cs root in
  let th = CONV_RULE (RAND_CONV (SAIL_HL_X86_REWRITE_CONV[] THENC
    SAIL_HL_X86_REMS_BRANCH_CONV cs (rand root) THENC
    SAIL_HL_X86_REMS_JOIN_CONV)) th in
  CONV_RULE (RAND_CONV (SAIL_HL_X86_REMS_STATE_CONV THENC
    SAIL_HL_X86_REMS_UNDEFINED_VALUES_CONV THENC flags)) th;;

(* Move the final-state existential inside the undefined-value
   existentials, where it can be eliminated. *)
let rec SAIL_HL_X86_REMS_PUSH_EXISTS_CONV tm =
  (GEN_REWRITE_CONV I [SWAP_EXISTS_THM] THENC
   BINDER_CONV (TRY_CONV SAIL_HL_X86_REMS_PUSH_EXISTS_CONV)) tm;;

(* Compare a normalized REMS root with an s2n-bignum instruction under
   the core observation. Both sides become `?ys. t = X ys`: the same state
   writes, ordered by component, and the same undefined choices. *)
(* Order the undefined choices of `?x1 .. xn. body` by their first use in
   body. After the state writes are ordered, both relations then name the
   same choice in the same position. *)
let SAIL_HL_X86_REMS_EXISTS_ORDER_CONV tm =
  let vs, body = strip_exists tm in
  if length vs < 2 then failwith "SAIL_HL_X86_REMS_EXISTS_ORDER_CONV" else
  let rec uses acc t =
    if mem t vs then (if mem t acc then acc else t :: acc) else
    match t with
    | Comb(f,x) -> uses (uses acc f) x
    | Abs(_,b) -> uses acc b
    | _ -> acc in
  let order = rev (uses [] body) in
  let order = order @ subtract vs order in
  if order = vs then failwith "already ordered" else
  let tm' = list_mk_exists(order, body) in
  let intro vars =
    itlist (fun v th -> EXISTS (mk_exists(v, concl th), v) th) vars (ASSUME body) in
  let rec elim ex vars th = match vars with
    | [] -> th
    | v::rest -> CHOOSE (v, ASSUME ex) (elim (snd(dest_exists ex)) rest th) in
  IMP_ANTISYM_RULE (DISCH tm (elim tm vs (intro order)))
                   (DISCH tm' (elim tm' order (intro vs)));;

(* Two relations may assemble the same register value from different
   slices, as when s2n-bignum writes AH and AL separately where REMS writes
   AX. Prove such a value equation by bit-blasting, keeping every operand
   that is not a slice, join, extension or bitwise operation opaque. *)
let SAIL_HL_X86_REMS_WORD_EQ_GEN_RULE fine tm =
  let structural = ["word_join"; "word_subword"; "word_zx"; "word_sx";
                    "word_and"; "word_or"; "word_xor"; "word_not"] in
  let literal_slice args = match args with
    | [_; p] -> (try let a,b = dest_pair p in is_numeral a && is_numeral b
                 with Failure _ -> false)
    | _ -> true in
  let rec atoms acc t =
    let h,args = strip_comb t in
    match h with
    | Const(name,_) when mem name structural &&
        (name <> "word_subword" || literal_slice args) ->
        itlist (fun a acc -> if is_type (type_of a) && fst(dest_type(type_of a)) = "word"
                             then atoms acc a else acc) args acc
    | Const(name,_) when fine && mem name ["~"; "/\\"; "\\/"; "==>"; "="; "COND"] &&
        (type_of t = bool_ty || name = "COND") ->
        itlist (fun a acc -> atoms acc a) args acc
    | Const(("word_ushr"|"word_shl"|"word_ishr"|"word_rol"|"word_ror") as name,_)
        when length args = 2 && is_numeral (el 1 args) &&
             (fine || name = "word_ushr") ->
        atoms acc (hd args)
    | Const("bit",_) when fine && length args = 2 && is_numeral (hd args) ->
        atoms acc (el 1 args)
    | Const("word",_) when length args = 1 && is_numeral (hd args) -> acc
    | Const(("T"|"F"),_) when fine -> acc
    | _ -> if mem t acc then acc else t :: acc in
  let l,r = dest_eq tm in
  let xs = atoms (atoms [] l) r in
  let vs = map (fun x -> genvar (type_of x)) xs in
  let abstract = subst (zip vs xs) tm in
  INST (zip xs vs) (BITBLAST_RULE abstract);;

let SAIL_HL_X86_REMS_WORD_EQ_RULE = SAIL_HL_X86_REMS_WORD_EQ_GEN_RULE false;;

(* Compare two chains of writes to the same components, value by value,
   proving each differing pair of values with rule. *)
let rec SAIL_HL_X86_REMS_STATE_EQ_RULE_CONV rule tm =
  let l,r = dest_eq tm in
  if l = r then EQT_INTRO (REFL l) else
  match l, r with
  | Comb(Comb(Comb(Const("write",_),c),a),x),
    Comb(Comb(Comb(Const("write",_),c'),b),y) when c = c' ->
      let va = if compare a b = 0 then REFL a else rule (mk_eq(a,b)) in
      let rest = EQT_ELIM (SAIL_HL_X86_REMS_STATE_EQ_RULE_CONV rule (mk_eq(x,y))) in
      EQT_INTRO (MK_COMB(AP_TERM (rator(rator l)) va, rest))
  | _ -> failwith "SAIL_HL_X86_REMS_STATE_EQ_CONV";;

let SAIL_HL_X86_REMS_STATE_EQ_CONV =
  SAIL_HL_X86_REMS_STATE_EQ_RULE_CONV SAIL_HL_X86_REMS_WORD_EQ_RULE;;

let SAIL_HL_X86_REMS_STATE_EQ_RULE_TAC rule =
  REPEAT (AP_TERM_TAC THEN ABS_TAC) THEN AP_TERM_TAC THEN
  CONV_TAC (SAIL_HL_X86_REMS_STATE_EQ_RULE_CONV rule);;

(* A legacy byte operand d selects a high byte exactly when 4 <= val d.
   REMS tests the zero-extended register number against 4. *)
let SAIL_HL_X86_REMS_LEGACY_FIELD = prove
 (`(!d:3 word. word_subword d (0,3):3 word = d) /\
   (!d:3 word. &(val(word_zx d:4 word)):int < &4 <=> ~(4 <= val d)) /\
   (!d:3 word. val d < 4 <=> ~(4 <= val d))`,
  REPEAT CONJ_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; DIMINDEX_3] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[ADD_CLAUSES];
    REWRITE_TAC[SAIL_HL_X86_GPR_LEGACY_FIELD_VALUE; INT_OF_NUM_LT] THEN
    ARITH_TAC;
    ARITH_TAC]);;

(* SEQ sequences an assignment; this sequences an undefined value. *)
let SAIL_HL_X86_REMS_UNDEFINED_SEQ = prove
 (`!c:(S,V)component r:S->T->bool s t.
     ((\s s'. ?y. write c y s = s') ,, r) s t <=> ?y. r (write c y s) t`,
  REWRITE_TAC[seq] THEN MESON_TAC[]);;

(* Compare a normalized REMS root with an s2n-bignum instruction, as
   SAIL_HL_X86_REMS_CLAIM_TAC below, after an optional case split. In each
   case, decide asl rewrites with the case assumptions asl, both in the
   normalized relation and in the unfolded instruction, and rule proves the
   remaining value equalities between the two final states. *)
let SAIL_HL_X86_REMS_CASES_CLAIM_TAC normalized instruction narrowing
    split decide rule =
  let t = `t:x86state` in
  let orient tm =
    if is_eq tm && rand tm = t && lhand tm <> t then SYM_CONV tm
    else failwith "oriented" in
  let cases = match split with None -> false | Some _ -> true in
  REPEAT GEN_TAC THEN
  (match split with None -> ALL_TAC | Some tac -> tac) THEN
  ASSUM_LIST (fun asl ->
    let normalized = if not cases then normalized else
      GEN_ALL (CONV_RULE (RAND_CONV
        (SAIL_HL_X86_REWRITE_CONV (asl @ [SAIL_HL_X86_REMS_LEGACY_FIELD;
                              SAIL_HL_X86_GPR_LEGACY_FIELD_VALUE;
                              INT_OF_NUM_EQ]) THENC
         decide asl THENC
         SAIL_HL_X86_REMS_STATE_CONV THENC
         TOP_DEPTH_CONV SAIL_HL_X86_REMS_UNDEFINED_CONV))
        (SPEC_ALL normalized)) in
    REWRITE_TAC[sail_hl_x86_core; normalized; LEFT_AND_EXISTS_THM]) THEN
  CONV_TAC(LAND_CONV(TRY_CONV SAIL_HL_X86_REMS_PUSH_EXISTS_CONV)) THEN
  REWRITE_TAC[UNWIND_THM1] THEN
  REWRITE_TAC[instruction] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  (* Resolve case-dependent choices of assignment before sequencing. *)
  (if not cases then ALL_TAC else
   ASM_REWRITE_TAC[SAIL_HL_X86_REMS_LEGACY_FIELD;
                   SAIL_HL_X86_GPR_LEGACY_FIELD_VALUE] THEN
   REWRITE_TAC[SAIL_HL_X86_REMS_BIT0_COND] THEN
   ASSUM_LIST (fun asl -> CONV_TAC (decide asl))) THEN
  REWRITE_TAC[assign; SEQ; UNDEFINED_VALUES; SAIL_HL_X86_REMS_UNDEFINED_SEQ;
              SEQ_ID; ASSIGNS_SEQ; ASSIGNS_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  (* Implicit multiply operands, as views of the full registers. *)
  REWRITE_TAC[RAX; RDX; EAX; EDX; AX; DX; AH; AL; GSYM COMPONENT_COMPOSE_ASSOC] THEN
  (if not cases then ALL_TAC else
   ASM_REWRITE_TAC[SAIL_HL_X86_REMS_LEGACY_FIELD;
                   SAIL_HL_X86_GPR_LEGACY_FIELD_VALUE] THEN
   REWRITE_TAC[SAIL_HL_X86_REMS_BIT0_COND]) THEN
  (* s2n-bignum's narrow register views as reads and writes of the full
     register, as for the shina claims. *)
  REWRITE_TAC[GPR8; GPR16; GPR32_Z; GPR64; READ_SHORT; WRITE_SHORT;
              READ_ZEROTOP_32; WRITE_ZEROTOP_32] THEN
  REWRITE_TAC SAIL_HL_X86_GPR_SHORT_REWRITES THEN
  REWRITE_TAC SAIL_HL_X86_GPR_INSERT_REWRITES THEN
  REWRITE_TAC[UNWIND_THM1; UNWIND_THM2; SAIL_HL_X86_RIP_TWICE] THEN
  CONV_TAC(TOP_DEPTH_CONV orient) THEN
  CONV_TAC(ONCE_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC narrowing THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV(SAIL_HL_X86_REMS_LOW_CONV ORELSEC
                          SAIL_HL_X86_REMS_NARROW_CONV)) THEN
  REWRITE_TAC[WORD_ZX_BITVAL] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
  REWRITE_TAC[SAIL_HL_X86_ARBITRARY_BIT0] THEN
  CONV_TAC(BINOP_CONV(TRY_CONV SAIL_HL_X86_REMS_EXISTS_ORDER_CONV)) THEN
  (* TEST's and two-operand IMUL's REMS bodies take their operands in the
     opposite order to s2n-bignum. *)
  REWRITE_TAC[WORD_AND_SYM; WORD_MUL_SYM; INT_MUL_SYM] THEN
  (REFL_TAC ORELSE
   (CONV_TAC(DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
    ASSUM_LIST (fun asl -> SAIL_HL_X86_REMS_STATE_EQ_RULE_TAC (rule asl))) ORELSE
   PRINT_GOAL_TAC);;

let SAIL_HL_X86_REMS_CLAIM_TAC normalized instruction narrowing legacy =
  SAIL_HL_X86_REMS_CASES_CLAIM_TAC normalized instruction narrowing
    (if legacy = [] then None else
     (* Legacy byte forms: consider low and high byte operands separately,
        resolving the REMS register selection in the normalized relation. *)
     Some(MAP_EVERY (fun v -> ASM_CASES_TAC (mk_comb(mk_comb(
       `(<=):num->num->bool`,`4`), mk_comb(`val:3 word->num`, v)))) legacy))
    (fun _ -> ALL_CONV) (fun _ -> SAIL_HL_X86_REMS_WORD_EQ_RULE);;

