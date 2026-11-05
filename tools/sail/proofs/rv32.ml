(* Agreement of the upstream RV32I and M instruction clauses, under the
   backend's RV32 register, memory and retirement interpretations, with
   s2n-bignum's relations. One table lists every form; the kind of each
   theorem comes from s2n-bignum's definition: _SAFE_EQ where it has an
   alignment guard, _DIFF where it permits every final state, and _EQ
   otherwise. For DIV, DIVU, REM and REMU, s2n-bignum also records the
   operands as a timing event, which Sail does not model, so their Sail
   side is followed by that event. Equivalence includes the x0 component,
   and immediates keep the Sail decoder's widths. *)
loadt "riscv/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/rv32.ml";;
loadt "tools/sail/_build/rv32-control.ml";;

let SAIL_HL_RV32_X0_CONTRACT = prove
 (`(!s:riscvstate. read (riscv_gpr (word 0)) s = word 0) /\
   (!v s:riscvstate. write (riscv_gpr (word 0)) v s = s)`,
  REWRITE_TAC[riscv_gpr; ZERO; X0; READ_RVALUE; WRITE_RVALUE]);;

let SAIL_HL_RV32_GPR_ORTHOGONAL = prove
 (`!r:5 word. orthogonal_components (riscv_gpr r) events /\
              orthogonal_components (riscv_gpr r) PC`,
  GEN_TAC THEN REWRITE_TAC[riscv_gpr] THEN REPEAT COND_CASES_TAC THEN
  CONJ_TAC THEN CONV_TAC ORTHOGONAL_COMPONENTS_CONV);;

(* Sail writes rd before the access event or the PC; s2n-bignum after.
   Reads of PC and events see through register writes. *)
let SAIL_HL_RV32_COMMUTE = prove
 (`(!r value trace s.
     write (riscv_gpr r) value (write events trace s) =
     write events trace (write (riscv_gpr r) value s)) /\
   (!r value pc s.
     write (riscv_gpr r) value (write PC pc s) =
     write PC pc (write (riscv_gpr r) value s)) /\
   (!r value s. read PC (write (riscv_gpr r) value s) = read PC s) /\
   (!r value s. read events (write (riscv_gpr r) value s) = read events s)`,
  MESON_TAC[SAIL_HL_RV32_GPR_ORTHOGONAL; orthogonal_components]);;

let SAIL_HL_RV32_PC = prove
 (`(!pc s. read PC (write PC pc s) = pc) /\
   (!pc s. read events (write PC pc s) = read events s) /\
   (!s:riscvstate. write PC (read PC s) s = s)`,
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC[] THEN
  MATCH_ACCEPT_TAC(CONJUNCT1(CONJUNCT2(REWRITE_RULE[strongly_valid_component]
    (STRONGLY_VALID_COMPONENT_RULE `PC:(riscvstate,32 word)component`)))));;

(* Word facts that relate Sail's operations to s2n-bignum's. *)
let SAIL_HL_RV32_WORDS = prove
 (`(!x:32 word. val(word_subword x (0,5):5 word) = val x MOD 32) /\
   (!b. (word_zx (if b then word 1 else word 0:1 word):32 word) =
        (if b then word 1 else word 0)) /\
   (!b. ((word(bitval b):1 word) = word 0 <=> ~b) /\
        ((word(bitval b):1 word) = word 1 <=> b)) /\
   (!x:32 word. word_subword x (0,8):8 word = word_zx x /\
                word_subword x (0,16):16 word = word_zx x /\
                word_subword x (0,32):32 word = x) /\
   (!x:32 word.
      word_or (word_and x (word_not (word (2 EXP 0))))
        (word_shl (word_zx (word 0:1 word)) 0) =
      word_and x (word_not (word 1))) /\
   (!x y:32 word.
      (iword (ival x * ival y):64 word) =
      word_mul (word_sx x:64 word) (word_sx y:64 word)) /\
   (!x y:32 word.
      word_subword (word_mul (word_sx x:64 word) (word_sx y)) (0,32):32 word =
      word_mul x y) /\
   (!x y:32 word.
      (iword (ival x * &(val y)):64 word) = word_mul (word_sx x) (word_zx y) /\
      (iword (&(val x) * &(val y)):64 word) =
      word_mul (word_zx x) (word_zx y))`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUBWORD; EXP; DIV_1] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV);
    REWRITE_TAC[FORALL_BOOL_THM] THEN CONV_TAC WORD_REDUCE_CONV;
    REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV;
    GEN_TAC THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST;
    REWRITE_TAC[EXP; WORD_ZX_0; WORD_SHL_ZERO; WORD_OR_0];
    REWRITE_TAC[word_sx; IWORD_INT_MUL];
    REWRITE_TAC[GSYM DIMINDEX_32; WORD_SUBWORD_DIMINDEX; WORD_USHR_ZERO] THEN
    SIMP_TAC[WORD_ZX_MUL; DIMINDEX_32; DIMINDEX_64;
             ARITH_RULE `32 <= 64`] THEN
    SIMP_TAC[GSYM WORD_SX_ZX; WORD_SX_SX; DIMINDEX_32; DIMINDEX_64;
             ARITH_RULE `32 <= 64`];
    REWRITE_TAC[word_sx; word_zx; WORD_IWORD; IWORD_INT_MUL]]);;

(* Sail's quotient and remainder round toward zero; the translator writes
   them with HOL's Euclidean div and rem (TRUST.md). Relate them to
   word_jdiv, word_jrem, word_udiv and word_umod: a quotient of 2^31, from
   -2^31 / -1, wraps to -2^31 in both. *)
let SAIL_HL_RV32_QUOT = prove
 (`!a b:int. ~(b = &0)
     ==> (if a < &0 then --(--a div b) else a div b) =
         int_sgn a * int_sgn b * (abs a div abs b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!c. c div b = int_sgn b * (c div abs b)`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[INT_SGN; INT_ABS] THEN
    ASM_CASES_TAC `&0:int < b` THENL
     [ASM_SIMP_TAC[INT_LT_IMP_LE; INT_MUL_LID];
      SUBGOAL_THEN `b:int < &0 /\ ~(&0 <= b)` STRIP_ASSUME_TAC THENL
       [ASM_INT_ARITH_TAC; ASM_REWRITE_TAC[INT_DIV_RNEG] THEN INT_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[INT_SGN; INT_ABS] THEN ASM_CASES_TAC `a:int < &0` THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[INT_ARITH `a:int < &0 ==> ~(&0 <= a) /\ ~(&0 < a)`] THEN
    INT_ARITH_TAC;
    ASM_CASES_TAC `a:int = &0` THEN
    ASM_REWRITE_TAC[INT_DIV_ZERO; INT_LT_REFL; INT_LE_REFL] THEN
    ASM_SIMP_TAC[INT_ARITH
      `~(a:int < &0) /\ ~(a = &0) ==> &0 <= a /\ &0 < a`] THEN
    INT_ARITH_TAC]);;

let SAIL_HL_RV32_REM = prove
 (`!a b:int. ~(b = &0)
     ==> (if a < &0 then --(--a rem b) else a rem b) =
         a - (if a < &0 then --(--a div b) else a div b) * b`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INT_DIVISION) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `a:int` th) THEN MP_TAC(SPEC `--a:int` th)) THEN
  INT_ARITH_TAC);;

let SAIL_HL_RV32_QUOT_WRAP = prove
 (`(!a b:int. abs(if a < &0 then --(--a div b) else a div b) <= abs a) /\
   (!q a:int. abs q <= abs a /\ -- &2147483648 <= a /\ a < &2147483648 /\
              q >= &2147483648 ==> (q == -- &2147483648) (mod (&2 pow 32)))`,
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[INT_ABS_NEG] THEN
    MESON_TAC[INT_DIV_LE; INT_ABS_NEG];
    REWRITE_TAC[int_congruent] THEN EXISTS_TAC `&1:int` THEN
    CONV_TAC INT_REDUCE_CONV THEN ASM_INT_ARITH_TAC]);;

let SAIL_HL_RV32_DIVISION = prove
 (`(!m n:32 word. ~(n = word 0) ==>
      word_jdiv m n =
      (if (if ival m < &0 then --(--ival m div ival n)
           else ival m div ival n) >= &2147483648
       then iword (-- &2147483648)
       else iword (if ival m < &0 then --(--ival m div ival n)
                   else ival m div ival n))) /\
   (!m n:32 word. word_jrem m n =
      if n = word 0 then m
      else iword(if ival m < &0 then --(--ival m rem ival n)
                 else ival m rem ival n)) /\
   (!m n:32 word.
      iword(&(val m) div &(val n)) = word_udiv m n /\
      iword(&(val m) rem &(val n)) = word_umod m n /\
      word_umod m (word 0) = m /\ iword(&(val m)) = m) /\
   iword (-- &1):32 word = word_not (word 0)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_TAC THEN SUBGOAL_THEN `~(ival(n:32 word) = &0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IVAL_EQ_0]; ALL_TAC] THEN
    REWRITE_TAC[word_jdiv; imodular] THEN
    ASM_SIMP_TAC[GSYM SAIL_HL_RV32_QUOT] THEN
    MATCH_MP_TAC(MESON[] `(p ==> x = a) ==> x = (if p then a else x)`) THEN
    DISCH_TAC THEN REWRITE_TAC[IWORD_EQ; DIMINDEX_32] THEN
    MATCH_MP_TAC(CONJUNCT2 SAIL_HL_RV32_QUOT_WRAP) THEN
    EXISTS_TAC `ival(m:32 word)` THEN
    ASM_REWRITE_TAC[SAIL_HL_RV32_QUOT_WRAP] THEN
    MP_TAC(ISPEC `m:32 word` IVAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
    CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN SIMP_TAC[];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[word_jrem; WORD_MUL_0; WORD_SUB_0] THEN
    SUBGOAL_THEN `~(ival(n:32 word) = &0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IVAL_EQ_0]; ALL_TAC] THEN
    ASM_SIMP_TAC[SAIL_HL_RV32_REM; word_jdiv; imodular;
                 GSYM SAIL_HL_RV32_QUOT] THEN
    REWRITE_TAC[IWORD_INT_SUB; IWORD_INT_MUL; IWORD_IVAL];
    REWRITE_TAC[INT_OF_NUM_DIV; INT_OF_NUM_REM; GSYM WORD_IWORD; word_udiv;
                word_umod; modular; VAL_WORD_0; MOD_ZERO; WORD_VAL];
    CONV_TAC WORD_REDUCE_CONV]);;

let SAIL_HL_RV32_ALIGNED4_BITS = prove
 (`!x:32 word. aligned 4 x ==> ~bit 0 x /\ ~bit 1 x`,
  GEN_TAC THEN REWRITE_TAC[aligned] THEN STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT {i:num | i < 2} (bits_of_num(val(x:32 word)))`
    MP_TAC THENL
   [REWRITE_TAC[BITS_OF_NUM_DISJOINT_NUMSEG_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th)) THEN
    REWRITE_TAC[ARITH; IN_BITS_OF_NUM; GSYM BIT_VAL] THEN MESON_TAC[]]);;

(* Unfold both relations and compare the states they compute; decide any
   conditions left, such as a zero divisor, case by case. *)
let SAIL_HL_RV32_UNFOLD_TAC definitions =
  ASM_REWRITE_TAC(definitions @
    [LET_DEF; LET_END_DEF; FST; SND; COND_ID; sail_hl_result_case;
     sail_hl_case_control; sail_hl_type_ExecutionResult_DISTINCT;
     riscv_addr; riscv_branch_target; riscv_event_load; riscv_event_store;
     riscv_event_jump; riscv_event_div; riscv_mulh; riscv_mulhsu; riscv_mulhu;
     WORD_SX_TRIVIAL; NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ; INT_OF_NUM_LT;
     INT_OF_NUM_LE; INT_OF_NUM_GE; CONJUNCT1 LT; VAL_EQ_0; IVAL_EQ_0;
     SAIL_HL_RV32_WORDS; CONJUNCT2 SAIL_HL_RV32_DIVISION]) THEN
  ASM_REWRITE_TAC[SAIL_HL_RV32_PC; SAIL_HL_RV32_COMMUTE] THEN
  REWRITE_TAC[SEQ] THEN
  REWRITE_TAC[assign; SAIL_HL_RV32_PC; SAIL_HL_RV32_COMMUTE] THEN
  TRY(MATCH_ACCEPT_TAC EQ_SYM_EQ) THEN
  REPEAT(COND_CASES_TAC THEN
    ASM_SIMP_TAC[SAIL_HL_RV32_DIVISION; IWORD_IVAL; UNWIND_THM1; UNWIND_THM2]);;

(* Read the guard from s2n-bignum's definition, rather than restating it:
   the definition must be "if guard then ... else ASSIGNS entirety". *)
let SAIL_HL_RV32_UNFOLD_TARGET definition target state =
  rhs(concl(REWRITE_CONV
    [definition; riscv_addr; riscv_branch_target; LET_DEF; LET_END_DEF]
    (mk_comb(target,state))));;

let SAIL_HL_RV32_GUARD definition target state =
  let conditional,argument =
    dest_comb(SAIL_HL_RV32_UNFOLD_TARGET definition target state) in
  if argument <> state then
    failwith "RV32 guard extraction changed the state argument";
  let guard,(_,fallback) = dest_cond conditional in
  if fallback <> `ASSIGNS entirety:riscvstate->riscvstate->bool` then
    failwith "RV32 guard extraction needs ASSIGNS entirety outside the guard";
  guard;;

(* x0 reads zero, so register 0 and offset 0 give address 0; with PC = 4
   the instruction's own address is 0 and a branch not taken goes to 4. *)
let SAIL_HL_RV32_GUARD_WITNESS_TAC fields =
  MAP_EVERY (fun field ->
    let width = hd(snd(dest_type(type_of field))) in
    EXISTS_TAC(mk_comb(mk_const("word",[width,`:N`]),`0`))) fields THEN
  EXISTS_TAC `write PC (word 4) (ARB:riscvstate)` THEN
  REWRITE_TAC[SAIL_HL_RV32_X0_CONTRACT; SAIL_HL_RV32_PC;
              riscv_instruction_pc] THEN
  REPEAT(CHANGED_TAC(CONV_TAC(WORD_REDUCE_CONV THENC INT_REDUCE_CONV THENC
    NUM_REDUCE_CONV) THEN REWRITE_TAC[])) THEN
  REWRITE_TAC[ALIGNED_WORD; DIMINDEX_32] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[];;

(* Inside the guard, decide its branch conditions, so that a branch's
   target is fixed, and use that a four-byte aligned target has bits 1
   and 0 clear: Sail asserts bit 0 and traps on bit 1. *)
let SAIL_HL_RV32_GUARDED_TAC guard definitions =
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun c -> ASM_CASES_TAC (rand(rator(rator c))))
    (find_terms is_cond guard) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    (try STRIP_ASSUME_TAC(MATCH_MP SAIL_HL_RV32_ALIGNED4_BITS th)
     with Failure _ -> ALL_TAC)) THEN
  SAIL_HL_RV32_UNFOLD_TAC definitions;;

(* Every s2n-bignum final state of ECALL and EBREAK, and no Sail one. *)
let SAIL_HL_RV32_DIFF_TAC definitions =
  REPEAT GEN_TAC THEN
  REWRITE_TAC(definitions @ [LET_DEF; LET_END_DEF; COND_ID; ASSIGNS; assign;
    WRITE_ENTIRETY; sail_hl_type_ExecutionResult_DISTINCT]) THEN
  MESON_TAC[];;

(* s2n-bignum records the operands of DIV, DIVU, REM and REMU as a timing
   event, which Sail does not model. Read that event from s2n-bignum's
   definition, if it has one, so that the theorem compares Sail's relation
   followed by the event. *)
let SAIL_HL_RV32_EVENT definition target state =
  let body = rhs(concl(REWRITE_CONV[definition; LET_DEF; LET_END_DEF]
    (mk_comb(target,state)))) in
  let body = rhs(concl(TOP_DEPTH_CONV BETA_CONV body)) in
  try Some(find_term (fun tm ->
    let f,args = strip_comb tm in
    is_const f && fst(dest_const f) = "riscv_event_div" && length args = 3) body)
  with Failure _ -> None;;

let sail_hl_rv32_head th = repeat rator (lhs(snd(strip_forall(concl th))));;

let sail_hl_rv32_fields terms =
  let rec walk found tm =
    if is_var tm then (if mem tm found then found else found @ [tm])
    else if is_comb tm then walk (walk found (rator tm)) (rand tm)
    else found in
  List.fold_left walk [] terms;;

(* The theorem of one form: its root, applied to the Sail fields in Sail's
   order, against s2n-bignum's relation, applied to the operands that the
   decoder passes for these fields. *)
let sail_hl_rv32_claim (form,(fields,operands),root,definition) =
  let s = `s:riscvstate` and t = `t:riscvstate` in
  let apply f args = List.fold_left (fun f a -> mk_icomb(f,a)) f args in
  let source = apply (sail_hl_rv32_head root) fields
  and target = apply (sail_hl_rv32_head definition) operands in
  let source,sequence = match SAIL_HL_RV32_EVENT definition target s with
    | Some event -> mk_icomb(mk_icomb(`(,,):(riscvstate->riscvstate->bool)->
        (riscvstate->riscvstate->bool)->riscvstate->riscvstate->bool`,
        source),event), REWRITE_TAC[seq]
    | None -> source, ALL_TAC in
  let quantified =
    subtract (sail_hl_rv32_fields [target; source]) [s; t] @ [s; t] in
  let relation r = list_mk_comb(r,[s;t]) in
  let definitions = [root; definition] in
  let name = "SAIL_HL_RV32_" ^ form in
  match SAIL_HL_RV32_UNFOLD_TARGET definition target s with
  | Comb(r,_) when r = `ASSIGNS entirety:riscvstate->riscvstate->bool` ->
      name ^ "_DIFF",
      prove(list_mk_forall(quantified,
        mk_conj(relation target, mk_neg(relation source))),
        SAIL_HL_RV32_DIFF_TAC definitions)
  | Comb(c,_) when is_cond c ->
      let guard = SAIL_HL_RV32_GUARD definition target s in
      let witnessed = filter (fun v -> mem v (frees guard)) quantified in
      let satisfiable = prove(list_mk_exists(witnessed,guard),
        SAIL_HL_RV32_GUARD_WITNESS_TAC (butlast witnessed)) in
      let safe = prove(list_mk_forall(quantified,
        mk_imp(guard,mk_iff(relation source,relation target))),
        SAIL_HL_RV32_GUARDED_TAC guard definitions) in
      name ^ "_SAFE_EQ", CONJ satisfiable safe
  | _ ->
      name ^ "_EQ",
      prove(list_mk_forall(quantified,
        mk_iff(relation source,relation target)),
        REPEAT GEN_TAC THEN sequence THEN SAIL_HL_RV32_UNFOLD_TAC definitions);;

(* Sail's fields, in its order, and s2n-bignum's operands for them. *)
let rtype = [`rs2:5 word`; `rs1:5 word`; `rd:5 word`],
            [`riscv_gpr rd`; `riscv_gpr rs1`; `riscv_gpr rs2`]
and itype = [`imm:12 word`; `rs1:5 word`; `rd:5 word`],
            [`riscv_gpr rd`; `riscv_gpr rs1`; `word_sx (imm:12 word):int32`]
and shift = [`shamt:6 word`; `rs1:5 word`; `rd:5 word`],
            [`riscv_gpr rd`; `riscv_gpr rs1`;
             `val(word_subword (shamt:6 word) (0,5):5 word)`]
and utype = [`imm:20 word`; `rd:5 word`],
            [`riscv_gpr rd`; `word_join (imm:20 word) (word 0:12 word):int32`]
and store = [`imm:12 word`; `rs2:5 word`; `rs1:5 word`],
            [`riscv_gpr rs2`; `riscv_gpr rs1`; `word_sx (imm:12 word):int32`]
and btype = [`imm:13 word`; `rs2:5 word`; `rs1:5 word`],
            [`riscv_gpr rs1`; `riscv_gpr rs2`; `word_sx (imm:13 word):int32`]
and jtype = [`imm:21 word`; `rd:5 word`],
            [`riscv_gpr rd`; `word_sx (imm:21 word):int32`]
and fence = [`reg_is_5ffiom_5factive:(riscvstate,bool)component`;
             `fm:4 word`; `pred:4 word`; `succ:4 word`;
             `rs:5 word`; `rd:5 word`], []
and ecall = [`reg_cur_5fprivilege:
               (riscvstate,sail_hl_type_Privilege)component`], []
and none = [], [];;

let SAIL_HL_RV32_FORMS = [
  "LUI", utype, sail_hl_rv_5fUTYPE_5fLUI, riscv_LUI;
  "AUIPC", utype, sail_hl_rv_5fUTYPE_5fAUIPC, riscv_AUIPC;
  "ADDI", itype, sail_hl_rv_5fITYPE_5fADDI, riscv_ADDI;
  "SLTI", itype, sail_hl_rv_5fITYPE_5fSLTI, riscv_SLTI;
  "SLTIU", itype, sail_hl_rv_5fITYPE_5fSLTIU, riscv_SLTIU;
  "XORI", itype, sail_hl_rv_5fITYPE_5fXORI, riscv_XORI;
  "ORI", itype, sail_hl_rv_5fITYPE_5fORI, riscv_ORI;
  "ANDI", itype, sail_hl_rv_5fITYPE_5fANDI, riscv_ANDI;
  "SLLI", shift, sail_hl_rv_5fSHIFTIOP_5fSLLI, riscv_SLLI;
  "SRLI", shift, sail_hl_rv_5fSHIFTIOP_5fSRLI, riscv_SRLI;
  "SRAI", shift, sail_hl_rv_5fSHIFTIOP_5fSRAI, riscv_SRAI;
  "ADD", rtype, sail_hl_rv_5fRTYPE_5fADD, riscv_ADD;
  "SUB", rtype, sail_hl_rv_5fRTYPE_5fSUB, riscv_SUB;
  "SLL", rtype, sail_hl_rv_5fRTYPE_5fSLL, riscv_SLL;
  "SLT", rtype, sail_hl_rv_5fRTYPE_5fSLT, riscv_SLT;
  "SLTU", rtype, sail_hl_rv_5fRTYPE_5fSLTU, riscv_SLTU;
  "XOR", rtype, sail_hl_rv_5fRTYPE_5fXOR, riscv_XOR;
  "SRL", rtype, sail_hl_rv_5fRTYPE_5fSRL, riscv_SRL;
  "SRA", rtype, sail_hl_rv_5fRTYPE_5fSRA, riscv_SRA;
  "OR", rtype, sail_hl_rv_5fRTYPE_5fOR, riscv_OR;
  "AND", rtype, sail_hl_rv_5fRTYPE_5fAND, riscv_AND;
  "MUL", rtype, sail_hl_rv_5fMUL_5fMUL, riscv_MUL;
  "MULH", rtype, sail_hl_rv_5fMUL_5fMULH, riscv_MULH;
  "MULHSU", rtype, sail_hl_rv_5fMUL_5fMULHSU, riscv_MULHSU;
  "MULHU", rtype, sail_hl_rv_5fMUL_5fMULHU, riscv_MULHU;
  "DIV", rtype, sail_hl_rv_5fDIV_5fDIV, riscv_DIV;
  "DIVU", rtype, sail_hl_rv_5fDIV_5fDIVU, riscv_DIVU;
  "REM", rtype, sail_hl_rv_5fREM_5fREM, riscv_REM;
  "REMU", rtype, sail_hl_rv_5fREM_5fREMU, riscv_REMU;
  "LB", itype, sail_hl_rv_5fLOAD_5fLB, riscv_LB;
  "LH", itype, sail_hl_rv_5fLOAD_5fLH, riscv_LH;
  "LW", itype, sail_hl_rv_5fLOAD_5fLW, riscv_LW;
  "LBU", itype, sail_hl_rv_5fLOAD_5fLBU, riscv_LBU;
  "LHU", itype, sail_hl_rv_5fLOAD_5fLHU, riscv_LHU;
  "SB", store, sail_hl_rv_5fSTORE_5fSB, riscv_SB;
  "SH", store, sail_hl_rv_5fSTORE_5fSH, riscv_SH;
  "SW", store, sail_hl_rv_5fSTORE_5fSW, riscv_SW;
  "FENCE", fence, sail_hl_rv_5fFENCE, riscv_FENCE;
  "FENCE_TSO", none, sail_hl_rv_5fFENCE_5fTSO, riscv_FENCE;
  "PAUSE", none, sail_hl_rv_5fPAUSE, riscv_FENCE;
  "BEQ", btype, sail_hl_rv_5fBTYPE_5fBEQ, riscv_BEQ;
  "BNE", btype, sail_hl_rv_5fBTYPE_5fBNE, riscv_BNE;
  "BLT", btype, sail_hl_rv_5fBTYPE_5fBLT, riscv_BLT;
  "BGE", btype, sail_hl_rv_5fBTYPE_5fBGE, riscv_BGE;
  "BLTU", btype, sail_hl_rv_5fBTYPE_5fBLTU, riscv_BLTU;
  "BGEU", btype, sail_hl_rv_5fBTYPE_5fBGEU, riscv_BGEU;
  "JAL", jtype, sail_hl_rv_5fJAL, riscv_JAL;
  "JALR", itype, sail_hl_rv_5fJALR, riscv_JALR;
  "ECALL", ecall, sail_hl_rv_5fECALL, riscv_ECALL;
  "EBREAK", none, sail_hl_rv_5fEBREAK, riscv_EBREAK];;

let SAIL_HL_RV32_CLAIMS = map sail_hl_rv32_claim SAIL_HL_RV32_FORMS;;

List.iter sail_hl_report SAIL_HL_RV32_CLAIMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_RV32_PROOFS_OK";;
