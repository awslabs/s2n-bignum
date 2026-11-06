(* Definitions, lemmas and tactics shared by the six Arm memory suites.
   A suite loads its generated model, then this file, then states its
   encoded forms and the tactic that proves them.

   Memory agreement observes every machine-state field except the access
   events. Sail can emit one event per lane while the HOL model emits one
   event for the whole instruction. Erasing events from BOTH outcomes makes
   this boundary explicit; it cannot conceal a changed register, flag, PC
   or byte of memory. Each claim states agreement under the exact
   successful-input guard of the HOL definition, and that the guard holds
   for some operands and state. *)
needs "tools/sail/proofs/tuple-apply-conv.ml";;
needs "tools/sail/proofs/proof-fork.ml";;
needs "tools/sail/proofs/report.ml";;

let sail_hl_arm_memory_erase_events = new_definition
 `sail_hl_arm_memory_erase_events (s:armstate) = write events [] s`;;

let sail_hl_arm_memory_observed = new_definition
 `sail_hl_arm_memory_observed (R:armstate->armstate->bool) s t <=>
    ?u. R s u /\
        sail_hl_arm_memory_erase_events u =
        sail_hl_arm_memory_erase_events t`;;

(* Equality after erasure is equality of the COMPLETE retained fields,
   not only the destination register or the accessed range of memory. *)
let SAIL_HL_ARM_MEMORY_OBSERVED_STATE_FIELDS = prove
 (`!s t:armstate.
     sail_hl_arm_memory_erase_events s =
     sail_hl_arm_memory_erase_events t <=>
     read PC s = read PC t /\
     read registers s = read registers t /\
     read simdregisters s = read simdregisters t /\
     read flags s = read flags t /\
     read memory s = read memory t`,
  REPEAT(MATCH_MP_TAC armstate_INDUCT ORELSE GEN_TAC) THEN
  REWRITE_TAC[sail_hl_arm_memory_erase_events; armstate_COMPONENTS;
              injectivity "armstate"]);;

let SAIL_HL_ARM_MEMORY_ERASE_EVENT_WRITE = prove
 (`!es. !s:armstate.
     sail_hl_arm_memory_erase_events (write events es s) =
     sail_hl_arm_memory_erase_events s`,
  REWRITE_TAC[sail_hl_arm_memory_erase_events] THEN
  CONV_TAC(DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN REWRITE_TAC[]);;

let SAIL_HL_ARM_MEMORY_ERASE_OTHER_WRITE = prove
 (`!c:(armstate,A)component. !x s.
     orthogonal_components c events
     ==> sail_hl_arm_memory_erase_events (write c x s) =
         write c x (sail_hl_arm_memory_erase_events s)`,
  REWRITE_TAC[sail_hl_arm_memory_erase_events; orthogonal_components] THEN
  MESON_TAC[]);;

(* XREG includes a conditional zero register. A symbolic index cannot be
   canonicalized by choosing one branch, but BOTH branches are disjoint
   from events. These facts retain every index, including encoded XZR. *)
let SAIL_HL_ARM_MEMORY_GPR_EVENTS_DISJOINT = prove
 (`!n. orthogonal_components (XREG n) events`,
  GEN_TAC THEN REWRITE_TAC[XREG] THEN COND_CASES_TAC THEN
  W(fun (_,goal) -> MATCH_ACCEPT_TAC(ORTHOGONAL_COMPONENTS_CONV goal)));;

let SAIL_HL_ARM_MEMORY_WREG_EVENTS_DISJOINT = prove
 (`!n. orthogonal_components (WREG n) events`,
  GEN_TAC THEN REWRITE_TAC[WREG] THEN
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_LEFT THEN
  REWRITE_TAC[SAIL_HL_ARM_MEMORY_GPR_EVENTS_DISJOINT]);;

(* Move erasure through a state write only after proving that its component
   is disjoint from events. In particular, this is not a rule that discards
   arbitrary writes or assumes that an unfamiliar component is irrelevant.
   TOP_DEPTH_CONV tries this at every subterm. Prepare each PART_MATCH
   once, and refuse a term without the rule's head shape before matching:
   setting up a match per subterm dominated the erasure passes. *)
let SAIL_HL_ARM_MEMORY_ERASE_WRITE_CONV =
  let other_write =
    PART_MATCH (lhand o rand) SAIL_HL_ARM_MEMORY_ERASE_OTHER_WRITE in
  let gpr_disjoint = PART_MATCH I SAIL_HL_ARM_MEMORY_GPR_EVENTS_DISJOINT
  and wreg_disjoint = PART_MATCH I SAIL_HL_ARM_MEMORY_WREG_EVENTS_DISJOINT in
  GEN_REWRITE_CONV I [SAIL_HL_ARM_MEMORY_ERASE_EVENT_WRITE] ORELSEC
  (fun term ->
    (match term with
     | Comb(Const("sail_hl_arm_memory_erase_events",_),
            Comb(Comb(Comb(Const("write",_),_),_),_)) -> ()
     | _ -> failwith "not an erased state write");
    let rule = other_write term in
    let goal = lhand(concl rule) in
    let disjoint =
      try gpr_disjoint goal
      with Failure _ ->
        try wreg_disjoint goal
        with Failure _ -> ORTHOGONAL_COMPONENTS_CONV goal in
    MP rule disjoint);;

(* A lane read is the corresponding little-endian slice of the whole
   byte-range read. Addresses use word arithmetic throughout: neither
   alignment nor absence of address-space wraparound is assumed. The type
   widths and lane extent are explicit, since wbytes uses width DIV 8. *)
let SAIL_HL_MEMORY_LANE_READ = prove
 (`!a:int64. !s:armstate. !k lanesize wholebytes.
     dimindex(:L) = 8 * lanesize /\
     dimindex(:W) = 8 * wholebytes /\
     k + lanesize <= wholebytes
     ==> (read (memory :> wbytes (word_add a (word k))) s:L word =
          word_subword (read (memory :> wbytes a) s:W word)
                       (8 * k,8 * lanesize))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; READ_COMPONENT_COMPOSE; VAL_WORD_SUBWORD;
              VAL_READ_WBYTES] THEN
  ASM_REWRITE_TAC[ARITH_RULE `MIN n n = n`;
                  ARITH_RULE `(8 * n) DIV 8 = n`] THEN
  REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
  ASM_SIMP_TAC[ARITH_RULE `k + l <= w ==> MIN (w - k) l = l`]);;

(* The source executes consecutive stores in increasing address order.
   WRITE_BYTES_COMBINE uses the opposite nesting order; the two orders
   agree for disjoint subranges. The total-size bound rules out a range
   overlapping itself after wrapping, not wrapping at the base address. *)
let SAIL_HL_MEMORY_ADJACENT_STORE = prove
 (`!a:int64. !m n x y s.
     m + n <= 2 EXP 64
     ==> write (bytes(a,m+n))
           (x MOD 2 EXP (8*m) + 2 EXP (8*m) * y) s =
         write (bytes(word_add a (word m),n)) y (write (bytes(a,m)) x s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WRITE_BYTES_COMBINE] THEN
  SUBGOAL_THEN
   `orthogonal_components (bytes(a:int64,m))
                          (bytes(word_add a (word m),n))`
   ASSUME_TAC THENL
   [REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; DIMINDEX_64;
                VAL_WORD_ADD; VAL_WORD] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[NONOVERLAPPING_MODULO_RMOD] THEN
    MP_TAC(SPECL
      [`2 EXP 64`; `val(a:int64)`; `0`; `m:num`; `m:num`; `n:num`]
      NONOVERLAPPING_MODULO_OFFSET_SIMPLE_BOTH) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; LE_REFL; LE_0];
    ASM_MESON_TAC[orthogonal_components]]);;

(* Lift adjacent byte stores through memory and asword. The low word is
   written first, exactly as on the separate-access source path. The bound
   prevents a range overlapping itself; it does not forbid base wraparound. *)
let SAIL_HL_MEMORY_PAIR_STORE = prove
 (`!a:int64. !x:L word. !y:H word. !s:armstate. !m n.
     dimindex(:L) = 8 * m /\
     dimindex(:H) = 8 * n /\
     dimindex(:W) = 8 * (m + n) /\
     m + n <= 2 EXP 64
     ==> write (memory :> wbytes a) (word_join y x:W word) s =
         write (memory :> wbytes (word_add a (word m))) y
           (write (memory :> wbytes a) x s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `dimindex(:H) + dimindex(:L) = dimindex(:W)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE] THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  CONV_TAC(DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[wbytes; WRITE_COMPONENT_COMPOSE; asword; through;
    read; write; ARITH_RULE `(8 * k) DIV 8 = k`] THEN
  ASM_SIMP_TAC[VAL_WORD_JOIN_SIMPLE] THEN
  MP_TAC(ISPECL [`a:int64`; `m:num`; `n:num`; `val(x:L word)`;
    `val(y:H word)`; `read memory s:64 word->byte`]
    SAIL_HL_MEMORY_ADJACENT_STORE) THEN
  ASM_REWRITE_TAC[write] THEN
  ASM_SIMP_TAC[MOD_LT; REWRITE_RULE[ASSUME `dimindex(:L) = 8 * m`]
    (ISPEC `x:L word` VAL_BOUND)] THEN
  REWRITE_TAC[ADD_SYM; MULT_SYM]);;

(* Unlike the zero destination register, encoded base register 31 is SP.
   Distinct base components follow from orthogonality and writability, not
   from a syntactic inequality between two component expressions. *)
let SAIL_HL_ARM_BASE_REGISTER_IS_SP = prove
 (`!n:5 word. XREG_SP n = SP <=> n = word 31`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_CASES_TAC `n:5 word = word 31` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `orthogonal_components (XREG_SP n) SP` ASSUME_TAC THENL
     [REWRITE_TAC[XREG_SP; SP] THEN
      MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN
      CONJ_TAC THENL
       [CONV_TAC VALID_COMPONENT_CONV;
        MATCH_MP_TAC ORTHOGONAL_COMPONENTS_ELEMENT THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`XREG_SP n`; `SP`] ARM_DISTINCT_WORD_COMPONENTS) THEN
    ASM_REWRITE_TAC[VALID_COMPONENT_RULE `SP`] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[XREG_SP; SP]]);;

let SAIL_HL_ARM_NONZERO_REGISTER_INDEX = prove
 (`!n:5 word. ~(n = word 31) ==> ~(val n >= 31)`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_CONV `dimindex(:5)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `n:5 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:5)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* The base encoding uses SP at 31; an ordinary register operand uses ZR.
   This conditional identity connects the source's branch on the encoding
   with the HOL base component without enumerating all 32 register values. *)
let SAIL_HL_ARM_BASE_REGISTER_COMPONENT = prove
 (`!n:5 word.
     XREG_SP n = if n = word 31 then SP else XREG' n`,
  GEN_TAC THEN ASM_CASES_TAC `n:5 word = word 31` THEN
  ASM_SIMP_TAC[XREG_SP; SP; XREG'; XREG;
    SAIL_HL_ARM_NONZERO_REGISTER_INDEX; WORD_VAL]);;

let SAIL_HL_ARM_GPR_WRITEBACK_DISJOINT = prove
 (`!t n:5 word.
     orthogonal_components (XREG' t) (XREG_SP n)
     ==> ~(t = n) \/ n = word 31`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n:5 word = word 31` THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `t:5 word = n` THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM SUBST1_TAC THEN
  ASM_SIMP_TAC[XREG'; XREG; SAIL_HL_ARM_NONZERO_REGISTER_INDEX;
               WORD_VAL; GSYM XREG_SP] THEN
  MP_TAC(ISPECL [`XREG_SP n`; `XREG_SP n`] ARM_DISTINCT_WORD_COMPONENTS) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `valid_component (XREG_SP n)` ASSUME_TAC THENL
   [REWRITE_TAC[XREG_SP] THEN CONV_TAC VALID_COMPONENT_CONV;
    ASM_MESON_TAC[]]);;

(* A 32-bit destination still overlaps its 64-bit base at the same index.
   The two component types differ, so distinctness of equal-width word
   components is not the relevant fact here. *)
let SAIL_HL_ARM_WREG_BASE_OVERLAP = prove
 (`!c:(S,64 word)component.
     valid_component c
     ==> ~orthogonal_components (c :> zerotop_32) c`,
  REWRITE_TAC[orthogonal_components; READ_ZEROTOP_32; valid_component] THEN
  REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[WORD_ZX_0; WORD_ZX_1; WORD_NE_10]);;

let SAIL_HL_ARM_WREG_WRITEBACK_DISJOINT = prove
 (`!t n:5 word.
     orthogonal_components (WREG' t) (XREG_SP n)
     ==> ~(t = n) \/ n = word 31`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n:5 word = word 31` THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `t:5 word = n` THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM SUBST1_TAC THEN
  ASM_SIMP_TAC[WREG'; WREG; XREG; SAIL_HL_ARM_NONZERO_REGISTER_INDEX;
               WORD_VAL; GSYM XREG_SP] THEN
  MATCH_MP_TAC SAIL_HL_ARM_WREG_BASE_OVERLAP THEN
  REWRITE_TAC[XREG_SP] THEN CONV_TAC VALID_COMPONENT_CONV);;

(* Select widths from the word types of the actual expression. The OCaml
   arithmetic only proposes the theorem instantiation: HOL then checks all
   width/size premises, and PART_MATCH checks the complete memory expression.
   An unfamiliar component, non-byte width or different slice is refused. *)
let SAIL_HL_ARM_MEMORY_PAIR_BYTE_WIDTH term =
  let name,parameters = dest_type(type_of term) in
  if name <> "word" || length parameters <> 1 then
    failwith "paired access needs a word";
  let width = Num.int_of_num(dest_finty(hd parameters)) in
  if width mod 8 <> 0 then failwith "paired access needs whole bytes";
  width / 8;;

let SAIL_HL_ARM_MEMORY_PAIR_WIDTH_RULE types m n theorem =
  let rule = INST_TYPE types (SPEC_ALL theorem) in
  let rule = INST [mk_small_numeral m,`m:num`;
                   mk_small_numeral n,`n:num`] rule in
  REWRITE_RULE[]
    (CONV_RULE (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) rule);;

let SAIL_HL_ARM_MEMORY_PAIR_STORE_CONV term =
  let head,args = strip_comb term in
  if fst(dest_const head) <> "write" || length args <> 3 then
    failwith "not a paired store";
  let value = el 1 args in
  let join,words = strip_comb value in
  if fst(dest_const join) <> "word_join" || length words <> 2 then
    failwith "paired store value is not a word join";
  let high = hd words and low = el 1 words in
  let types = [
    hd(snd(dest_type(type_of low))),`:L`;
    hd(snd(dest_type(type_of high))),`:H`;
    hd(snd(dest_type(type_of value))),`:W`] in
  let rule = SAIL_HL_ARM_MEMORY_PAIR_WIDTH_RULE types
    (SAIL_HL_ARM_MEMORY_PAIR_BYTE_WIDTH low)
    (SAIL_HL_ARM_MEMORY_PAIR_BYTE_WIDTH high) SAIL_HL_MEMORY_PAIR_STORE in
  PART_MATCH lhand rule term;;

(* SP checking compares the value with its rounded-down 16-byte address.
   This fact needs only the HOL instruction's existing alignment guard;
   it does not assume a value for a feature or control register. *)
let SAIL_HL_ARM_ALIGNED_SP_IWORD = prove
 (`!sp:64 word.
     aligned 16 sp
     ==> iword ((&(val sp) div &16) * &16):64 word = sp`,
  REWRITE_TAC[INT_OF_NUM_DIV; INT_OF_NUM_MUL; GSYM WORD_IWORD;
              aligned; DIVIDES_DIV_MULT] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WORD_VAL]);;

(* Extract only the canonical flat-memory word read. This is deliberately
   narrower than arbitrary component composition: the final PART_MATCH
   must retain the original base, initial state and word types. Lane
   searches call this on every subterm, so parse the component once. *)
let SAIL_HL_ARM_MEMORY_WORD_READ_PARTS =
  let memory_component = `memory` in
  fun term ->
  let head,args = strip_comb term in
  if fst(dest_const head) <> "read" || length args <> 2 then
    failwith "not a memory word read";
  let compose,parts = strip_comb(hd args) in
  if fst(dest_const compose) <> ":>" ||
     length parts <> 2 || hd parts <> memory_component then
    failwith "not a canonical memory component";
  let bytes,addresses = strip_comb(el 1 parts) in
  if fst(dest_const bytes) <> "wbytes" || length addresses <> 1 then
    failwith "not a word-sized byte range";
  hd addresses,el 1 args;;

(* Re-express a literal-offset lane read as a slice of a supplied whole
   read. Byte width and lane extent are proved by HOL, including when the
   64-bit base wraps. A later register's complete read can start at a+16,
   while its source lane has normalized to a+20: the offset is then four.
   Only identical symbolic roots and literal offsets are matched. The
   proposed address equality is checked with HOL word-addition rules; the
   complete read on the theorem's right remains the original supplied term.
   Other roots, states, symbolic offsets or out-of-range lanes are refused. *)
let SAIL_HL_ARM_MEMORY_LANE_CONV whole_read term =
  let base,state = SAIL_HL_ARM_MEMORY_WORD_READ_PARTS whole_read in
  let address,lane_state = SAIL_HL_ARM_MEMORY_WORD_READ_PARTS term in
  if lane_state <> state then failwith "lane read uses another initial state";
  let literal_add expression =
    let head,args = strip_comb expression in
    if fst(dest_const head) <> "word_add" || length args <> 2 then
      failwith "not a literal word offset";
    let word,arguments = strip_comb(el 1 args) in
    if fst(dest_const word) <> "word" || length arguments <> 1 then
      failwith "lane read needs a numeral byte offset";
    hd args,dest_small_numeral(hd arguments) in
  let offset = if address = base then 0 else
    let root,offset = literal_add address in
    if root = base then offset else
    let base_root,base_offset =
      try literal_add base with Failure _ -> base,0 in
    if root <> base_root || offset < base_offset then
      failwith "lane read uses another base or precedes the complete read";
    offset - base_offset in
  let lane = SAIL_HL_ARM_MEMORY_PAIR_BYTE_WIDTH term in
  let whole = SAIL_HL_ARM_MEMORY_PAIR_BYTE_WIDTH whole_read in
  let types = [
    hd(snd(dest_type(type_of term))),`:L`;
    hd(snd(dest_type(type_of whole_read))),`:W`] in
  let rule = ISPECL [base;state;mk_small_numeral offset;
    mk_small_numeral lane;mk_small_numeral whole]
    (INST_TYPE types SAIL_HL_MEMORY_LANE_READ) in
  let rule = REWRITE_RULE[WORD_ADD_0]
    (CONV_RULE (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) rule) in
  let normalize_address =
    PURE_REWRITE_CONV[WORD_ADD_0; WORD_ADD_ASSOC_CONSTS] THENC
    DEPTH_CONV NUM_ADD_CONV in
  let rule = CONV_RULE (LAND_CONV normalize_address) rule in
  let normalized = normalize_address term in
  TRANS normalized (PART_MATCH lhand rule (rand(concl normalized)));;

(* Sail increments integer register indices modulo 32; HOL uses five-bit
   register fields. These facts retain wraparound, including Q31 -> Q0.
   They constrain no instruction operand and replace no source calculation. *)
let SAIL_HL_ARM_MEMORY_REGISTER_REM32 = prove
 (`!n:int. n - &32 * (n div &32) = n rem &32`,
  REWRITE_TAC[INT_REM_DIV] THEN INT_ARITH_TAC);;

let SAIL_HL_ARM_MEMORY_REGISTER_WRAP = prove
 (`!t:5 word. !i:num.
     (&(val t) + &i) rem &32 = &(val(word_add t (word i)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_REM; INT_OF_NUM_EQ;
    VAL_WORD_ADD; VAL_WORD; DIMINDEX_CONV `dimindex(:5)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC MOD_DOWN_CONV THEN REFL_TAC);;

let SAIL_HL_ARM_MEMORY_REGISTER_WRAP_BASE =
  GEN_ALL(REWRITE_RULE[INT_ADD_RID; WORD_ADD_0]
    (SPECL [`t:5 word`; `0`] SAIL_HL_ARM_MEMORY_REGISTER_WRAP));;

let SAIL_HL_ARM_MEMORY_STRUCTURE_REGISTER_DISJOINT = prove
 (`!t:5 word. !i j:num.
     i < 32 /\ j < 32 /\ ~(i = j)
     ==> orthogonal_components
          (QREG(val(word_add t (word i))))
          (QREG(val(word_add t (word j))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[QREG; WORD_VAL] THEN
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN
  CONJ_TAC THENL
   [CONV_TAC VALID_COMPONENT_CONV;
    MATCH_MP_TAC ORTHOGONAL_COMPONENTS_ELEMENT THEN
    REWRITE_TAC[WORD_RULE
      `word_add (t:N word) x = word_add t y <=> x = y`] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_CONV `dimindex(:5)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]]);;

let SAIL_HL_ARM_MEMORY_STRUCTURE_OTHER_READ = prove
 (`!t:5 word. !i j:num. !x:128 word. !s:armstate.
     i < 32 /\ j < 32 /\ ~(i = j)
     ==> read (QREG(val(word_add t (word i))))
           (write (QREG(val(word_add t (word j)))) x s) =
         read (QREG(val(word_add t (word i)))) s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`t:5 word`; `i:num`; `j:num`]
    SAIL_HL_ARM_MEMORY_STRUCTURE_REGISTER_DISJOINT) THEN
  ASM_REWRITE_TAC[orthogonal_components] THEN MESON_TAC[]);;

(* The largest supported structure has four consecutive registers.
   Instantiate only these finite differences, proving the side conditions.
   The initial five-bit field stays symbolic in every theorem. *)
let SAIL_HL_ARM_MEMORY_STRUCTURE_OTHER_READ_RULES =
  flat(map (fun i -> map (fun j ->
    REWRITE_RULE[WORD_ADD_0]
      (CONV_RULE NUM_REDUCE_CONV
        (SPECL [`t:5 word`; mk_small_numeral i; mk_small_numeral j]
          SAIL_HL_ARM_MEMORY_STRUCTURE_OTHER_READ)))
    (filter (fun j -> i <> j) [0;1;2;3])) [0;1;2;3]);;

let SAIL_HL_ARM_MEMORY_STRUCTURE_DISJOINT_RULES =
  flat(map (fun i -> map (fun j ->
    REWRITE_RULE[WORD_ADD_0]
      (CONV_RULE NUM_REDUCE_CONV
        (SPECL [`t:5 word`; mk_small_numeral i; mk_small_numeral j]
          SAIL_HL_ARM_MEMORY_STRUCTURE_REGISTER_DISJOINT)))
    (filter (fun j -> i <> j) [0;1;2;3])) [0;1;2;3]);;

let SAIL_HL_ARM_MEMORY_WRITE_COMMUTE = prove
 (`!c:(S,A)component. !d:(S,B)component. !x y s.
     orthogonal_components c d
     ==> write c x (write d y s) = write d y (write c x s)`,
  REWRITE_TAC[orthogonal_components] THEN MESON_TAC[]);;

(* Remove a genuinely overwritten earlier Q-register write, even when
   other disjoint writes separate it from the final write. Each crossing
   needs a checked orthogonality theorem; both the old and new value
   calculations remain in their original expressions.

   Swapping arbitrary writes as rewrite rules can loop. This conversion
   succeeds only after locating an earlier write to the SAME component,
   removes that one write, and retains the order of every other write. *)
let SAIL_HL_ARM_MEMORY_STRUCTURE_OVERWRITE_CONV term =
  let write_arguments expression =
    let head,args = strip_comb expression in
    if not(is_const head) || fst(dest_const head) <> "write" ||
       length args <> 3 then failwith "not a complete state write";
    args in
  let arguments = write_arguments term in
  let component = hd arguments and value = el 1 arguments in
  let component_head,_ = strip_comb component in
  if not(is_const component_head) ||
     fst(dest_const component_head) <> "QREG" then
    failwith "not a complete Q-register write";
  let outer state = mk_comb(rator term,state) in
  let disjoint c d =
    let goal = list_mk_comb
      (mk_mconst("orthogonal_components",
        mk_fun_ty (type_of c) (mk_fun_ty (type_of d) `:bool`)),
       [c;d]) in
    try tryfind (fun theorem -> PART_MATCH I theorem goal)
      SAIL_HL_ARM_MEMORY_STRUCTURE_DISJOINT_RULES
    with Failure _ -> ORTHOGONAL_COMPONENTS_CONV goal in
  let rec remove state =
    let inner = write_arguments state in
    let other = hd inner and other_value = el 1 inner and base = el 2 inner in
    if component = other then COMPONENT_WRITE_OVER_WRITE_CONV(outer state)
    else
      let prior = remove base in
      let commute = MATCH_MP
        (ISPECL [component;other;value;other_value;base]
          SAIL_HL_ARM_MEMORY_WRITE_COMMUTE)
        (disjoint component other) in
      let inner_function = rator state in
      let changed = AP_TERM inner_function prior in
      let _,new_state = strip_comb(rand(concl prior)) in
      let restored = MATCH_MP
        (ISPECL [component;other;value;other_value;el 2 new_state]
          SAIL_HL_ARM_MEMORY_WRITE_COMMUTE)
        (disjoint component other) in
      TRANS commute (TRANS changed (GSYM restored)) in
  remove(el 2 arguments);;

(* The post-increment register is read after vector or memory updates in
   the upstream body. Those updates cannot change any GPR. Prove both
   branches of XREG's zero-register definition rather than require Rm<31. *)
let SAIL_HL_ARM_MEMORY_STRUCTURE_GPR_READ_QREG = prove
 (`!i j:num. !x:128 word. !s:armstate.
     read (XREG i) (write (QREG j) x s) = read (XREG i) s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[XREG] THEN COND_CASES_TAC THEN
  W(fun (_,goal) -> MATCH_ACCEPT_TAC(ORTHOGONAL_COMPONENTS_CONV goal)));;

let SAIL_HL_ARM_MEMORY_STRUCTURE_GPR_READ_EVENTS = prove
 (`!i:num. !es. !s:armstate.
     read (XREG i) (write events es s) = read (XREG i) s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[SAIL_HL_ARM_MEMORY_GPR_EVENTS_DISJOINT]);;

let SAIL_HL_ARM_MEMORY_STRUCTURE_GPR_READ_MEMORY = prove
 (`!i:num. !a:64 word. !x:N word. !s:armstate.
     read (XREG i) (write (memory :> wbytes a) x s) = read (XREG i) s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
  REWRITE_TAC[XREG] THEN COND_CASES_TAC THEN
  W(fun (_,goal) -> MATCH_ACCEPT_TAC(ORTHOGONAL_COMPONENTS_CONV goal)));;

let SAIL_HL_ARM_MEMORY_STRUCTURE_GPR_READ_RULES =
  [SAIL_HL_ARM_MEMORY_STRUCTURE_GPR_READ_QREG;
   SAIL_HL_ARM_MEMORY_STRUCTURE_GPR_READ_EVENTS;
   SAIL_HL_ARM_MEMORY_STRUCTURE_GPR_READ_MEMORY];;

let SAIL_HL_ARM_MEMORY_HOL_DEFINITIONS = [
  "arm_LDR",arm_LDR; "arm_STR",arm_STR; "arm_LDRB",arm_LDRB; "arm_STRB",arm_STRB;
  "arm_LDP",arm_LDP; "arm_STP",arm_STP; "arm_LDP4",arm_LDP4; "arm_STP4",arm_STP4;
  "arm_LD2",arm_LD2; "arm_ST2",arm_ST2; "arm_LD3",arm_LD3; "arm_ST3",arm_ST3;
  "arm_LD1R",arm_LD1R;
];;

let SAIL_HL_ARM_MEMORY_FIELD31 = prove
 (`!n:5 word.
     (val n = 31 <=> n = word 31) /\
     (31 = val n <=> n = word 31)`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_CONV `dimindex(:5)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]);;

(* A branch join binds its state and mutable locals as a tuple. When that
   tuple is an unknown conditional, ordinary GEN_BETA_CONV cannot match
   its constructor pattern. Reconstruct only the nested pairs in that
   pattern from FST/SND projections, proving each reconstruction with PAIR.
   Beta conversion then sees the required constructors. This works for any
   tuple length and does not copy the continuation into each branch.
   A different constructor pattern is deliberately refused. *)
let SAIL_HL_ARM_MEMORY_TUPLE_BETA_CONV ?(beta=GEN_BETA_CONV) term =
  let abstraction,argument = dest_comb term in
  let pattern,_ = dest_gabs abstraction in
  let rec reconstruct pattern argument =
    if is_var pattern then REFL argument else
    let left,right = dest_pair pattern in
    let pair = ISPEC argument PAIR in
    let projections = lhand(concl pair) in
    let first,second = dest_pair projections in
    let reconstructed = MK_COMB
      (AP_TERM (rator(rator projections)) (reconstruct left first),
       reconstruct right second) in
    TRANS reconstructed pair in
  let shape = reconstruct pattern argument in
  let changed = AP_TERM abstraction (SYM shape) in
  TRANS changed (beta(rand(concl changed)));;

(* Keep tuple arguments and prior write states as evaluator closures.
   Substituting a growing state history into every later lane duplicates
   work even when a read immediately passes the intervening writes.
   Component conversions return kernel proofs; unfamiliar overlaps remain
   visible and must be handled by the family proof. Extra equations, such
   as reads across consecutive vector registers, must have no assumptions:
   Compute reduces under binders and cannot use a particular goal's facts. *)
let SAIL_HL_ARM_MEMORY_STATE_CBV_TAC ?(defer_read_state=false) extra_rules =
  List.iter (fun theorem ->
    if hyp theorem <> [] then
      failwith "memory CBV requires closed extra rules") extra_rules;
  W(fun (_,_) ->
    let computations = Compute.bool_compset () in
    let beta = SAIL_HL_TUPLE_APPLY_CONV () ORELSEC GEN_BETA_CONV in
    let arithmetic = REWRITES_CONV
      (itlist (uncurry net_of_conv)
        (int_red_conv_list @ num_red_conv_list) empty_net) in
    num_compute_add_convs computations;
    int_compute_add_convs computations;
    word_compute_add_convs computations;
    Compute.add_thms
      [LET_END_DEF; FST; SND; NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ;
       INT_OF_NUM_LT; INT_OF_NUM_REM; WORD_VAL;
       SEQ; SEQ_ID; no_offset;
       offset_address; offset_writeback; offset_writesback]
      computations;
    (* Discard an earlier partial Q write only when a later write to that
       SAME component replaces it and every intervening write is proved
       disjoint. The checked conversion retains values, events and order. *)
    Compute.add_conv
      (`write:(A,B)component->B->A->A`,3,
       CHANGED_CONV SAIL_HL_ARM_MEMORY_STRUCTURE_OVERWRITE_CONV ORELSEC
       CHANGED_CONV COMPONENT_WRITE_OVER_WRITE_CONV)
      computations;
    (* Normalize each write value once, but keep its previous state as a
       closure until a read needs it. Traversing the whole growing history
       at each write repeatedly revisits old event tails and register reads.
       Keeping values opaque too would instead copy unresolved dependencies
       into later tuple bindings. Component conversions still account for
       every read, and the complete-state proof retains all writes/order. *)
    Compute.set_skip computations `write:(A,B)component->B->A->A` (Some 2);
    Compute.add_conv
      (`GABS:(A->bool)->A`,2,
       beta ORELSEC SAIL_HL_ARM_MEMORY_TUPLE_BETA_CONV ~beta)
      computations;
    Compute.add_conv
      (`dimindex:(A->bool)->num`,1,DIMINDEX_CONV) computations;
    (* Distribute only the small projections introduced by tuple beta
       conversion, never the complete continuation. *)
    Compute.add_conv
      (`FST:A#B->A`,1,REWR_CONV COND_RAND) computations;
    Compute.add_conv
      (`SND:A#B->B`,1,REWR_CONV COND_RAND) computations;
    (* A post-register increment reads its GPR after vector, event or
       memory writes. These universal bank-frame facts retain all register
       indices and do not assume that the input fields are distinct. *)
    Compute.add_thms SAIL_HL_ARM_MEMORY_STRUCTURE_GPR_READ_RULES computations;
    (* Install the closed bank equations before the generic conversion.
       Compute tries those rewrite rules before an appended conversion. *)
    Compute.add_thms extra_rules computations;
    Compute.add_conv
      (`read:(A,B)component->A->B`,2,
       (fun term ->
         (* Reparse the result once, after the whole proven read-over-write
            chain. An unproved overlap remains for the family proof. Each
            accepted step must change the term; a future identity rule
            therefore cannot make the repetition loop. *)
         let equality = CHANGED_CONV
           (REPEATC(CHANGED_CONV COMPONENT_READ_OVER_WRITE_CONV)) term in
         let left = lhand(concl equality) in
         if not(aconv left term) || hyp equality <> [] then
           failwith "memory read chain: mismatched or open equality";
         if left = term then equality else TRANS(ALPHA term left) equality))
      computations;
    (* A control result chooses a fault or a successful continuation.
       Strong CBV otherwise reduces both function bodies while a symbolic
       discriminator remains unresolved. In particular that can expand a
       whole store loop under an unknown state before the SP guard is used.
       Keep the continuations opaque. This checked conversion evaluates
       only the discriminator; the original constructor equations then
       select the continuation. Unknown outcomes stay visible until the
       caller's existing guard simplification resolves them. *)
    let result_case =
      `sail_hl_result_case:(A->C)->(B->C)->(A+B)->C` in
    let case_rules = filter (fun theorem ->
      try
        let head,_ = strip_comb(lhand(concl(SPEC_ALL theorem))) in
        fst(dest_const head) = "sail_hl_result_case"
      with Failure _ -> false)
      (flat(map (CONJUNCTS o SPEC_ALL) extra_rules)) in
    if case_rules <> [] then (
      Compute.set_skip computations result_case (Some 0);
      Compute.add_conv
        (result_case,3,
         CHANGED_CONV
          (RAND_CONV(Compute.CBV_CONV computations) THENC
           TRY_CONV(FIRST_CONV(map REWR_CONV case_rules))))
        computations);
    (* Strict evaluation shares normalized load histories before copying
       them. Deferring read states can instead copy unresolved joined
       histories. Four-register stores opt in because checked frame rules
       remove irrelevant writes faster; strict evaluation of their residual
       still handles unfamiliar reads and every remaining write value. *)
    let reduce = CONV_TAC(fun term ->
      if not defer_read_state then Compute.CBV_CONV computations term else
      let read_constant = `read:(A,B)component->A->B` in
      Compute.set_skip computations read_constant (Some 1);
      let reduced =
        try Compute.CBV_CONV computations term
        with error ->
          Compute.set_skip computations read_constant None;
          raise error in
      Compute.set_skip computations read_constant None;
      TRANS reduced
        (Compute.CBV_CONV computations (rand(concl reduced)))) in
    (* Selecting one control result can reveal another encoded-field or
       alignment test inside its previously opaque continuation. Alternate
       the same closed evaluator with the existing goal facts until those
       facts no longer change the term. Assumptions are used by the tactic,
       never registered in Compute, which also reduces under binders. *)
    reduce THEN
    REPEAT
     (CHANGED_TAC
       (PURE_ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ;
          INT_OF_NUM_LT; SAIL_HL_ARM_MEMORY_FIELD31;
          COND_CLAUSES; COND_ID] THEN
        PURE_ASM_SIMP_TAC
          [SAIL_HL_ARM_ALIGNED_SP_IWORD; COND_CLAUSES; COND_ID]) THEN
      reduce) THEN
    (* Earlier writes remain prior-state closures rather than being
       evaluated again. Close their exposed skeleton with only identities,
       built-in arithmetic and the existing proved overwrite conversions.
       No helper body or state history is expanded; an unproved overlap
       remains visible to the family proof. *)
    PURE_REWRITE_TAC[WORD_VAL; LET_END_DEF] THEN
    CONV_TAC(DEPTH_CONV(CHANGED_CONV arithmetic)) THEN
    CONV_TAC(TOP_DEPTH_CONV
      (CHANGED_CONV SAIL_HL_ARM_MEMORY_STRUCTURE_OVERWRITE_CONV ORELSEC
       CHANGED_CONV COMPONENT_WRITE_OVER_WRITE_CONV)));;

(* Select the instruction's safe branch before reducing assignment syntax.
   The SP fact is derived from its exact guard, not imposed as an additional
   source-configuration assumption. Both base encodings remain represented. *)
let SAIL_HL_ARM_MEMORY_PREPARE_TAC
    ?(defer_read_state=false) extra_rules source_definition target_definition =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `n:5 word = word 31 ==> aligned 16 (read SP (s:armstate))`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[SAIL_HL_ARM_BASE_REGISTER_IS_SP;
                  SAIL_HL_ARM_BASE_REGISTER_COMPONENT];
    ALL_TAC] THEN
  ASM_CASES_TAC `n:5 word = word 31` THENL
   [ASSUME_TAC(MATCH_MP
      (ASSUME `n:5 word = word 31 ==> aligned 16 (read SP (s:armstate))`)
      (ASSUME `n:5 word = word 31`));
    ALL_TAC] THEN
  PURE_ASM_REWRITE_TAC[sail_hl_arm_memory_observed; source_definition;
    target_definition; FST; SND; NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ;
    INT_OF_NUM_LT; SAIL_HL_ARM_BASE_REGISTER_IS_SP;
    SAIL_HL_ARM_BASE_REGISTER_COMPONENT; SAIL_HL_ARM_MEMORY_FIELD31;
    XREG'; no_offset; offset_address; offset_writeback; offset_writesback] THEN
  SAIL_HL_ARM_MEMORY_STATE_CBV_TAC ~defer_read_state
    (source_definition::extra_rules) THEN
  PURE_ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ;
    INT_OF_NUM_LT; SAIL_HL_ARM_MEMORY_FIELD31;
    COND_CLAUSES; COND_ID] THEN
  PURE_ASM_SIMP_TAC[SAIL_HL_ARM_ALIGNED_SP_IWORD; COND_CLAUSES; COND_ID] THEN
  PURE_ASM_REWRITE_TAC[SEQ; SEQ_ID; WORD_ZX_TRIVIAL; WORD_SX_TRIVIAL;
    word_zx; WORD_SHL_WORD; MULT_SYM] THEN
  SAIL_HL_ARM_MEMORY_STATE_CBV_TAC ~defer_read_state
    (source_definition::extra_rules) THEN
  PURE_REWRITE_TAC[assign; GSYM BYTES64_WBYTES; GSYM BYTES128_WBYTES] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  PURE_ASM_REWRITE_TAC[no_offset;
    offset_address; offset_writeback; offset_writesback;
    SAIL_HL_ARM_MEMORY_FIELD31;
    COND_CLAUSES; COND_ID; SEQ; SEQ_ID; WORD_ADD_0] THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_ARM_MEMORY_ERASE_WRITE_CONV) THEN
  PURE_REWRITE_TAC[EXISTS_SIMP; UNWIND_THM1; UNWIND_THM2] THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_ARM_MEMORY_ERASE_WRITE_CONV) THEN
  REWRITE_TAC[];;

(* A pre/post-indexed GPR instruction is safe only when its destination or
   source does not overlap the writable base. The existing HOL guard gives
   that component fact. Derive the matching encoded-field condition from
   it; do not assume that distinct field names mean distinct registers.
   Encoding 31 remains included: its ordinary operand is ZR, its base SP. *)
let SAIL_HL_ARM_MEMORY_SINGLE_WRITEBACK_FIELDS = prove
 (`!t n:5 word.
     (~(t = n) \/ n = word 31)
     ==> ~(n = t /\ ~(n = word 31)) /\
         ~(val n = val t /\ ~(val n = 31)) /\
         (~(n = word 31) ==> ~(val n = val t))`,
  REWRITE_TAC[VAL_EQ; SAIL_HL_ARM_MEMORY_FIELD31] THEN MESON_TAC[]);;

let SAIL_HL_ARM_MEMORY_SINGLE_GUARD_FACTS guard =
  let facts = CONJUNCTS(PURE_REWRITE_RULE
    [no_offset; offset_writesback; IMP_CLAUSES; AND_CLAUSES] guard) in
  let disjoint = List.filter_map (fun fact ->
    try Some(MATCH_MP SAIL_HL_ARM_GPR_WRITEBACK_DISJOINT fact)
    with Failure _ ->
      try Some(MATCH_MP SAIL_HL_ARM_WREG_WRITEBACK_DISJOINT fact)
      with Failure _ -> None) facts in
  facts @ flat(map (fun theorem -> CONJUNCTS
    (MATCH_MP SAIL_HL_ARM_MEMORY_SINGLE_WRITEBACK_FIELDS theorem)) disjoint);;

(* After the base case split, apply the guard-derived implication rather
   than asking rewriting to discover its propositional consequence.
   A SIMD operand has a different register bank, so there may be no such
   implication; do not manufacture a field inequality in that case. *)
let SAIL_HL_ARM_MEMORY_SINGLE_BRANCH_FACTS_TAC =
  W(fun (assumptions,_) ->
    match List.find_opt (fun (_,theorem) ->
      aconv (concl theorem) `~(n:5 word = word 31)`) assumptions with
    | None -> ALL_TAC
    | Some(_,non_sp) ->
        MAP_EVERY ASSUME_TAC
          (List.filter_map (fun (_,theorem) ->
            try Some(MATCH_MP theorem non_sp) with Failure _ -> None)
            assumptions));;

(* Lane/value bridges for the LD1 (multiple-register), LD2, LD3 and LD1R
   proofs. They connect lane calculations with whole-register and
   whole-memory operations; they neither constrain operands nor replace a
   Sail body.

   Enumerate bit positions on small variables once. Substituting
   the actual calculated values afterwards avoids repeatedly traversing a
   complete lane history while constructing the finite case theorem.
   A register result has 128 bits; each individual memory lane has 8, 16,
   32 or 64 bits. Other value types remain a visible proof failure. *)
let SAIL_HL_ARM_MEMORY_STRUCTURE_VALUE_BITS =
  map (fun width ->
    let word_type = string_of_int width ^ " word" in
    GEN_ALL(CONV_RULE
      (RAND_CONV
        (BINDER_CONV(LAND_CONV(RAND_CONV DIMINDEX_CONV)) THENC
         EXPAND_CASES_CONV))
      (ISPECL [parse_term("x:" ^ word_type);parse_term("y:" ^ word_type)]
        WORD_EQ_BITS_ALT))
  ) [8;16;32;64;128];;

let SAIL_HL_ARM_MEMORY_STRUCTURE_VALUE_TAC =
  GEN_REWRITE_TAC I SAIL_HL_ARM_MEMORY_STRUCTURE_VALUE_BITS THEN
  REWRITE_TAC all_simd_rules THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM word_zx; BIT_WORD_INSERT; BIT_WORD_DUPLICATE;
    BIT_WORD_JOIN; BIT_WORD_SUBWORD; BIT_WORD_ZX; BIT_WORD_0;
    word_subdeinterleave; word_interleave; BIT_WORD_OF_BITS;
    IN_ELIM_THM; LENGTH] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[LET_END_DEF; BIT_WORD_INSERT; BIT_WORD_JOIN; BIT_WORD_SUBWORD;
    BIT_WORD_ZX; BIT_WORD_0] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  (* Zero-extending a 64-bit memory read clears bits 64..127. The bit
     expansion above still contains observations of the original word;
     discharge those out-of-width positions rather than assume its value. *)
  SIMP_TAC[BIT_TRIVIAL; DIMINDEX_64; ARITH] THEN PRINT_GOAL_TAC;;

(* Re-express source lane reads through the target's complete contiguous
   read. The checked lane conversion retains the exact initial state and
   base, proves each extent, and supports address wraparound. Try larger
   complete reads first and refuse equal-size/self slices. Multiple whole
   reads are needed when another memory family shares this finisher. *)
let SAIL_HL_ARM_MEMORY_STRUCTURE_LANES_TAC =
  W(fun (_,goal) ->
    let reads = find_terms (fun term ->
      try ignore(SAIL_HL_ARM_MEMORY_WORD_READ_PARTS term); true
      with Failure _ -> false) goal in
    if reads = [] then ALL_TAC else
    let wholes = sort (fun left right ->
      SAIL_HL_ARM_MEMORY_PAIR_BYTE_WIDTH left >
      SAIL_HL_ARM_MEMORY_PAIR_BYTE_WIDTH right) reads in
    CONV_TAC(DEPTH_CONV(fun term ->
      tryfind (fun whole ->
        if SAIL_HL_ARM_MEMORY_PAIR_BYTE_WIDTH term >=
           SAIL_HL_ARM_MEMORY_PAIR_BYTE_WIDTH whole then
          failwith "not a smaller memory lane";
        SAIL_HL_ARM_MEMORY_LANE_CONV whole term) wholes)));;

(* A store writes one element at a time in ascending address order. Split
   the target's complete memory write into that same order. The whole word
   is first reconstructed from its slices by a fixed-width HOL word proof;
   the existing pair-store conversion then proves each memory split.

   The element width is the smallest actual memory-write width present in
   the comparison, not a chosen value for any instruction argument. Each
   conversion checks the original complete memory component and refuses an
   unrelated component, unsupported width or non-integral lane layout. *)
let SAIL_HL_ARM_MEMORY_STRUCTURE_STORE_TAC =
  let rules = ref [] in
  let memory_component = `memory` in
  let memory_write term =
    let head,args = strip_comb term in
    if not(is_const head) || fst(dest_const head) <> "write" ||
       length args <> 3 then failwith "not a complete memory write";
    let compose,parts = strip_comb(hd args) in
    if not(is_const compose) || fst(dest_const compose) <> ":>" ||
       length parts <> 2 || hd parts <> memory_component then
      failwith "not the flat memory component";
    let bytes,addresses = strip_comb(el 1 parts) in
    if not(is_const bytes) || fst(dest_const bytes) <> "wbytes" ||
       length addresses <> 1 then failwith "not a word-sized memory range";
    el 1 args in
  let rule width element =
    try assoc (width,element) !rules with Failure _ ->
    if not(mem width [64;128;192;256;384]) ||
       not(mem element [8;16;32;64]) || width mod element <> 0 then
      failwith "unsupported structure-store lane layout";
    let positions = map (fun i -> i * element)
      (0--(width / element - 1)) in
    let whole = "(x:" ^ string_of_int width ^ " word)" in
    let slice position =
      "(word_subword " ^ whole ^ " (" ^ string_of_int position ^
      "," ^ string_of_int element ^ "):" ^
      string_of_int element ^ " word)" in
    let rec joined positions = match positions with
      | [position] -> slice position
      | _ ->
          let low,high = chop_list (length positions / 2) positions in
          "(word_join " ^ joined high ^ " " ^ joined low ^ ":" ^
          string_of_int (length positions * element) ^ " word)" in
    let theorem = prove(parse_term
      ("!x:" ^ string_of_int width ^ " word. x = " ^ joined positions),
      CONV_TAC WORD_BLAST) in
    rules := ((width,element),theorem)::!rules;
    theorem in
  W(fun (_,goal) ->
    let writes = find_terms (fun term ->
      try ignore(memory_write term); true with Failure _ -> false) goal in
    if writes = [] then ALL_TAC else
    let element = itlist min
      (map (fun term ->
        8 * SAIL_HL_ARM_MEMORY_PAIR_BYTE_WIDTH(memory_write term)) writes)
      128 in
    CONV_TAC(TOP_DEPTH_CONV(fun term ->
      let value = memory_write term in
      let width = 8 * SAIL_HL_ARM_MEMORY_PAIR_BYTE_WIDTH value in
      if width <= element then failwith "already an individual memory lane";
      let joined = PART_MATCH lhand (rule width element) value in
      let changed = AP_THM (AP_TERM (rator(rator term)) joined) (rand term) in
      CONV_RULE(RAND_CONV
        (TOP_DEPTH_CONV SAIL_HL_ARM_MEMORY_PAIR_STORE_CONV)) changed)));;

(* The normal forms have the same complete state-write structure. Check
   each component, prove differing register/lane values by bits, then
   rebuild the equality with kernel congruence. A changed component, state
   structure or unsupported value type is a visible proof failure. *)
let SAIL_HL_ARM_MEMORY_STRUCTURE_STATE_EQ left right =
  let rec equality source target =
    if source = target then REFL source else
    let source_head,source_args = strip_comb source
    and target_head,target_args = strip_comb target in
    if source_head <> target_head || not(is_const source_head) ||
       fst(dest_const source_head) <> "write" ||
       length source_args <> 3 || length target_args <> 3 ||
       hd source_args <> hd target_args then
      failwith "different complete memory state-write structures";
    let source_value = el 1 source_args and target_value = el 1 target_args in
    let value = if source_value = target_value then REFL source_value else
      prove(mk_eq(source_value,target_value),
        SAIL_HL_ARM_MEMORY_STRUCTURE_VALUE_TAC) in
    MK_COMB(AP_TERM(rator(rator source)) value,
      equality (el 2 source_args) (el 2 target_args)) in
  equality left right;;

let SAIL_HL_ARM_MEMORY_STRUCTURE_STATE_TAC =
  W(fun (_,goal) ->
    try
      let source = lhand(lhand goal) and target = lhand(rand goal) in
      let equality = SAIL_HL_ARM_MEMORY_STRUCTURE_STATE_EQ source target in
      REWRITE_TAC[equality]
    with Failure message -> PRINT_GOAL_TAC THEN FAIL_TAC message);;

(* General preparation retains the original instruction equation and exact
   safe guard. The remaining rewrites align integer register indices,
   vector components and zero-cleared upper bits with the HOL instruction. *)
let SAIL_HL_ARM_MEMORY_STRUCTURE_CBV_RULES =
  [SAIL_HL_ARM_MEMORY_REGISTER_REM32; SAIL_HL_ARM_MEMORY_REGISTER_WRAP;
   SAIL_HL_ARM_MEMORY_REGISTER_WRAP_BASE;
   WORD_ADD_0; WORD_ADD_ASSOC_CONSTS; INT_ADD_LID; INT_ADD_RID;
   (* A 64-bit vector form uses DREG. Expose its QREG projection before
      another lane copies the state, so the same closed disjoint-read
      rules apply. Writes still clear the upper 64 bits exactly. *)
   DREG'; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64] @
  SAIL_HL_ARM_MEMORY_STRUCTURE_OTHER_READ_RULES;;

let SAIL_HL_ARM_MEMORY_STRUCTURE_TAC ?(defer_read_state=false)
    source_definition target_definition =
  (* The post-register encoding uses Rm=31 for an immediate increment.
     Split that case and every other register value before reducing offset
     operations. Forms without an Rm field do not need this split. *)
  REPEAT GEN_TAC THEN
  W(fun (_,goal) ->
    if vfree_in `m:5 word` goal then
      ASM_CASES_TAC `m:5 word = word 31`
    else ALL_TAC) THEN
  (* Reduce reads across different registers BEFORE a subsequent lane
     copies its previous state. These are universal kernel equations,
     not hypotheses about an operand or source configuration. *)
  SAIL_HL_ARM_MEMORY_PREPARE_TAC ~defer_read_state
    SAIL_HL_ARM_MEMORY_STRUCTURE_CBV_RULES source_definition
    (REWRITE_RULE[WORD_DEINTERLEAVE_CLAUSES] target_definition) THEN
  REWRITE_TAC[SAIL_HL_ARM_MEMORY_REGISTER_REM32;
    SAIL_HL_ARM_MEMORY_REGISTER_WRAP;
    SAIL_HL_ARM_MEMORY_REGISTER_WRAP_BASE; WORD_ADD_0;
    WORD_ADD_ASSOC_CONSTS; INT_ADD_LID; INT_ADD_RID;
    NUM_OF_INT_OF_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[QREG'; DREG'; DREG; WRITE_ZEROTOP_64; READ_ZEROTOP_64;
    word_zx; WORD_VAL; WORD_DUPLICATE_64_128; WORD_ADD_0] THEN
  (* LD3 binds a three-element list before assembling its assignments.
     Contract that checked constructor pattern, then the newly exposed
     deterministic sequence. No source branch or result is selected. *)
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  PURE_REWRITE_TAC[seq; SEQ_ID] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  PURE_REWRITE_TAC[seq; SEQ_ID; EXISTS_SIMP; UNWIND_THM1; UNWIND_THM2] THEN
  (* Canonicalize memory components before applying the universal bank
     frame rules. A post-register store reads its increment after byte
     writes; bytes8 must expose wbytes for the existing memory/GPR fact. *)
  REWRITE_TAC[BYTES8_WBYTES; BYTES16_WBYTES; BYTES32_WBYTES;
    BYTES64_WBYTES; BYTES128_WBYTES] THEN
  (* An event write can hide the next other-register write, and vice versa.
     Repeat these decreasing read reductions until both are gone. *)
  REPEAT(CHANGED_TAC
   (PURE_REWRITE_TAC
      (SAIL_HL_ARM_MEMORY_STRUCTURE_OTHER_READ_RULES @
       SAIL_HL_ARM_MEMORY_STRUCTURE_GPR_READ_RULES) THEN
    CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV))) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_ARM_MEMORY_STRUCTURE_OVERWRITE_CONV) THEN
  SAIL_HL_ARM_MEMORY_STRUCTURE_STORE_TAC THEN
  PURE_REWRITE_TAC[WORD_ADD_0; WORD_ADD_ASSOC_CONSTS] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  SAIL_HL_ARM_MEMORY_STRUCTURE_LANES_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_ARM_MEMORY_ERASE_WRITE_CONV) THEN
  REWRITE_TAC[EXISTS_SIMP; UNWIND_THM1; UNWIND_THM2] THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_ARM_MEMORY_ERASE_WRITE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  SAIL_HL_ARM_MEMORY_STRUCTURE_STATE_TAC THEN PRINT_GOAL_TAC;;

(* Encoded forms. A form is the Sail root's name, its encoded fields with
   their types, and the HOL instruction applied to its operands. Register
   fields remain five-bit words, including 31 and every overlap. The
   transfer registers are named rt and rt2, after Arm's Rt and Rt2, so
   that no field shares a name with the final state t. Structure registers
   are consecutive modulo 32. For post-register forms, Rm=31 selects the
   encoded immediate increment rather than XZR's value. Address arithmetic
   stays in 64-bit words, including wraparound. *)
let SAIL_HL_ARM_MEMORY_FIELDS names =
  map (fun name -> name,`:5 word`) names;;

let SAIL_HL_ARM_MEMORY_POST mode bytes = match mode with
  | "NO" -> "No_Offset"
  | "POSTI" -> "Postimmediate_Offset (word " ^ string_of_int bytes ^ ")"
  | "POSTR" ->
      "(if val (m:5 word) = 31 then Postimmediate_Offset (word " ^
      string_of_int bytes ^ ") else Postreg_Offset (XREG' m))"
  | _ -> failwith "unknown encoded structure memory addressing mode";;

let SAIL_HL_ARM_MEMORY_STRUCTURE_FORMS operations widths elements modes make =
  flat(map (fun operation -> flat(map (fun width ->
    flat(map (fun element -> map (fun mode ->
      let fields = SAIL_HL_ARM_MEMORY_FIELDS
        (["rt";"n"] @ if mode = "POSTR" then ["m"] else []) in
      make operation width element mode fields
    ) modes) (elements width))
  ) widths)) operations);;

let SAIL_HL_ARM_MEMORY_MULTIPLE_FORM operation width mnemonic count
    element mode fields =
  let register_type = if width = 64 then "DREG'" else "QREG'" in
  let registers = map (fun index ->
    "(" ^ register_type ^ " " ^
    (if index = 0 then "rt" else "(word_add rt (word " ^ string_of_int index ^ "))") ^
    ")") (0--(count - 1)) in
  let target = "arm_" ^ operation ^ " " ^ String.concat " " registers ^
    " (XREG_SP n) (" ^ SAIL_HL_ARM_MEMORY_POST mode (count * width / 8) ^ ")" in
  "arm_" ^ operation ^ string_of_int width ^ "_SIMD_LD" ^ mnemonic ^
    "_E" ^ string_of_int element ^ "_" ^ mode,fields,parse_term target;;

let SAIL_HL_ARM_MEMORY_INTERLEAVED_FORM count operation width element mode fields =
  let registers = map (fun index ->
    "(QREG' " ^ (if index = 0 then "rt"
      else "(word_add rt (word " ^ string_of_int index ^ "))") ^ ")"
  ) (0--(count - 1)) in
  let operands = if count = 3 then "[" ^ String.concat ";" registers ^ "]"
    else String.concat " " registers in
  let target = "arm_" ^ operation ^ " " ^ operands ^ " (XREG_SP n) (" ^
    SAIL_HL_ARM_MEMORY_POST mode (count * width / 8) ^ ") " ^
    string_of_int width ^ " " ^ string_of_int element in
  "arm_" ^ operation ^ string_of_int width ^ "_SIMD_LD" ^ string_of_int count ^
    "_E" ^ string_of_int element ^ "_" ^ mode,fields,parse_term target;;

let SAIL_HL_ARM_MEMORY_INTERLEAVED_ELEMENTS width =
  if width = 64 then [8;16;32] else [8;16;32;64];;

(* Read the successful-input guard from the instantiated HOL instruction,
   rather than maintaining a second list of alignment/overlap conditions.
   Refuse a different equation shape or fallback: the caller must supply an
   actual guarded memory definition with ASSIGNS entirety on its unsafe
   branch. No Sail expression or instruction effect is manufactured here. *)
let SAIL_HL_ARM_MEMORY_GUARD definition application state =
  let unfolded = REWRITE_CONV [definition; LET_DEF; LET_END_DEF]
    (mk_comb(application,state)) in
  let conditional,last_argument = dest_comb(rand(concl unfolded)) in
  if last_argument <> state then
    failwith "memory guard extraction changed the state argument";
  let guard,(_,fallback) = dest_cond conditional in
  if fallback <> `ASSIGNS entirety:armstate->armstate->bool` then
    failwith "memory guard extraction requires the HOL unsafe havoc branch";
  guard;;

(* A guard that never holds would make the form's _SAFE_EQ theorem say
   nothing, so the claim also states that each guard holds somewhere. Give
   the five-bit register fields distinct indices below 31, every other word
   field 0 and the state ARB, then decide the instance: register equalities
   with s2n-bignum's ARM_DISTINCT_WORD_COMPONENTS_CONV, overlaps with
   ORTHOGONAL_COMPONENTS_CONV and offsets with offset_writesback. With
   these indices no base register is SP, so no alignment is needed. *)
let SAIL_HL_ARM_MEMORY_GUARD_CONV =
  let component_equality term =
    let c,_ = dest_eq term in
    if fst(dest_type(type_of c)) <> "component" then
      failwith "not a component equality";
    EQF_INTRO(EQT_ELIM(ARM_DISTINCT_WORD_COMPONENTS_CONV(mk_neg term))) in
  let registers = [XREG'; WREG'; QREG'; DREG'; XREG_SP] in
  REWRITE_CONV registers THENC WORD_REDUCE_CONV THENC
  REWRITE_CONV(offset_writesback :: registers) THENC WORD_REDUCE_CONV THENC
  ONCE_DEPTH_CONV component_equality THENC
  ONCE_DEPTH_CONV(EQT_INTRO o ORTHOGONAL_COMPONENTS_CONV) THENC
  REWRITE_CONV[];;

let SAIL_HL_ARM_MEMORY_GUARD_WITNESS parameters guard state =
  let fields = filter (fun field -> mem field (frees guard)) parameters in
  let witness field (index,values) =
    match dest_type(type_of field) with
    | "word",[width] ->
        let word = mk_const("word",[width,`:N`]) in
        if width = `:5` then
          index + 1, mk_comb(word,mk_small_numeral index) :: values
        else index, mk_comb(word,`0`) :: values
    | _ -> failwith "memory guard witness requires word fields" in
  let _,values = itlist witness (rev fields) (0,[]) in
  prove(list_mk_exists(fields @ [state],guard),
    MAP_EVERY EXISTS_TAC (rev values @ [`ARB:armstate`]) THEN
    CONV_TAC SAIL_HL_ARM_MEMORY_GUARD_CONV);;

(* Prove and report the _SAFE_EQ claim of one form: the HOL guard holds
   for some operands and state, and wherever it holds, the observed Sail
   relation equals the observed HOL relation. The claim retains every
   encoded field and every exported source-configuration parameter. The
   tactic receives the generated root's equation and the HOL definition. *)
let SAIL_HL_ARM_MEMORY_CLAIM tactic (root,fields,target) =
  let source_definition,source =
    Sail_hl_memory_model.SAIL_HL_ARM_MEMORY_MODEL_BINDING root fields in
  let head,_ = strip_comb target in
  let definition = assoc (fst(dest_const head))
    SAIL_HL_ARM_MEMORY_HOL_DEFINITIONS in
  let parameters = union (frees source) (frees target) in
  let s = variant parameters `s:armstate` in
  let t = variant (s::parameters) `t:armstate` in
  let guard = SAIL_HL_ARM_MEMORY_GUARD definition target s in
  let satisfiable = SAIL_HL_ARM_MEMORY_GUARD_WITNESS parameters guard s in
  let observed relation =
    list_mk_comb(`sail_hl_arm_memory_observed`,[relation;s;t]) in
  let safe = prove(list_mk_forall(parameters @ [s;t],
      mk_imp(guard,mk_iff(observed source,observed target))),
    tactic source_definition definition) in
  sail_hl_report("SAIL_HL_ARM_" ^ String.sub root 4 (String.length root - 4) ^
    "_SAFE_EQ",CONJ satisfiable safe);;

(* Prove every form of a suite. The forms may be split across forked
   processes here (proof-fork.ml); each form is proved in exactly one of
   them. The suite then ends with check_axioms and its marker. *)
let SAIL_HL_ARM_MEMORY_CLAIMS marker tactic forms =
  sail_hl_proof_fork marker;
  List.iter (fun ((root,_,_) as form) ->
    if sail_hl_proof_shard root then SAIL_HL_ARM_MEMORY_CLAIM tactic form)
    forms;;
