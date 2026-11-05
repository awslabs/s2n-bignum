(* Register agreement for add/subtract, logic and unary arithmetic.

   The caller loads the generated arithmetic model and x86-gpr-lemmas.ml,
   then passes the model's defining theorems. Each claim compares the entire
   initial/final state relation
   with the corresponding s2n-bignum instruction, not just its destination.
   REX byte registers and legacy high-byte registers are separate forms.
   The 32-bit component includes the architectural upper-bit zeroing.

   Width instances share word/flag mathematics and register normalization.
   There are no operand-value or alias restrictions. Multiply has separate
   product mathematics; shifts have separate count/outcome proofs. *)
let SAIL_HL_X86_GPR_OPERATIONS =
 ["ADD",x86_ADD,false; "ADC",x86_ADC,false;
  "SUB",x86_SUB,false; "SBB",x86_SBB,false; "CMP",x86_CMP,false;
  "AND",x86_AND,false; "OR",x86_OR,false; "XOR",x86_XOR,false;
  "TEST",x86_TEST,false; "ADCX",x86_ADCX,false; "ADOX",x86_ADOX,false;
  "INC",x86_INC,true; "DEC",x86_DEC,true; "NEG",x86_NEG,true;
  "NOT",x86_NOT,true];;

(* PF depends on exactly eight bits, regardless of the operand width.
   The upstream XOR circuit and word_evenparity are related by the existing
   proved byte identity. Open that identity only after word arithmetic and
   register views are normalized: both models then have the same eight
   Boolean observations, without expanding a whole machine state. *)
let SAIL_HL_X86_GPR_PARITY_BITS = CONV_RULE
  (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
  (REWRITE_RULE
    [LET_DEF;LET_END_DEF;BIT_WORD_0;BIT_WORD_BITVAL;BIT_WORD_NOT;
     BIT_WORD_XOR;BIT_WORD_SUBWORD;BIT_WORD_ZX]
    SAIL_HL_X86_PARITY8);;

(* Specializing the general flag facts to y=1 does not calculate an
   instruction result: these remain proved word identities for all x. *)
let SAIL_HL_X86_GPR_PROOF_FACTS width =
  let source = mk_finty(num width) in
  let reduce = CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC WORD_REDUCE_CONV THENC NUM_REDUCE_CONV) in
  let additions = SAIL_HL_X86_GPR_FLAG_REWRITES width in
  let subtraction = SAIL_HL_X86_GPR_SUB_REWRITES width in
  let x = parse_term(Printf.sprintf "x:%d word" width)
  and one = parse_term(Printf.sprintf "word 1:%d word" width) in
  (* FLAG_REWRITES places the no-carry auxiliary fact at index 3 and
     signed-add overflow at index 4. INC specializes these AF/OF facts
     to adding one; the other flags retain their general identities. *)
  let unary_aux = el 3 additions and unary_overflow = el 4 additions in
  let unary = map reduce
    [GEN x (SPECL [x;one] unary_aux);
     GEN x (SPECL [x;one] unary_overflow)] in
  let sign = CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE[source,`:N`] MSB_IVAL) in
  let complement = GEN x (reduce(REWRITE_RULE[BITVAL_CLAUSES;COND_CLAUSES]
    (ISPEC x (SPEC `T` (CONJUNCT2 WORD_XOR_MASK))))) in
  (* DEC/NEG also specialize subtraction at a literal operand. Retain
     their signed observations as well as their bit form: reducing the
     literal sign bit changes which of these patterns can match. *)
  let facts = complement :: unary @ map (REWRITE_RULE[sign]) unary @
    additions @ subtraction @ map (REWRITE_RULE[sign]) subtraction in
  if exists (fun theorem -> hyp theorem <> [] || frees(concl theorem) <> [])
    facts then failwith "open GPR flag rewrite";
  facts;;

(* Some roots retain ModR/M field extraction. Proved subword and register
   identities recover the supplied operand fields before substituting the
   decoded register reads. The same normalization is repeated if undefined
   flag handling exposes another paired value/state binding. Normalize only
   the decoder's three-bit register fields here: opening four-bit arithmetic
   slices earlier would hide the auxiliary-carry theorem's word pattern. *)
let SAIL_HL_X86_GPR_LEGACY_FIELD_VALUE = REWRITE_RULE[]
  (CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE[`:3`,`:M`;`:4`,`:N`] VAL_WORD_ZX));;

let SAIL_HL_X86_GPR_REGISTER_FIELDS_TAC =
  REWRITE_TAC[FST;SND;OUTL;OUTR;GSYM WORD_IWORD;WORD_VAL;
    INT_OF_NUM_REM;NUM_OF_INT_OF_NUM;MOD_MOD_REFL;SAIL_HL_X86_JOIN_ZERO] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV(fun term ->
    if type_of term = `:3 word` then WORD_SIMPLE_SUBWORD_CONV term
    else failwith "not a three-bit register field")) THEN
  REWRITE_TAC[SAIL_HL_X86_REGISTER_BITS;WORD_VAL;
    SAIL_HL_X86_REGISTER_MOD;SAIL_HL_X86_REGISTER_INDEX;
    SAIL_HL_X86_JOIN_ZERO] THEN
  ASM_REWRITE_TAC[SAIL_HL_X86_GPR_LEGACY_FIELD_VALUE;
    INT_OF_NUM_LE;INT_OF_NUM_LT] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < 8 ==> n <= 7`] THEN
  CONV_TAC SAIL_HL_X86_STRICT_LET_CONV;;

let SAIL_HL_X86_GPR_TAC definitions facts width legacy unary instruction =
  let source = mk_finty(num width) in
  let sign = CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE[source,`:N`] MSB_IVAL) in
  REPEAT GEN_TAC THEN
  (if legacy then
    MAP_EVERY (fun name ->
      MP_TAC(ISPEC (parse_term(name ^ ":3 word")) VAL_BOUND))
      (if unary then ["d"] else ["d";"m"]) THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT DISCH_TAC THEN
    ASM_CASES_TAC `4 <= val(d:3 word)` THEN
    (if unary then ALL_TAC else ASM_CASES_TAC `4 <= val(m:3 word)`)
   else ALL_TAC) THEN
  SAIL_HL_X86_REWRITE_TAC(definitions @
    [instruction;GPR8;GPR16;GPR32_Z;GPR64;
     assign;SEQ;UNDEFINED_VALUES;SEQ_ID;ASSIGNS_THM;FST;SND;OUTL;OUTR;
     READ_SHORT;WRITE_SHORT;READ_ZEROTOP_32;WRITE_ZEROTOP_32;
     GSYM WORD_IWORD;WORD_VAL;SAIL_HL_X86_JOIN_ZERO;WORD_ZX_BITVAL;
     SAIL_HL_X86_LOW_SUBWORD `:8`;SAIL_HL_X86_LOW_SUBWORD source]) THEN
  CONV_TAC SAIL_HL_X86_STRICT_LET_CONV THEN
  SAIL_HL_X86_GPR_REGISTER_FIELDS_TAC THEN
  REWRITE_TAC[OUTL;OUTR;FST;SND;GSYM WORD_IWORD;WORD_VAL] THEN
  CONV_TAC SAIL_HL_X86_STRICT_LET_CONV THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LE;INT_OF_NUM_LT] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < 8 ==> n <= 7`] THEN
  REWRITE_TAC SAIL_HL_X86_GPR_SHORT_REWRITES THEN
  CONV_TAC SAIL_HL_X86_STRICT_LET_CONV THEN
  REWRITE_TAC[OUTL;OUTR;FST;SND;GSYM WORD_IWORD;WORD_VAL] THEN
  CONV_TAC SAIL_HL_X86_STRICT_LET_CONV THEN
  REWRITE_TAC[BIT_WORD_0;BIT_WORD_BITVAL;BIT_WORD_NOT;BIT_WORD_XOR;
    BIT_WORD_AND;BIT_WORD_OR;BIT_WORD_SUBWORD;BIT_WORD_ZX] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC(WORD_ZX_BITVAL :: facts) THEN
  REWRITE_TAC[ADD_CLAUSES;INT_ADD_RID;INT_ADD_LID] THEN
  REWRITE_TAC[WORD_RULE
    `word_sub (word_sub x y) z:N word = word_sub x (word_add y z)`] THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC SAIL_HL_X86_GPR_INSERT_REWRITES THEN
  REWRITE_TAC[GSYM word_zx;WORD_ZX_TRIVIAL] THEN
  REWRITE_TAC[GSYM sign;GSYM SAIL_HL_X86_GPR_PARITY_BITS;
    BIT_WORD_AND;BIT_WORD_OR;BIT_WORD_XOR;BIT_WORD_NOT;
    BIT_WORD_SUBWORD;BIT_WORD_ZX] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_SUB_LZERO;VAL_WORD_0;IVAL_WORD_0;INT_SUB_LZERO;
    SAIL_HL_X86_NEG_CARRY] THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
  REWRITE_TAC[SAIL_HL_X86_ARBITRARY_BIT0] THEN
  SAIL_HL_X86_GPR_REGISTER_FIELDS_TAC THEN
  (* Decoding and partial-register normalization can expose a full-register
     sign observation after the first flag pass. Reapply the same proved
     facts before comparing the ordered writes; no value or flag is omitted. *)
  REWRITE_TAC facts THEN
  REWRITE_TAC[WORD_AND_SYM;CONJ_SYM] THEN
  (REFL_TAC ORELSE PRINT_GOAL_TAC);;

let SAIL_HL_X86_GPR_CLAIM definitions facts width legacy
    (operation,instruction,unary) =
  let bits = if legacy then 3 else 4 in
  let operands = if unary then "R" else "RR" in
  let root = Printf.sprintf "X86_%s%d%s_%s" operation width
    (if legacy then "_LEGACY" else "") operands in
  let constant = "sail_hl_" ^
    String.concat "_5f" (String.split_on_char '_' root) in
  let arguments = if unary then "d" else "d m" in
  let components = SAIL_HL_X86_GPR_COMPONENT width legacy "d" ^
    (if unary then "" else
      " " ^ SAIL_HL_X86_GPR_COMPONENT width legacy "m") in
  let statement = parse_term(Printf.sprintf
    "!%s:%d word. !s t:x86state. %s %s s t <=> x86_%s %s s t"
    arguments bits constant arguments operation components) in
  let name = "SAIL_HL_" ^ root ^ "_EQ" in
  print_endline(name ^ " starting");
  let started = Sys.time() in
  let theorem = prove(statement,
    SAIL_HL_X86_GPR_TAC definitions facts width legacy unary instruction) in
  Printf.printf "CPU: %.3fs\n%!" (Sys.time() -. started);
  name,theorem;;

let SAIL_HL_X86_GPR_PROOFS definitions widths =
  let facts = map (fun width -> width,SAIL_HL_X86_GPR_PROOF_FACTS width)
    widths in
  List.concat_map (fun (operation,_,_ as instruction) ->
    List.concat_map (fun width ->
      if mem operation ["ADCX";"ADOX"] && width <> 32 && width <> 64
      then [] else
      let encodings = if width = 8 then [false;true] else [false] in
      map (fun legacy ->
        SAIL_HL_X86_GPR_CLAIM definitions (assoc width facts)
          width legacy instruction) encodings) widths)
    SAIL_HL_X86_GPR_OPERATIONS;;
