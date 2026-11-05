(* Register shifts and rotates, with an eight-bit count.
   Sail masks that count to six bits for 64-bit operands and five bits for
   smaller operands. Zero, one and the other masked counts
   determine which flags are preserved, calculated or left arbitrary.
   Each theorem compares every final state, with no alias restrictions or
   assumptions about initial flags, upper register bits or other state.
   Instruction fetch and acquisition of a count from CL are not covered.

   The source single shifts are exec_shl/exec_shr/exec_sar in
   model/insn_groups.sail; the double shifts are exec_shld/exec_shrd in
   model/insn_baseline.sail. Keep word calculations symbolic, discharge
   their index assertions from the count mask, and preserve independent
   choices for every undefined flag. The 35 agreement claims cover every
   matching form in the generated 41-form catalogue. For the six 8- and
   16-bit carry rotates, an _EXACT theorem states shina's relation in
   terms of s2n-bignum's, and x86-rcl-rcr-claims.ml derives a closed
   counterexample to equality from it. No claim restricts the supplied
   count to avoid an undefined result or flag.

   Narrow reads and writes use the existing GPR components. A 32-bit write
   clears the upper half even at count zero. REX byte forms address low
   bytes; legacy fields 4..7 address AH/CH/DH/BH. Every theorem includes
   these partial-register effects and preserves the remaining state. *)
needs "tools/sail/proofs/report.ml";;
needs "tools/sail/proofs/x86-arithmetic-lemmas.ml";;
needs "tools/sail/proofs/x86-gpr-lemmas.ml";;
needs "tools/sail/proofs/proof-fork.ml";;

loadt "tools/sail/_build/x86-shift.ml";;

(* Zero extension preserves zero tests when the target is wide enough.
   Sail's Boolean selectors use a 512-bit OR-reduction circuit. *)
let SAIL_HL_X86_ZX_EQ_ZERO = prove
 (`!w:N word.
   dimindex(:N) <= dimindex(:M)
   ==> ((word_zx w:M word) = word 0 <=> w = word 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN
  ASM_SIMP_TAC[VAL_WORD_ZX]);;

let SAIL_HL_X86_ZX6_EQ_ZERO = CONV_RULE
  (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
  (INST_TYPE [`:6`,`:N`;`:512`,`:M`] SAIL_HL_X86_ZX_EQ_ZERO);;

let SAIL_HL_X86_COUNT6_CHOICES = prove
 (`!k:num. k < 64 ==>
   ((word k:6 word) = word 0 <=> k = 0) /\
   ((word k:6 word) = word 1 <=> k = 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ; CONG] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;

let SAIL_HL_X86_ROTATE_COMPLEMENT_COUNT = prove
 (`!k:num. k < 64 ==> num_of_int (&64 - &k) = 64 - k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k <= 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[INT_OF_NUM_SUB; NUM_OF_INT_OF_NUM]);;

let SAIL_HL_X86_NOT_BOOLEAN_WORD = prove
 (`!p:bool.
   word_not(word(bitval p):1 word) = word(bitval(~p))`,
  GEN_TAC THEN BOOL_CASES_TAC `p:bool` THEN
  REWRITE_TAC[bitval] THEN CONV_TAC WORD_REDUCE_CONV);;

let SAIL_HL_X86_BLEND_BIT1 = REWRITE_RULE[WORD_SX_TRIVIAL]
  (INST_TYPE [`:1`,`:N`] SAIL_HL_X86_BLEND_MASK);;

let SAIL_HL_X86_COMPLEMENT_COUNT = prove
 (`!width k. k <= width ==>
   num_of_int (&width - &k) = width - k`,
  SIMP_TAC[INT_OF_NUM_SUB; NUM_OF_INT_OF_NUM]);;

let SAIL_HL_X86_ROTATE_SHIFT_SYMBOLIC =
  map (fun theorem -> CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [`:64`,`:N`] (GSYM theorem)))
    [WORD_ROL_SHIFTS; WORD_ROR_SHIFTS];;

(* Prove Sail's nonzero circuit once with an opaque input. Its nine stages
   use each previous OR result twice. Substituting a large instruction
   expression through those stages first would duplicate it exponentially.
   Retain the original LET body as a rewrite, so it is contracted before
   evaluating the enclosing instruction's bindings. *)
let SAIL_HL_X86_SHIFT_OR_REDUCE = prove
 (`!x:N word.
   sail_hl_shared_x86_2dshift_or_5freduce_5f6 x =
   (word(bitval(~((word_zx x:512 word) = word 0))):1 word)`,
  REWRITE_TAC[sail_hl_shared_x86_2dshift_or_5freduce_5f6;
    sail_hl_shared_x86_2dshift_zero_5fextend_5f5; NUM_OF_INT_OF_NUM] THEN
  CONV_TAC SAIL_HL_X86_STRICT_LET_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_OR_REDUCTION_512] THEN REFL_TAC);;

let SAIL_HL_X86_SHIFT_OR_BODY = REWRITE_RULE
  [sail_hl_shared_x86_2dshift_or_5freduce_5f6;
   sail_hl_shared_x86_2dshift_zero_5fextend_5f5; NUM_OF_INT_OF_NUM]
  SAIL_HL_X86_SHIFT_OR_REDUCE;;

(* Resolve component reads before copying a binding into later bindings.
   All steps are kernel conversions. As in the shared LET conversion,
   conditional factoring is restricted to tuples and word_insert; it must
   not move a conditional inside a numeral or obscure a word mask.
   Paired lets use the shared schema-based tuple beta conversion, falling
   back to GEN_BETA_CONV, which substitutes through the body once per field.
   The vacuous-quantifier rewrites EXISTS_SIMP and FORALL_SIMP apply only
   after vfree_in finds no occurrence: their matcher instead renames the
   bound variable and scans the whole body before failing. Both changes
   give the same theorems up to bound-variable names. *)
let SAIL_HL_X86_SHIFT_LET_CONV term =
  let cache = Sail_hl_x86_term_identity.create 1024 in
  let tuple_beta = SAIL_HL_TUPLE_APPLY_CONV ~contract_result:true () in
  let vacuous_rewrites = map (concl o SPEC_ALL) [EXISTS_SIMP; FORALL_SIMP] in
  let vacuous term =
    match term with
    | Comb(Const(("?" | "!"),_),Abs(v,body)) when not (vfree_in v body) ->
        (REWR_CONV EXISTS_SIMP ORELSEC REWR_CONV FORALL_SIMP) term
    | _ -> failwith "shift let: not a vacuous quantifier" in
  let factor = REWR_CONV (GSYM COND_RAND) in
  let common_application term =
    (match term with
     | Comb(Comb(Comb(Const("COND",_),_),_),_) -> ()
     | _ -> failwith "shift let: not a conditional");
    let theorem = factor term in
    match fst(strip_comb(rand(concl theorem))) with
    | Const(",",_) | Const("word_insert",_) -> theorem
    | _ -> failwith "shift let: not a shared application" in
  let beta term =
    match term with
    | Comb(Abs(_,_),_) -> BETA_CONV term
    | Comb(Comb(Const("GABS",_),_),_) ->
        (tuple_beta ORELSEC GEN_BETA_CONV) term
    | _ -> failwith "shift let: not an abstraction application" in
  let basic = REWR_CONV SAIL_HL_X86_SHIFT_OR_BODY
    ORELSEC COMPONENT_READ_OVER_WRITE_CONV ORELSEC common_application
    ORELSEC GEN_REWRITE_CONV I (LET_END_DEF :: filter (fun theorem ->
      not (exists (aconv (concl theorem)) vacuous_rewrites)) (basic_rewrites()))
    ORELSEC vacuous in
  let rec normalize term =
    try Sail_hl_x86_term_identity.find cache term with Not_found ->
    let theorem =
    ((CHANGED_CONV basic ORELSEC beta ORELSEC
      (fun term -> match term with
       | Comb(Comb(Const("LET",_),_),_) ->
           (RAND_CONV normalize THENC REWR_CONV LET_DEF THENC beta) term
       | _ -> failwith "shift let: not a LET"))
     THENC normalize ORELSEC
     (CHANGED_CONV (SUB_CONV normalize) THENC normalize) ORELSEC REFL) term in
    let left = lhand(concl theorem) in
    if hyp theorem <> [] || not(aconv left term) then
      failwith "shift let cache: open or mismatched equality";
    let theorem = if left = term then theorem
      else TRANS(ALPHA term left) theorem in
    Sail_hl_x86_term_identity.add cache term theorem;
    theorem in
  normalize term;;

let SAIL_HL_X86_ROTATE_TAC definitions =
  REPEAT GEN_TAC THEN
  SAIL_HL_X86_REWRITE_TAC(definitions @
    [assign; SEQ; UNDEFINED_VALUES; SEQ_ID; ASSIGNS_SEQ; ASSIGNS_THM;
     FST; SND; OUTL; OUTR]) THEN
  CONV_TAC SAIL_HL_X86_SHIFT_LET_CONV THEN
  REWRITE_TAC[FST; SND; OUTL; OUTR; GSYM WORD_IWORD; WORD_VAL;
              INT_OF_NUM_REM; NUM_OF_INT_OF_NUM; MOD_MOD_REFL] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  SUBGOAL_THEN `val(count:8 word) MOD 64 < 64` ASSUME_TAC THENL
    [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_SIMP_TAC[SAIL_HL_X86_ROTATE_COMPLEMENT_COUNT] THEN
  ASM_SIMP_TAC(SAIL_HL_X86_ROTATE_SHIFT_SYMBOLIC @
    [ARITH_RULE `k < 64 ==> k <= 64`]) THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC[BIT_WORD_BITVAL; DIMINDEX_1;
              SAIL_HL_X86_OR_REDUCTION_512] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_ZX6_EQ_ZERO; WORD_XOR_EQ_0] THEN
  ASM_SIMP_TAC[SAIL_HL_X86_COUNT6_CHOICES] THEN
  REWRITE_TAC[SAIL_HL_X86_NOT_BOOLEAN_WORD;
              SAIL_HL_X86_BLEND_MASK; SAIL_HL_X86_BLEND_BIT1] THEN
  ASM_CASES_TAC `val(count:8 word) MOD 64 = 0` THENL
   [ASM_REWRITE_TAC[WORD_ROL_ZERO; WORD_ROR_ZERO];
    ASM_CASES_TAC `val(count:8 word) MOD 64 = 1` THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[BIT_WORD_XOR; BIT_WORD_BITVAL; DIMINDEX_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
  REWRITE_TAC[SAIL_HL_X86_ARBITRARY_BIT0; EXISTS_SIMP; EQ_SYM_EQ] THEN
  REFL_TAC;;

(* The source computes unsigned comparisons by subtracting zero-extended
   operands and observing the extra sign bit. The masked 64-bit count fits
   in seven bits; this equation removes its unreachable overflow branches
   without assuming anything about the supplied eight-bit count. *)
let SAIL_HL_X86_SHIFT_GT7 = prove
 (`!a:7 word. !b:7 word.
   bit 7 (word_sub (word_zx b:8 word) (word_zx a)) <=>
   val b < val a`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`b:7 word`; `a:7 word`; `F`]
    (SAIL_HL_X86_DIFFERENCE_AT `:7` `:8`)) THEN
  REWRITE_TAC[BITVAL_CLAUSES; INT_OF_NUM_CLAUSES; INT_ADD_RID; ADD_CLAUSES;
              WORD_SUB_0] THEN DISCH_TAC THEN
  REWRITE_TAC[CONV_RULE NUM_REDUCE_CONV
    (REWRITE_RULE[DIMINDEX_8] (INST_TYPE [`:8`,`:N`] MSB_IVAL))] THEN
  ASM_REWRITE_TAC[INT_ARITH `x-y:int < &0 <=> x < y`;
                  INT_OF_NUM_LT]);;

let SAIL_HL_X86_SHIFT_WORD7 = prove
 (`!k. k < 64 ==> val(word k:7 word) = k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `k < 64 ==> k < 128`]);;

(* SAR remains defined when the count exceeds the operand width: fill with
   the sign bit and take CF from that same bit. Sail clamps the carry index
   with min_u; HOL's arithmetic shift has the equivalent sign-fill rule.
   These identities cover arbitrary natural counts before the instruction
   proof introduces its mask. They do not enumerate operand bits. *)
let SAIL_HL_X86_SAR_CF = prove
 (`!x:N word. !k.
   bit 0 (word_ishr x k) <=> bit (MIN k (dimindex(:N)-1)) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_WORD_ISHR;ADD_CLAUSES] THEN
  ASM_CASES_TAC `k < dimindex(:N)` THEN
  ASM_SIMP_TAC[MIN;DIMINDEX_GE_1;LE_1;
    ARITH_RULE `k < n ==> k <= n-1`;
    ARITH_RULE `1 <= n /\ ~(k < n) ==> ~(k <= n-1)`]);;

let SAIL_HL_X86_SAR_MIN_VALUE = prove
 (`!k bound. k < 64 /\ bound < 64 ==>
   val(if bound < k then (word bound:7 word) else word k) = MIN k bound`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MIN;ARITH_RULE `k <= bound <=> ~(bound < k)`] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[SAIL_HL_X86_SHIFT_WORD7]);;

let SAIL_HL_X86_SAR_MIN_BOUND = prove
 (`!width k. 0 < width ==> MIN k (width-1) < width`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MIN] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* A positive count below the width gives the last bit shifted out.
   At the width or above, SHL/SHR leave CF arbitrary instead; SAR keeps
   the sign-fill carry rule. These are word identities, not assumptions
   about instruction operands or counts. *)
let SAIL_HL_X86_NARROW_SHIFT_CF = prove
 (`!x:N word. !k. 0 < k /\ k < dimindex(:N) ==>
   (bit (dimindex(:N)-1) (word_shl x (k-1)) <=>
    bit (dimindex(:N)-k) x) /\
   (bit 0 (word_ushr x (k-1)) <=> bit (k-1) x)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[BIT_WORD_SHL;BIT_WORD_USHR;ADD_CLAUSES;DIMINDEX_GE_1;
    ARITH_RULE `1 <= n ==> n-1 < n`;
    ARITH_RULE `0 < k /\ k < n ==> k-1 <= n-1 /\ k-1 < n`;
    ARITH_RULE `0 < k /\ k < n ==> n-1-(k-1) = n-k`]);;

let SAIL_HL_X86_NARROW_SHIFT_LEFT_INDEX = prove
 (`!width k. 0 < k /\ k <= width /\ width <= 64 ==>
   num_of_int (((&width + &64) - &k) rem &64) = width-k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&width + &64) - &k:int = &(64+(width-k))`
    SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_ADD;GSYM INT_OF_NUM_SUB] THEN INT_ARITH_TAC;
    REWRITE_TAC[INT_OF_NUM_REM;NUM_OF_INT_OF_NUM] THEN
    ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    REWRITE_TAC[MOD_REFL;ADD_CLAUSES;MOD_MOD_REFL] THEN
    ASM_SIMP_TAC[MOD_LT;ARITH_RULE
      `0 < k /\ k <= width /\ width <= 64 ==> width-k < 64`]]);;

let SAIL_HL_X86_NARROW_SHL_SIGN_ONE = prove
 (`!x:N word. 2 <= dimindex(:N) ==>
   (bit (dimindex(:N)-1) (word_shl x 1) <=>
    bit (dimindex(:N)-2) x)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[BIT_WORD_SHL;
    ARITH_RULE `2 <= n ==> n-1 < n /\ 1 <= n-1 /\ (n-1)-1 = n-2`]);;

let SAIL_HL_X86_NARROW_DOUBLE_RESULT = prove
 (`!w:(N tybit0)word. !k. k <= dimindex(:N) ==>
   (word_subword (word_shl w k) (dimindex(:N),dimindex(:N)):N word) =
   word_subword w (dimindex(:N)-k,dimindex(:N))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT;BIT_WORD_SUBWORD;BIT_WORD_SHL;
    DIMINDEX_TYBIT0] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= n ==> k <= n+i`;
    ARITH_RULE `i < n ==> n+i < 2*n`;
    ARITH_RULE `k <= n ==> (n+i)-k = (n-k)+i`]);;

let SAIL_HL_X86_NARROW_DOUBLE_CF = prove
 (`!x y:N word. !k. 0 < k /\ k <= dimindex(:N) ==>
   (bit (2*dimindex(:N)-k) (word_join x y:(N tybit0)word) <=>
    bit (dimindex(:N)-k) x)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[BIT_WORD_JOIN;DIMINDEX_TYBIT0;
    ARITH_RULE `0 < k /\ k <= n ==> 2*n-k < 2*n /\ ~(2*n-k < n)`;
    ARITH_RULE `k <= n ==> (2*n-k)-n = n-k`]);;

let SAIL_HL_X86_NARROW_DOUBLE_RIGHT_RESULT = prove
 (`!w:(N tybit0)word. !k.
   (word_subword (word_ushr w k) (0,dimindex(:N)):N word) =
   word_subword w (k,dimindex(:N))`,
  REWRITE_TAC[WORD_EQ_BITS_ALT;BIT_WORD_SUBWORD;BIT_WORD_USHR;
    ADD_CLAUSES;ADD_SYM]);;

let SAIL_HL_X86_NARROW_DOUBLE_HALVES = prove
 (`!x y:N word.
   (word_subword (word_join x y:(N tybit0)word)
     (dimindex(:N),dimindex(:N)):N word) = x /\
   (word_subword (word_join x y:(N tybit0)word)
     (0,dimindex(:N)):N word) = y`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT;BIT_WORD_SUBWORD;BIT_WORD_JOIN;
    DIMINDEX_TYBIT0] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ADD_CLAUSES;ADD_SUB;ADD_SUB2;MIN;LE_REFL;
    ARITH_RULE `i < n ==> n+i < 2*n /\ i < 2*n`;
    ARITH_RULE `~(n+i < n)`]);;

(* A generic word lemma at one width, with its dimensions evaluated. *)
let SAIL_HL_X86_SHIFT_AT width theorem =
  CONV_RULE (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [mk_finty(num width),`:N`] theorem);;

(* Sail uses h=k+bitval(k=0) when extracting carry. At zero this gives h=1
   so its index assertions remain true, even though the old carry flag is
   restored. Do not replace h by k before separating the zero-count case. *)
let SAIL_HL_X86_SHIFT_LEFT_INDEX width =
  CONV_RULE (NUM_REDUCE_CONV THENC INT_REDUCE_CONV)
    (SPEC (mk_small_numeral width) SAIL_HL_X86_NARROW_SHIFT_LEFT_INDEX);;

(* The generic shift facts at width 64 or 32. *)
let SAIL_HL_X86_SHIFT_FACTS width =
  let at = SAIL_HL_X86_SHIFT_AT width in
  at SAIL_HL_X86_NARROW_SHIFT_CF, at SAIL_HL_X86_SAR_CF,
  SAIL_HL_X86_SHIFT_LEFT_INDEX width,
  REWRITE_RULE[] (at SAIL_HL_X86_NARROW_SHL_SIGN_ONE),
  at SAIL_HL_X86_NARROW_DOUBLE_RESULT, at SAIL_HL_X86_NARROW_DOUBLE_CF,
  at SAIL_HL_X86_NARROW_DOUBLE_RIGHT_RESULT,
  at SAIL_HL_X86_NARROW_DOUBLE_HALVES;;

let SAIL_HL_X86_SHIFT_SIGN64 =
  CONV_RULE NUM_REDUCE_CONV
    (REWRITE_RULE[DIMINDEX_64] (INST_TYPE [`:64`,`:N`] MSB_IVAL));;

let SAIL_HL_X86_SHIFT_PARITY64 =
  CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE
    [LET_DEF; LET_END_DEF; BIT_WORD_NOT; BIT_WORD_XOR; BIT_WORD_SUBWORD;
     BIT_WORD_ZX; DIMINDEX_1; DIMINDEX_2; DIMINDEX_4; DIMINDEX_8; DIMINDEX_64]
    (GEN `z:64 word`
      (SPEC `word_zx(z:64 word):8 word` SAIL_HL_X86_PARITY8)));;

let SAIL_HL_X86_ARITHMETIC_SHIFT64 = SAIL_HL_X86_ARITHMETIC_SHIFT 64;;

(* Conditional flag choices expose assignment lambdas after the count
   case has been selected. Sequence those lambdas directly; a havoc still
   quantifies over every value of the written component. These equations
   also handle zero-count flag self-writes without assuming any old flag. *)
let SAIL_HL_X86_SHIFT_ASSIGN_SEQUENCE = prove
 (`!c:(S,V)component. !y:V. !r:S->T->bool. !s:S. !t:T.
   ((\u:S. \v:S. v = write c y u) ,, r) s t <=>
   r (write c y s) t`,
  REWRITE_TAC[seq] THEN MESON_TAC[]);;

let SAIL_HL_X86_SHIFT_HAVOC_SEQUENCE = prove
 (`!c:(S,V)component. !r:S->T->bool. !s:S. !t:T.
   ((\u:S. \v:S. ?y:V. v = write c y u) ,, r) s t <=>
   (?y:V. r (write c y s) t)`,
  REWRITE_TAC[seq] THEN MESON_TAC[]);;

(* The same normalization proves all five shifts. First contract helpers
   and capture register/flag reads. Derive the count bound from MOD, then
   split only zero, one and the other masked counts. This keeps the source
   carry index h=k+bitval(k=0) valid at zero. The source's assertions and
   out-of-range alternatives disappear only after their guards are proved.

   Finally sequence the chosen flag relations, normalize independent
   writes, and remove choices only when they no longer occur. AF remains
   arbitrary for positive counts; OF remains arbitrary for counts above
   one. Expanding bit observations after slicing lets the double shifts
   use the same parity and sign facts without expanding whole operands. *)
let SAIL_HL_X86_SCALAR_SHIFT_TAC definitions =
  let single_cf,sar_cf,left_index,sign_one,
      double_result,double_cf,double_right,double_halves =
    SAIL_HL_X86_SHIFT_FACTS 64 in
  REPEAT GEN_TAC THEN
  SAIL_HL_X86_REWRITE_TAC(definitions @
    [assign; SEQ; UNDEFINED_VALUES; SEQ_ID; ASSIGNS_SEQ; ASSIGNS_THM;
     FST; SND; OUTL; OUTR]) THEN
  CONV_TAC SAIL_HL_X86_SHIFT_LET_CONV THEN
  REWRITE_TAC[FST; SND; OUTL; OUTR; GSYM WORD_IWORD; WORD_VAL;
              INT_OF_NUM_REM; NUM_OF_INT_OF_NUM; MOD_MOD_REFL;
              WORD_ZX_TRIVIAL; WORD_SX_TRIVIAL;
              SAIL_HL_X86_SHIFT_GT7] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  SUBGOAL_THEN `val(count:8 word) MOD 64 < 64` ASSUME_TAC THENL
    [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC[BIT_WORD_BITVAL; VAL_WORD_BITVAL; DIMINDEX_1;
              SAIL_HL_X86_OR_REDUCTION_512] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_ZX6_EQ_ZERO; WORD_XOR_EQ_0] THEN
  ASM_SIMP_TAC[SAIL_HL_X86_COUNT6_CHOICES;
               SAIL_HL_X86_SHIFT_WORD7] THEN
  REWRITE_TAC[SAIL_HL_X86_NOT_BOOLEAN_WORD;
              SAIL_HL_X86_BLEND_MASK; SAIL_HL_X86_BLEND_BIT1;
              SAIL_HL_X86_SHIFT_GT7; VAL_WORD_BITVAL;
              INT_OF_NUM_ADD; GSYM WORD_IWORD] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  ASM_SIMP_TAC[SAIL_HL_X86_SHIFT_WORD7;
               SAIL_HL_X86_ARITHMETIC_SHIFT64;
               double_result; double_right;
               ARITH_RULE `k < 64 ==> k <= 64`] THEN
  ASM_CASES_TAC `val(count:8 word) MOD 64 = 0` THENL
   [ASM_REWRITE_TAC[BITVAL_CLAUSES; WORD_SHL_ZERO; WORD_USHR_ZERO;
                    WORD_ISHR_ZERO];
    ASM_CASES_TAC `val(count:8 word) MOD 64 = 1` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES]] THEN
  ASM_SIMP_TAC[SAIL_HL_X86_COMPLEMENT_COUNT;
    left_index; SAIL_HL_X86_SHIFT_WORD7; single_cf; sar_cf; double_cf;
    ARITH_RULE `k < 64 ==> k <= 64 /\ MIN (k - 1) 63 = k - 1`;
    ARITH_RULE `~(k=0) ==> 0 < k`;
    ARITH_RULE `~(k=0) ==> 1 <= k`;
    ARITH_RULE `~(k=0) /\ k < 64 ==> k-1 < 64`;
    ARITH_RULE `~(k=0) /\ k < 64 ==> ~(63 < k-1)`;
    ARITH_RULE `k < 64 ==> ~(64 < k)`;
    INT_OF_NUM_ADD; INT_OF_NUM_SUB; INT_OF_NUM_LT;
    INT_OF_NUM_LE; NUM_OF_INT_OF_NUM; ADD_CLAUSES;
    GSYM WORD_IWORD] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[BIT_WORD_NOT; BIT_WORD_XOR; BIT_WORD_SUBWORD; BIT_WORD_ZX;
    BIT_WORD_BITVAL; DIMINDEX_1; DIMINDEX_2; DIMINDEX_4; DIMINDEX_8;
    DIMINDEX_64; ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_JOIN_ZERO; SAIL_HL_X86_ZERO64;
    SAIL_HL_X86_SHIFT_PARITY64; GSYM SAIL_HL_X86_SHIFT_SIGN64;
    sign_one; double_halves] THEN
  REWRITE_TAC[BIT_WORD_XOR; BIT_WORD_BITVAL; DIMINDEX_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_SHIFT_ASSIGN_SEQUENCE;
              SAIL_HL_X86_SHIFT_HAVOC_SEQUENCE] THEN
  REWRITE_TAC[SEQ; SEQ_ID; ASSIGNS_SEQ] THEN
  REWRITE_TAC[assign; ASSIGNS_THM] THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
  REWRITE_TAC[SAIL_HL_X86_SHIFT_ASSIGN_SEQUENCE;
              SAIL_HL_X86_SHIFT_HAVOC_SEQUENCE] THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
  REWRITE_TAC[SAIL_HL_X86_ARBITRARY_BIT0; EXISTS_SIMP; EQ_SYM_EQ] THEN
  REWRITE_TAC[SAIL_HL_X86_SHIFT_ASSIGN_SEQUENCE;
              SAIL_HL_X86_SHIFT_HAVOC_SEQUENCE] THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; WORD_SHL_ZERO; WORD_USHR_ZERO;
    WORD_ISHR_ZERO; BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_NOT; BIT_WORD_XOR;
    BIT_WORD_0; BIT_WORD_1; BIT_WORD_BITVAL; DIMINDEX_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[INT_GE; INT_GT; INT_OF_NUM_LE; INT_OF_NUM_LT;
    INT_OF_NUM_SUB; ARITH_RULE `~(k=0) ==> 1 <= k`;
    ARITH_RULE `k < 64 ==> k <= 64`;
    ARITH_RULE `k < 64 ==> k <= 128`] THEN
  REWRITE_TAC[GSYM WORD_IWORD] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[SAIL_HL_X86_SHIFT_WORD7;
    ARITH_RULE `k < 64 ==> k-1 < 64`;
    ARITH_RULE `k < 64 ==> ~(63 < k-1)`] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; VAL_WORD_0; VAL_WORD_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[double_cf; single_cf; sar_cf;
    ARITH_RULE `k < 64 ==> k <= 64 /\ MIN (k - 1) 63 = k - 1`;
    ARITH_RULE `~(k=0) ==> 0 < k`] THEN
  REWRITE_TAC[GSYM SAIL_HL_X86_SHIFT_PARITY64;
    BIT_WORD_SUBWORD; BIT_WORD_ZX; BIT_WORD_JOIN; DIMINDEX_64;
    DIMINDEX_128; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_ARBITRARY_BIT0; EXISTS_SIMP; EQ_SYM_EQ] THEN
  (REFL_TAC ORELSE
   (CONV_TAC(LAND_CONV(GEN_REWRITE_CONV I [SWAP_EXISTS_THM])) THEN REFL_TAC));;

(* Narrow rotates use the same word-rotation equations as the 64-bit forms.
   Preserve the original five-bit masked count when deciding OF: rotating
   an eight-bit word by eight does not make the instruction's count zero.
   Reduce modulo the word width only inside the word rotation. *)
let SAIL_HL_X86_NARROW_ROTATE_TAC width legacy definitions =
  let dimension = mk_finty(num width) in
  let rotations = map (fun theorem -> CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [dimension,`:N`] (GSYM theorem)))
    [WORD_ROL_SHIFTS; WORD_ROR_SHIFTS] in
  let low_read = GSYM(CONV_RULE(DEPTH_CONV DIMINDEX_CONV)
    (INST_TYPE[dimension,`:M`] WORD_ZX_SUBWORD)) in
  let mods = if width = 32 then [] else map (fun theorem -> CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE[dimension,`:N`] (GSYM theorem)))
    [WORD_ROL_MOD;WORD_ROR_MOD] in
  REPEAT GEN_TAC THEN
  (if legacy then
    MP_TAC(ISPEC `d:3 word` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN ASM_CASES_TAC `4 <= val(d:3 word)`
   else ALL_TAC) THEN
  SAIL_HL_X86_REWRITE_TAC(definitions @
    [GPR8;GPR16;GPR32;GPR32_Z;assign;SEQ;UNDEFINED_VALUES;SEQ_ID;
     ASSIGNS_SEQ;ASSIGNS_THM;FST;SND;OUTL;OUTR]) THEN
  CONV_TAC SAIL_HL_X86_SHIFT_LET_CONV THEN
  REWRITE_TAC[FST;SND;OUTL;OUTR;GSYM WORD_IWORD;WORD_VAL;
    INT_OF_NUM_REM;NUM_OF_INT_OF_NUM;MOD_MOD_REFL;
    INT_GE;INT_GT;INT_OF_NUM_LT;INT_OF_NUM_LE] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < 8 ==> n <= 7`] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  (SUBGOAL_THEN `val(count:8 word) MOD 32 < 32` ASSUME_TAC THENL
    [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV;ALL_TAC] THEN
   SUBGOAL_THEN
    (parse_term(Printf.sprintf "val(count:8 word) MOD 32 MOD %d < %d"
                  width width)) ASSUME_TAC THENL
    [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV;ALL_TAC]) THEN
  REWRITE_TAC SAIL_HL_X86_GPR_SHORT_REWRITES THEN
  CONV_TAC SAIL_HL_X86_SHIFT_LET_CONV THEN
  ASM_SIMP_TAC[SAIL_HL_X86_COMPLEMENT_COUNT;LT_IMP_LE] THEN
  ASM_SIMP_TAC(rotations @ mods @ [LT_IMP_LE]) THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC[BIT_WORD_BITVAL;DIMINDEX_1;SAIL_HL_X86_OR_REDUCTION_512] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_ZX6_EQ_ZERO;WORD_XOR_EQ_0] THEN
  ASM_SIMP_TAC[SAIL_HL_X86_COUNT6_CHOICES;
              ARITH_RULE `k < 32 ==> k < 64`] THEN
  REWRITE_TAC[SAIL_HL_X86_NOT_BOOLEAN_WORD;
    SAIL_HL_X86_BLEND_MASK;SAIL_HL_X86_BLEND_BIT1] THEN
  (ASM_CASES_TAC `val(count:8 word) MOD 32 = 0` THENL
    [ASM_REWRITE_TAC[WORD_ROL_ZERO;WORD_ROR_ZERO];
     ASM_CASES_TAC `val(count:8 word) MOD 32 = 1` THEN ASM_REWRITE_TAC[]]) THEN
  REWRITE_TAC[BIT_WORD_XOR;BIT_WORD_BITVAL;DIMINDEX_1;low_read] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  ASM_SIMP_TAC[ARITH_RULE `n < 8 ==> n <= 7`] THEN
  CONV_TAC SAIL_HL_X86_SHIFT_LET_CONV THEN
  REWRITE_TAC SAIL_HL_X86_GPR_INSERT_REWRITES THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
  REWRITE_TAC(mods @
    [SAIL_HL_X86_ARBITRARY_BIT0;EXISTS_SIMP;EQ_SYM_EQ;
     low_read;GSYM word_zx]) THEN
  REFL_TAC;;

(* The five-bit mask makes every 32-bit shift count smaller than its
   operand width. This discharges the source's carry-index assertions and
   excludes the large-count differences recorded for narrower SHL/SHR and
   double shifts. Keep source and destination registers unconstrained. *)
let SAIL_HL_X86_SHIFT32_FLAGS = SAIL_HL_X86_GPR_FLAG_REWRITES 32;;
let SAIL_HL_X86_SHIFT_ZERO32 = el 7 SAIL_HL_X86_SHIFT32_FLAGS;;
let SAIL_HL_X86_SHIFT_SIGN32 = el 8 SAIL_HL_X86_SHIFT32_FLAGS;;
let SAIL_HL_X86_SHIFT_PARITY32 = last SAIL_HL_X86_SHIFT32_FLAGS;;

let SAIL_HL_X86_SHIFT32_WORD7 = prove
 (`!k. k < 32 ==> val(word k:7 word) = k`,
  SIMP_TAC[SAIL_HL_X86_SHIFT_WORD7;
           ARITH_RULE `k < 32 ==> k < 64`]);;

let SAIL_HL_X86_SHIFT32_COUNT_CHOICES = prove
 (`!k. k < 32 ==>
   ((word k:6 word) = word 0 <=> k = 0) /\
   ((word k:6 word) = word 1 <=> k = 1)`,
  SIMP_TAC[SAIL_HL_X86_COUNT6_CHOICES;
           ARITH_RULE `k < 32 ==> k < 64`]);;

let SAIL_HL_X86_SHIFT32_TAC definitions =
  let single_cf,sar_cf,left_index,sign_one,
      double_result,double_cf,double_right,double_halves =
    SAIL_HL_X86_SHIFT_FACTS 32 in
  REPEAT GEN_TAC THEN
  SAIL_HL_X86_REWRITE_TAC(definitions @
    [GPR32_Z; assign; SEQ; UNDEFINED_VALUES; SEQ_ID;
     ASSIGNS_SEQ; ASSIGNS_THM; FST; SND; OUTL; OUTR]) THEN
  CONV_TAC SAIL_HL_X86_SHIFT_LET_CONV THEN
  REWRITE_TAC[FST; SND; OUTL; OUTR; GSYM WORD_IWORD; WORD_VAL;
    INT_OF_NUM_REM; NUM_OF_INT_OF_NUM; MOD_MOD_REFL;
    WORD_ZX_TRIVIAL; WORD_SX_TRIVIAL; SAIL_HL_X86_SHIFT_GT7] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  SUBGOAL_THEN `val(count:8 word) MOD 32 < 32` ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC SAIL_HL_X86_GPR_SHORT_REWRITES THEN
  CONV_TAC SAIL_HL_X86_SHIFT_LET_CONV THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC[BIT_WORD_BITVAL; VAL_WORD_BITVAL; DIMINDEX_1;
    SAIL_HL_X86_OR_REDUCTION_512] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_ZX6_EQ_ZERO; WORD_XOR_EQ_0] THEN
  ASM_SIMP_TAC[SAIL_HL_X86_SHIFT32_COUNT_CHOICES;
               SAIL_HL_X86_SHIFT32_WORD7] THEN
  REWRITE_TAC[SAIL_HL_X86_NOT_BOOLEAN_WORD; SAIL_HL_X86_BLEND_MASK;
    SAIL_HL_X86_BLEND_BIT1; SAIL_HL_X86_SHIFT_GT7; VAL_WORD_BITVAL;
    INT_OF_NUM_ADD; GSYM WORD_IWORD] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  ASM_SIMP_TAC[SAIL_HL_X86_SHIFT32_WORD7;
    SAIL_HL_X86_ARITHMETIC_SHIFT32;
    double_result; double_right;
    ARITH_RULE `k < 32 ==> k <= 32`] THEN
  ASM_CASES_TAC `val(count:8 word) MOD 32 = 0` THENL
   [ASM_REWRITE_TAC[BITVAL_CLAUSES; WORD_SHL_ZERO; WORD_USHR_ZERO;
                    WORD_ISHR_ZERO];
    ASM_CASES_TAC `val(count:8 word) MOD 32 = 1` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES]] THEN
  ASM_SIMP_TAC[SAIL_HL_X86_COMPLEMENT_COUNT;
    left_index; SAIL_HL_X86_SHIFT32_WORD7; single_cf; sar_cf; double_cf;
    ARITH_RULE `k < 32 ==> k <= 32 /\ MIN (k - 1) 31 = k - 1`;
    ARITH_RULE `~(k=0) ==> 0 < k /\ 1 <= k`;
    ARITH_RULE `~(k=0) /\ k < 32 ==> k-1 < 32`;
    ARITH_RULE `~(k=0) /\ k < 32 ==> ~(31 < k-1)`;
    ARITH_RULE `k < 32 ==> ~(32 < k)`;
    INT_OF_NUM_ADD; INT_OF_NUM_SUB; INT_OF_NUM_LT; INT_OF_NUM_LE;
    NUM_OF_INT_OF_NUM; ADD_CLAUSES; GSYM WORD_IWORD] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[BIT_WORD_NOT; BIT_WORD_XOR; BIT_WORD_SUBWORD; BIT_WORD_ZX;
    BIT_WORD_BITVAL; DIMINDEX_1; DIMINDEX_2; DIMINDEX_4; DIMINDEX_8;
    DIMINDEX_32; DIMINDEX_64; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_JOIN_ZERO; SAIL_HL_X86_SHIFT_ZERO32;
    SAIL_HL_X86_SHIFT_PARITY32; GSYM SAIL_HL_X86_SHIFT_SIGN32;
    sign_one; double_halves] THEN
  REWRITE_TAC[BIT_WORD_XOR; BIT_WORD_BITVAL; DIMINDEX_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_SHIFT_ASSIGN_SEQUENCE;
              SAIL_HL_X86_SHIFT_HAVOC_SEQUENCE; SEQ; SEQ_ID; ASSIGNS_SEQ] THEN
  REWRITE_TAC[assign; ASSIGNS_THM] THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC SAIL_HL_X86_GPR_INSERT_REWRITES THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
  REWRITE_TAC[SAIL_HL_X86_SHIFT_ASSIGN_SEQUENCE;
              SAIL_HL_X86_SHIFT_HAVOC_SEQUENCE;
              SAIL_HL_X86_ARBITRARY_BIT0; EXISTS_SIMP; EQ_SYM_EQ] THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
  ASM_SIMP_TAC[NUM_OF_INT_OF_NUM; BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_NOT;
    BIT_WORD_XOR; BIT_WORD_0; BIT_WORD_1; BIT_WORD_BITVAL; DIMINDEX_1;
    INT_GE; INT_GT; INT_OF_NUM_LE; INT_OF_NUM_LT; INT_OF_NUM_SUB;
    ARITH_RULE `~(k=0) ==> 1 <= k`; ARITH_RULE `k < 32 ==> k <= 96`;
    ARITH_RULE `k < 32 ==> k <= 32`] THEN
  REWRITE_TAC[GSYM WORD_IWORD] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[SAIL_HL_X86_SHIFT32_WORD7;
    ARITH_RULE `k < 32 ==> k-1 < 32`;
    ARITH_RULE `k < 32 ==> ~(31 < k-1)`;
    ARITH_RULE `k < 32 ==> k-1 < 64`;
    ARITH_RULE `32-k < 64`; ARITH_RULE `k < 32 ==> k < 64`] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; VAL_WORD_0; VAL_WORD_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[double_cf; single_cf; sar_cf;
    ARITH_RULE `k < 32 ==> k <= 32 /\ MIN (k - 1) 31 = k - 1`;
    ARITH_RULE `~(k=0) ==> 0 < k`] THEN
  REWRITE_TAC[GSYM SAIL_HL_X86_SHIFT_PARITY32; BIT_WORD_SUBWORD;
    BIT_WORD_ZX; BIT_WORD_JOIN; DIMINDEX_32; DIMINDEX_64; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_ARBITRARY_BIT0; EXISTS_SIMP; EQ_SYM_EQ;
    WORD_SHL_ZERO; WORD_USHR_ZERO; WORD_ISHR_ZERO; BIT_WORD_ZX;
    DIMINDEX_32; DIMINDEX_64;
    GSYM(CONV_RULE(DEPTH_CONV DIMINDEX_CONV)
      (INST_TYPE[`:32`,`:M`] WORD_ZX_SUBWORD))] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[SAIL_HL_X86_COMPLEMENT_COUNT;
    ARITH_RULE `k < 32 ==> k <= 64`;
    ARITH_RULE `~(k=0) ==> 0 < k`;
    ARITH_RULE `0 < k ==> 64-k < 64 /\ 32-k < 32`;
    ARITH_RULE `k < 32 ==> ~(64-k < 32) /\ (64-k)-32 = 32-k`] THEN
  (REFL_TAC ORELSE
   (CONV_TAC(LAND_CONV(GEN_REWRITE_CONV I [SWAP_EXISTS_THM])) THEN REFL_TAC));;

(* Independent undefined choices may occur in a different binder order.
   Require the same witnesses, types and complete state expressions, then
   reorder only the existential binders by kernel equalities. No witness
   is discarded and no instruction calculation is changed. *)
let SAIL_HL_X86_EXISTS_ORDER_TAC ((_,goal) as state) =
  let ordered vars body =
    let rec visit bound term found =
      if is_var term then
        if mem term vars && not(mem term bound) && not(mem term found)
        then found @ [term] else found
      else if is_comb term then
        let left,right = dest_comb term in
        visit bound right (visit bound left found)
      else if is_abs term then
        let binder,body = dest_abs term in visit (binder::bound) body found
      else found in
    visit [] body [] in
  let vars1,body1 = strip_exists(lhand goal)
  and vars2,body2 = strip_exists(rand goal) in
  let order1 = ordered vars1 body1 and order2 = ordered vars2 body2 in
  if List.length order1 <> List.length vars1 ||
     List.length order2 <> List.length vars2 ||
     List.map type_of order1 <> List.map type_of order2 then
    failwith "existential witnesses differ";
  let used = frees body1 @ frees body2 in
  let fresh = List.map(fun var -> variant used (genvar(type_of var))) order1 in
  if not(aconv (vsubst(zip fresh order1) body1)
                (vsubst(zip fresh order2) body2)) then
    failwith "state terms differ beyond existential order";
  let rec front wanted term =
    let binder,_ = dest_exists term in
    if binder = wanted then REFL term
    else (BINDER_CONV(front wanted) THENC
          REWR_CONV SWAP_EXISTS_THM) term in
  let rec reorder wanted term =
    match wanted with
    | [] -> REFL term
    | binder::rest ->
        (front binder THENC BINDER_CONV(reorder rest)) term in
  (CONV_TAC(LAND_CONV(reorder order1) THENC RAND_CONV(reorder order2))
   THEN REFL_TAC) state;;

(* Share register/flag normalization across narrow single and double shifts.
   The arithmetic case retains SAR's sign-fill rule. The other cases split
   the undefined boundary as well as zero/one: >=width for CF alone, but
   >width for a double shift's destination and all six flags. Every choice
   stays existentially quantified; no operand or alias is constrained. *)
let SAIL_HL_X86_NARROW_SHIFT_TAC width legacy arithmetic double definitions =
  let dimension = mk_finty(num width) in
  let one_bound = ARITH_RULE
    (parse_term(Printf.sprintf "1 <= %d" width)) in
  let flags = SAIL_HL_X86_GPR_FLAG_REWRITES width in
  let zero = el 7 flags and sign = el 8 flags
  and parity = REWRITE_RULE[WORD_ZX_TRIVIAL](last flags) in
  let sar = SAIL_HL_X86_ARITHMETIC_SHIFT width in
  let narrow = SAIL_HL_X86_SHIFT_AT width in
  let cf = narrow SAIL_HL_X86_SAR_CF in
  let single_cf = narrow SAIL_HL_X86_NARROW_SHIFT_CF in
  let sign_one = narrow SAIL_HL_X86_NARROW_SHL_SIGN_ONE in
  let double_result = narrow SAIL_HL_X86_NARROW_DOUBLE_RESULT in
  let double_cf = narrow SAIL_HL_X86_NARROW_DOUBLE_CF in
  let double_right = narrow SAIL_HL_X86_NARROW_DOUBLE_RIGHT_RESULT in
  let double_halves = narrow SAIL_HL_X86_NARROW_DOUBLE_HALVES in
  let left_index = SAIL_HL_X86_SHIFT_LEFT_INDEX width in
  let bank_index_bound = CONV_RULE NUM_REDUCE_CONV
    (SPEC (mk_small_numeral width)
      (ARITH_RULE `!n k. n < 64 ==> n-k < 64`)) in
  let low_read = GSYM(CONV_RULE(DEPTH_CONV DIMINDEX_CONV)
    (INST_TYPE[dimension,`:M`] WORD_ZX_SUBWORD)) in
  let min_value = CONV_RULE NUM_REDUCE_CONV
    (GEN `k:num` (SPECL[`k:num`;mk_small_numeral(width-1)]
      SAIL_HL_X86_SAR_MIN_VALUE)) in
  let min_bound = CONV_RULE NUM_REDUCE_CONV
    (SPEC (mk_small_numeral width) SAIL_HL_X86_SAR_MIN_BOUND) in
  let double_min = CONV_RULE NUM_REDUCE_CONV
    (GEN `k:num` (SPECL[`k:num`;mk_small_numeral width]
      SAIL_HL_X86_SAR_MIN_VALUE)) in
  REPEAT GEN_TAC THEN
  (if legacy then
    MP_TAC(ISPEC `d:3 word` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN ASM_CASES_TAC `4 <= val(d:3 word)`
   else ALL_TAC) THEN
  SAIL_HL_X86_REWRITE_TAC(definitions @
    [GPR8;GPR16;GPR32_Z;assign;SEQ;UNDEFINED_VALUES;SEQ_ID;
     ASSIGNS_SEQ;ASSIGNS_THM;FST;SND;OUTL;OUTR]) THEN
  CONV_TAC SAIL_HL_X86_SHIFT_LET_CONV THEN
  REWRITE_TAC[FST;SND;OUTL;OUTR;GSYM WORD_IWORD;WORD_VAL;
    INT_OF_NUM_REM;NUM_OF_INT_OF_NUM;MOD_MOD_REFL;
    WORD_ZX_TRIVIAL;WORD_SX_TRIVIAL;SAIL_HL_X86_SHIFT_GT7;
    INT_GE;INT_GT;INT_OF_NUM_LT;INT_OF_NUM_LE] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[double_min;MIN;double_result;double_right;
    ARITH_RULE `k < n ==> k <= n`;
    ARITH_RULE `~(k<=n) ==> n < k`] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < 8 ==> n <= 7`] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  (SUBGOAL_THEN `val(count:8 word) MOD 32 < 32` ASSUME_TAC THENL
    [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV;ALL_TAC]) THEN
  REWRITE_TAC SAIL_HL_X86_GPR_SHORT_REWRITES THEN
  CONV_TAC SAIL_HL_X86_SHIFT_LET_CONV THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC[BIT_WORD_BITVAL;VAL_WORD_BITVAL;DIMINDEX_1;
    SAIL_HL_X86_OR_REDUCTION_512] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_ZX6_EQ_ZERO;WORD_XOR_EQ_0] THEN
  ASM_SIMP_TAC[SAIL_HL_X86_COUNT6_CHOICES;SAIL_HL_X86_SHIFT_WORD7;
    ARITH_RULE `k < 32 ==> k < 64`] THEN
  REWRITE_TAC[SAIL_HL_X86_NOT_BOOLEAN_WORD;SAIL_HL_X86_BLEND_MASK;
    SAIL_HL_X86_BLEND_BIT1;SAIL_HL_X86_SHIFT_GT7;VAL_WORD_BITVAL;
    INT_OF_NUM_ADD;GSYM WORD_IWORD] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  ASM_SIMP_TAC[SAIL_HL_X86_SHIFT_WORD7;sar;
    ARITH_RULE `k < 32 ==> k < 64`] THEN
  (ASM_CASES_TAC `val(count:8 word) MOD 32 = 0` THENL
    [ASM_REWRITE_TAC[BITVAL_CLAUSES;WORD_ISHR_ZERO;
                    WORD_SHL_ZERO;WORD_USHR_ZERO];
     ASM_CASES_TAC `val(count:8 word) MOD 32 = 1` THEN
     ASM_REWRITE_TAC[BITVAL_CLAUSES;ADD_CLAUSES]]) THEN
  (if arithmetic then ALL_TAC else
   ASM_CASES_TAC(parse_term(Printf.sprintf
     "val(count:8 word) MOD 32 %s %d"
     (if double then "<=" else "<") width))) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[INT_OF_NUM_SUB;NUM_OF_INT_OF_NUM;
    ARITH_RULE `~(k=0) ==> 0 < k /\ 1 <= k`;
    ARITH_RULE `k <= n ==> ~(n < k)`;
    ARITH_RULE `k < 32 ==> k <= 32`;
    ARITH_RULE `k < 32 ==> k-1 < 64`;SAIL_HL_X86_SHIFT_WORD7;
    INT_OF_NUM_ADD;INT_OF_NUM_LT;INT_OF_NUM_LE;ADD_CLAUSES;
    GSYM WORD_IWORD] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV THEN
  (* Preserve a common result expression before expanding its flag bits.
     Count one leaves a literal side condition on the selected width. *)
  ASM_SIMP_TAC[double_result;double_right;double_halves;one_bound] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BIT_WORD_NOT;BIT_WORD_XOR;BIT_WORD_SUBWORD;BIT_WORD_ZX;
    BIT_WORD_BITVAL;DIMINDEX_1;DIMINDEX_2;DIMINDEX_4;DIMINDEX_8;
    ADD_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_JOIN_ZERO;zero;parity;GSYM sign;sign_one] THEN
  REWRITE_TAC[BIT_WORD_XOR;BIT_WORD_BITVAL;DIMINDEX_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= n ==> ~(n < k)`;
    ARITH_RULE `~(k=0) ==> 1 <= k`;
    ARITH_RULE `k < 32 ==> k <= 32`;
    INT_OF_NUM_SUB;NUM_OF_INT_OF_NUM] THEN
  REWRITE_TAC[SAIL_HL_X86_SHIFT_ASSIGN_SEQUENCE;
    SAIL_HL_X86_SHIFT_HAVOC_SEQUENCE;SEQ;SEQ_ID;ASSIGNS_SEQ;
    assign;ASSIGNS_THM] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < 8 ==> n <= 7`] THEN
  CONV_TAC SAIL_HL_X86_SHIFT_LET_CONV THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC SAIL_HL_X86_GPR_INSERT_REWRITES THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
  REWRITE_TAC[SAIL_HL_X86_SHIFT_ASSIGN_SEQUENCE;
    SAIL_HL_X86_SHIFT_HAVOC_SEQUENCE;SAIL_HL_X86_ARBITRARY_BIT0;
    EXISTS_SIMP;EQ_SYM_EQ] THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
  ASM_SIMP_TAC[NUM_OF_INT_OF_NUM;BIT_WORD_AND;BIT_WORD_OR;BIT_WORD_NOT;
    BIT_WORD_XOR;BIT_WORD_0;BIT_WORD_1;BIT_WORD_BITVAL;DIMINDEX_1;
    INT_GE;INT_GT;INT_OF_NUM_LE;INT_OF_NUM_LT;INT_OF_NUM_SUB;
    ARITH_RULE `~(k=0) ==> 1 <= k`] THEN
  REWRITE_TAC[GSYM WORD_IWORD] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[SAIL_HL_X86_SHIFT_WORD7;
    ARITH_RULE `k < 32 ==> k-1 < 64`] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM;VAL_WORD_0;VAL_WORD_1;cf] THEN
  ASM_SIMP_TAC[single_cf;left_index;double_cf;double_min;double_result;
    double_right;
    ARITH_RULE `~(k=0) ==> 0 < k`;
    ARITH_RULE `k < 32 ==> k < 64`;
    ARITH_RULE `k < n ==> k <= n`;
    ARITH_RULE `~(k<=n) ==> n < k`;
    ARITH_RULE `~(k<n) ==> n <= k`;
    ARITH_RULE `0 < k /\ k <= n ==> k-1 < n`;
    ARITH_RULE `k <= n ==> MIN k n = k`] THEN
  ASM_SIMP_TAC[min_value;ARITH_RULE `k < 32 ==> k-1 < 64`] THEN
  REWRITE_TAC[min_bound] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM parity;BIT_WORD_SUBWORD;BIT_WORD_ZX;ADD_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_ARBITRARY_BIT0;EXISTS_SIMP;EQ_SYM_EQ;
    WORD_ISHR_ZERO;WORD_SHL_ZERO;WORD_USHR_ZERO;
    low_read;GSYM word_zx;min_bound;double_halves] THEN
  REWRITE_TAC[BIT_WORD_SUBWORD;BIT_WORD_ZX;ADD_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[left_index;min_bound;
    ARITH_RULE `~(k=0) ==> 0 < k`;
    ARITH_RULE `k < n ==> k <= n`;
    ARITH_RULE `0 < k /\ k <= n ==> n-k < n /\ k-1 < n`;
    ARITH_RULE `n < 64 ==> n-k < 64`] THEN
  REWRITE_TAC[bank_index_bound] THEN
  (if double then
    ASM_SIMP_TAC[double_result;double_right;double_halves;one_bound;
      BIT_WORD_SHL;BIT_WORD_USHR;BIT_WORD_JOIN;BIT_WORD_ZX;
      DIMINDEX_16;DIMINDEX_32;
      ARITH_RULE `k <= n ==> k <= n+i`;
      ARITH_RULE `i < n ==> n+i < 2*n`;
      ARITH_RULE `0 < k /\ k <= n ==> 2*n-k < 2*n`;
      ARITH_RULE `k <= n ==> (n+i)-k = (n-k)+i`] THEN
    CONV_TAC NUM_REDUCE_CONV
   else ALL_TAC) THEN
  (* Discharge the source's index assertions from the original count mask,
     including the clamped count used before an undefined double result. *)
  REWRITE_TAC[VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;ARITH_RULE `k < 32 ==> k < 64`;
    ARITH_RULE `k < 32 ==> k <= 64`;
    ARITH_RULE `k < 32 ==> k < 128`;
    ARITH_RULE `~(k=0) ==> 1 <= k`] THEN
  ASM_REWRITE_TAC[MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (REFL_TAC ORELSE
   (CONV_TAC(LAND_CONV(GEN_REWRITE_CONV I [SWAP_EXISTS_THM])) THEN REFL_TAC) ORELSE
   SAIL_HL_X86_EXISTS_ORDER_TAC);;

(* A carry rotate joins CF above the operand. At a count of w + 1, the
   operand width plus one, the rotation is the identity. *)
let SAIL_HL_X86_CARRY_JOIN = prove
 (`!p:1 word. !x:N word.
     word_rol (word_join p x:((1,N)finite_sum)word) (dimindex(:N) + 1) =
     word_join p x /\
     word_ror (word_join p x:((1,N)finite_sum)word) (dimindex(:N) + 1) =
     word_join p x /\
     word_subword (word_join p x:((1,N)finite_sum)word) (0,dimindex(:N)) = x /\
     (bit (dimindex(:N)) (word_join p x:((1,N)finite_sum)word) <=> bit 0 p)`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC WORD_ROL_EQ_SELF; MATCH_MP_TAC WORD_ROR_EQ_SELF;
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_JOIN];
    REWRITE_TAC[BIT_WORD_JOIN]] THEN
  SIMP_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; ADD_CLAUSES; LT_REFL; SUB_REFL;
           ARITH_RULE `MIN n n = n /\ n < 1 + n /\ (i < n ==> i < 1 + n)`] THEN
  CONV_TAC NUMBER_RULE);;

(* Carry rotates use different circular layouts: Sail joins operand/carry,
   putting carry at bit 0; HOL joins carry/operand, putting carry at bit w.
   These identities at width w compare the observed data and carry bits.
   They neither identify the two (w+1)-bit types nor assume instruction
   agreement. The count is unrestricted; later instruction proofs derive
   its mask. The last identity accounts for the two models' equivalent
   one-count OF calculations: with one right carry rotation, the result's
   top bit is the input carry and its next bit is the operand's top bit.
   In the statements, W, V, U and Y stand for w, w + 1, w - 1 and w - 2. *)
let SAIL_HL_X86_CARRY_LEMMAS w =
  let number letter value text = String.concat (string_of_int value)
    (String.split_on_char letter text) in
  let fill text = number 'W' w (number 'V' (w + 1)
    (number 'U' (w - 1) (number 'Y' (w - 2) text))) in
  let term text = parse_term(fill text) in
  let rules = map (fun text -> ARITH_RULE(term text)) in
  let reduce =
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV in
  let bound = SUBGOAL_THEN (term "k MOD V < V") ASSUME_TAC THENL
    [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] in
  let facts = MAP_EVERY (fun text ->
    SUBGOAL_THEN (term text) ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) in
  let layout rotate bit_rotate extra simps = prove(term(
    "!x:W word. !p:1 word. !k. \
     word_subword (" ^ rotate ^ " (word_join x p:V word) k) (1,W):W word = \
     word_subword (" ^ rotate ^
       " (word_join p x:((1,W)finite_sum)word) k) (0,W)"),
    REPEAT GEN_TAC THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; bit_rotate; BIT_WORD_JOIN;
                DIMINDEX_FINITE_SUM] THEN
    reduce THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    bound THEN facts extra THEN
    REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC(ADD_CLAUSES :: rules simps) THEN
    TRY ASM_ARITH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC) in
  let carry rotate bit_rotate extra simps = prove(term(
    "!x:W word. !p:1 word. !k. \
     bit 0 (" ^ rotate ^ " (word_join x p:V word) k) <=> \
     bit W (" ^ rotate ^ " (word_join p x:((1,W)finite_sum)word) k)"),
    REPEAT GEN_TAC THEN
    REWRITE_TAC[bit_rotate; BIT_WORD_JOIN; DIMINDEX_FINITE_SUM] THEN
    reduce THEN bound THEN
    ASM_CASES_TAC (term "k MOD V = 0") THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN facts extra THEN
    REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC(ADD_CLAUSES :: rules simps) THEN
    TRY ASM_ARITH_TAC THEN
    (REFL_TAC ORELSE (AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC))) in
  let rol_layout = layout "word_rol" BIT_WORD_ROL []
    ["i < W ==> i < V /\\ 1 + i < V"; "i < 1 ==> i < V"; "i < V ==> i - k < V";
     "i < k /\\ k < V ==> i + V - k < V";
     "i < k /\\ k < V ==> i + (V - k) < V"] in
  let ror_layout = layout "word_ror" BIT_WORD_ROR
    ["((1 + i) + k MOD V) - V < V"; "(i + k MOD V) - V < V"]
    ["i < W ==> i < V /\\ 1 + i < V"; "i < 1 ==> i < V"; "i < V ==> i - k < V";
     "i < W /\\ k < V ==> i + k - V < V";
     "i < W /\\ k < V ==> (1 + i) + k - V < V";
     "i < k /\\ k < V ==> i + V - k < V";
     "i < k /\\ k < V ==> i + (V - k) < V"] in
  let rol_carry = carry "word_rol" BIT_WORD_ROL []
    ["k < V ==> W - k < V"; "0 < k /\\ k < V ==> V - k < V";
     "0 < k /\\ k < V ==> (V - k) - 1 = W - k"] in
  let ror_carry = carry "word_ror" BIT_WORD_ROR ["(W + k MOD V) - V < V"]
    ["k < V ==> k - 1 < V"; "0 < k ==> (W + k) - V = k - 1"] in
  let rol_sign = prove(term
   "!x:W word. !p:1 word. !k. \
    bit W (word_rol (word_join x p:V word) k) <=> \
    bit U (word_subword \
      (word_rol (word_join p x:((1,W)finite_sum)word) k) (0,W):W word)",
    REPEAT GEN_TAC THEN
    MP_TAC(AP_TERM (term "bit U:W word->bool")
      (SPECL [term "x:W word"; `p:1 word`; `k:num`] rol_layout)) THEN
    REWRITE_TAC[BIT_WORD_SUBWORD] THEN reduce THEN REWRITE_TAC[]) in
  let ror_one = prove(term
   "!x:W word. !p:1 word. \
    (bit U (word_subword (word_ror \
       (word_join p x:((1,W)finite_sum)word) 1) (0,W):W word) <=> bit 0 p) /\\ \
    (bit Y (word_subword (word_ror \
       (word_join p x:((1,W)finite_sum)word) 1) (0,W):W word) <=> bit U x)",
    REPEAT GEN_TAC THEN
    REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_ROR; BIT_WORD_JOIN;
                DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
    reduce THEN REWRITE_TAC[]) in
  let zero_data = GEN_ALL(el 2 (CONJUNCTS(SPEC_ALL
    (SAIL_HL_X86_SHIFT_AT w SAIL_HL_X86_CARRY_JOIN)))) in
  [rol_layout; ror_layout; rol_carry; ror_carry; rol_sign], zero_data, ror_one;;

let SAIL_HL_X86_CARRY_LAYOUTS =
  map (fun width -> width, SAIL_HL_X86_CARRY_LEMMAS width) [64; 32];;

(* The 64- and 32-bit carry rotates. The count is masked to six or five
   bits, below the rotated width w + 1. *)
let SAIL_HL_X86_CARRY_ROTATE_TAC width definitions =
  let layouts, zero_data, ror_one = assoc width SAIL_HL_X86_CARRY_LAYOUTS in
  let count = Printf.sprintf "val(count:8 word) MOD %d" width in
  let test relation value =
    parse_term(Printf.sprintf "%s %s %d" count relation value) in
  let narrow tactic = if width = 32 then tactic else ALL_TAC in
  let rotations = map (fun theorem ->
    SAIL_HL_X86_SHIFT_AT (width + 1) (GSYM theorem))
    [WORD_ROL_SHIFTS; WORD_ROR_SHIFTS] in
  REPEAT GEN_TAC THEN
  SAIL_HL_X86_REWRITE_TAC(definitions @
    [GPR32_Z; assign; SEQ; UNDEFINED_VALUES; SEQ_ID; ASSIGNS_SEQ; ASSIGNS_THM;
     FST; SND; OUTL; OUTR]) THEN
  CONV_TAC SAIL_HL_X86_SHIFT_LET_CONV THEN
  REWRITE_TAC[FST; SND; OUTL; OUTR; GSYM WORD_IWORD; WORD_VAL;
              INT_OF_NUM_REM; NUM_OF_INT_OF_NUM; MOD_MOD_REFL] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  SUBGOAL_THEN (test "<" width) ASSUME_TAC THENL
    [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN (mk_conj(test "<" (width + 1), test "<=" (width + 1)))
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  narrow(REWRITE_TAC SAIL_HL_X86_GPR_SHORT_REWRITES THEN
         CONV_TAC SAIL_HL_X86_SHIFT_LET_CONV) THEN
  ASM_SIMP_TAC[MOD_LT; SAIL_HL_X86_COMPLEMENT_COUNT] THEN
  ASM_SIMP_TAC rotations THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC[BIT_WORD_BITVAL; DIMINDEX_1;
              SAIL_HL_X86_OR_REDUCTION_512] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_ZX6_EQ_ZERO; WORD_XOR_EQ_0] THEN
  ASM_SIMP_TAC(SAIL_HL_X86_COUNT6_CHOICES ::
    (if width = 32 then [ARITH_RULE `k < 32 ==> k < 64`] else [])) THEN
  REWRITE_TAC([SAIL_HL_X86_NOT_BOOLEAN_WORD;
               SAIL_HL_X86_BLEND_MASK; SAIL_HL_X86_BLEND_BIT1] @ layouts) THEN
  ASM_CASES_TAC (test "=" 0) THENL
   [ASM_REWRITE_TAC[WORD_ROL_ZERO; WORD_ROR_ZERO; zero_data; BIT_WORD_JOIN;
                    BIT_WORD_SUBWORD];
    ASM_CASES_TAC (test "=" 1) THEN ASM_REWRITE_TAC[ror_one]] THEN
  REWRITE_TAC[BIT_WORD_XOR; BIT_WORD_BITVAL; DIMINDEX_1;
              DIMINDEX_FINITE_SUM] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  narrow(REWRITE_TAC SAIL_HL_X86_GPR_INSERT_REWRITES) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
  REWRITE_TAC([SAIL_HL_X86_ARBITRARY_BIT0; EXISTS_SIMP; EQ_SYM_EQ] @
    (if width = 32 then
       [GSYM(CONV_RULE(DEPTH_CONV DIMINDEX_CONV)
          (INST_TYPE[`:32`,`:M`] WORD_ZX_SUBWORD)); GSYM word_zx]
     else [])) THEN
  REFL_TAC;;

(* The six 8- and 16-bit carry rotates are not equal to s2n-bignum's: at
   a whole-cycle count, a nonzero masked count that rotates the operand
   and CF a whole cycle (9, 18 or 27 for bytes, 17 for 16 bits), shina
   keeps OF, where s2n-bignum leaves OF undefined. The _EXACT theorems
   state the whole relation for every operand, count and state: shina's
   relation is s2n-bignum's, with OF also kept at those counts. Being
   equations, they also show that shina has an outcome wherever that
   relation does: they cannot hold just because shina permits no final
   state.

   The proof splits the masked count into its 32 values. For each, both
   relations reduce to explicit writes of the register, CF and OF.
   s2n-bignum's undefined OF is the existential SAIL_HL_X86_OF_UNDEFINED
   removes; the writes are put in one order, and bit-blasting proves the
   register and flag values equal. *)
let SAIL_HL_X86_OF_UNDEFINED = prove
 (`!s s':x86state. (?y. write OF y s = s') <=> write OF (read OF s') s = s'`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:bool` (SUBST1_TAC o SYM)) THEN
    CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
    CONV_TAC(DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN REFL_TAC;
    DISCH_TAC THEN EXISTS_TAC `read OF (s':x86state)` THEN
    ASM_REWRITE_TAC[]]);;

let SAIL_HL_X86_WRITE_CONGRUENCE = prove
 (`!c:(A,B)component. !a b s s'.
   a = b /\ s = s' ==> write c a s = write c b s'`,
  SIMP_TAC[]);;

let SAIL_HL_X86_MASKED_COUNT = prove
 (`!c:8 word. val c MOD 32 < 32`,
  GEN_TAC THEN REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Bit-blasting treats a register read as a word variable only when the
   register index is not itself a word expression, as in the legacy forms. *)
let SAIL_HL_X86_GENERALIZE_READS_TAC (asl,w as goal) =
  let reads = setify(find_terms (fun term ->
    match term with
    | Comb(Comb(Const("read",_),component),_) ->
        can (find_term (fun t -> t = `registers`)) component
    | _ -> false) w) in
  MAP_EVERY (fun term ->
    SPEC_TAC(term, genvar(type_of term)) THEN GEN_TAC) reads goal;;

let SAIL_HL_X86_CARRY_PREPARE_TAC legacy definitions =
  REPEAT GEN_TAC THEN
  (if legacy then
    MP_TAC(ISPEC `d:3 word` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN ASM_CASES_TAC `4 <= val(d:3 word)`
   else ALL_TAC) THEN
  SAIL_HL_X86_REWRITE_TAC(definitions @
    [GPR8;GPR16;assign;SEQ;UNDEFINED_VALUES;SEQ_ID;
     ASSIGNS_SEQ;ASSIGNS_THM;FST;SND;OUTL;OUTR]) THEN
  CONV_TAC SAIL_HL_X86_SHIFT_LET_CONV THEN
  REWRITE_TAC[FST;SND;OUTL;OUTR;GSYM WORD_IWORD;WORD_VAL;
    INT_OF_NUM_REM;NUM_OF_INT_OF_NUM;MOD_MOD_REFL;
    INT_GE;INT_GT;INT_OF_NUM_LT;INT_OF_NUM_LE] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < 8 ==> n <= 7`] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC SAIL_HL_X86_GPR_SHORT_REWRITES THEN
  CONV_TAC SAIL_HL_X86_SHIFT_LET_CONV THEN
  (* Name a legacy low-byte register as the statement does. *)
  (if legacy then REWRITE_TAC[GSYM word_zx] else ALL_TAC) THEN
  (* One goal per masked count, with every count-dependent choice made. *)
  MP_TAC(SPEC `count:8 word` SAIL_HL_X86_MASKED_COUNT) THEN
  SPEC_TAC(`val(count:8 word) MOD 32`,`k:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[BIT_WORD_BITVAL;DIMINDEX_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV BETA_CONV);;

(* Two states given by explicit writes: put the writes in one order and
   prove the register and flag values equal. *)
let SAIL_HL_X86_CARRY_CLOSE_TAC =
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
  REPEAT(MATCH_MP_TAC SAIL_HL_X86_WRITE_CONGRUENCE THEN CONJ_TAC) THEN
  TRY REFL_TAC THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
  SAIL_HL_X86_GENERALIZE_READS_TAC THEN BITBLAST_TAC;;

(* From shina's state, s2n-bignum's undefined OF is the value shina
   writes, and at a whole-cycle count that value is the old OF. From
   s2n-bignum's state t, the witness for shina's unknown OF bit is OF in t;
   where shina determines OF, the witness is not used. *)
let SAIL_HL_X86_CARRY_EXACT_TAC legacy definitions =
  SAIL_HL_X86_CARRY_PREPARE_TAC legacy definitions THEN
  REWRITE_TAC[SAIL_HL_X86_OF_UNDEFINED] THEN
  (EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN(SUBST1_TAC o SYM)) THEN
    REPEAT CONJ_TAC THEN SAIL_HL_X86_CARRY_CLOSE_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> rand(concl th) = `t:x86state`)) THEN
    EXISTS_TAC `word(bitval(read OF (t:x86state))):1 word` THEN
    ASM_REWRITE_TAC[] THEN SAIL_HL_X86_CARRY_CLOSE_TAC]);;

(* The claims: each form's generated root against s2n-bignum's relation
   at the masked count. The 8- and 16-bit carry rotates instead get an
   exact relation: s2n-bignum's, with OF also kept where kept holds. *)
let sail_hl_x86_shift_root operation width legacy =
  Printf.sprintf "X86_%s%d%s_%s" operation width
    (if legacy then "_LEGACY" else "")
    (if mem operation ["SHLD"; "SHRD"] then "RRI" else "RI");;

let SAIL_HL_X86_SHIFT_CLAIM tactic kept (operation,width,legacy,source,target) =
  let root = sail_hl_x86_shift_root operation width legacy in
  let names = if mem operation ["SHLD"; "SHRD"] then ["d"; "m"] else ["d"] in
  let statement = parse_term(Printf.sprintf
    "!%s:%d word. !count:8 word. !s t:x86state. \
     sail_hl_%s %s count s t <=> x86_%s %s (val count MOD %d) s t%s"
    (String.concat " " names) (if legacy then 3 else 4)
    (String.concat "_5f" (String.split_on_char '_' root))
    (String.concat " " names) operation
    (String.concat " " (map (SAIL_HL_X86_GPR_COMPONENT width legacy) names))
    (if width = 64 then 64 else 32)
    (if kept = "" then ""
     else " /\\ (" ^ kept ^ " ==> read OF t = read OF s)")) in
  Option.map (fun theorem -> root, theorem)
    (sail_hl_proof_claim root (fun () ->
      prove(statement, tactic [source; target])));;

let SAIL_HL_X86_SHIFT_TAC operation width legacy =
  match operation with
  | "ROL" | "ROR" ->
      if width = 64 then SAIL_HL_X86_ROTATE_TAC
      else SAIL_HL_X86_NARROW_ROTATE_TAC width legacy
  | "RCL" | "RCR" -> SAIL_HL_X86_CARRY_ROTATE_TAC width
  | _ ->
      if width = 64 then SAIL_HL_X86_SCALAR_SHIFT_TAC
      else if width = 32 then SAIL_HL_X86_SHIFT32_TAC
      else SAIL_HL_X86_NARROW_SHIFT_TAC width legacy (operation = "SAR")
        (mem operation ["SHLD"; "SHRD"]);;

(* Each claim below is proved by exactly one process when the claims are
   split across forked processes (proof-fork.ml); everything above is
   shared setup. *)
sail_hl_proof_fork "SAIL_HOL_LIGHT_X86_SHIFT_PROOFS_OK";;

let SAIL_HL_X86_SHIFT_CLAIMS = List.filter_map
 (fun (operation,width,legacy,_,_ as form) ->
    SAIL_HL_X86_SHIFT_CLAIM
      (SAIL_HL_X86_SHIFT_TAC operation width legacy) "" form)
 ["ROL",64,false,sail_hl_X86_5fROL64_5fRI,x86_ROL;
  "ROR",64,false,sail_hl_X86_5fROR64_5fRI,x86_ROR;
  "RCL",64,false,sail_hl_X86_5fRCL64_5fRI,x86_RCL;
  "RCR",64,false,sail_hl_X86_5fRCR64_5fRI,x86_RCR;
  "SHL",64,false,sail_hl_X86_5fSHL64_5fRI,SAIL_HL_X86_SHL_DEF;
  "SHR",64,false,sail_hl_X86_5fSHR64_5fRI,SAIL_HL_X86_SHR_DEF;
  "SAR",64,false,sail_hl_X86_5fSAR64_5fRI,x86_SAR;
  "SHLD",64,false,sail_hl_X86_5fSHLD64_5fRRI,SAIL_HL_X86_SHLD_DEF;
  "SHRD",64,false,sail_hl_X86_5fSHRD64_5fRRI,SAIL_HL_X86_SHRD_DEF;
  "ROL",8,false,sail_hl_X86_5fROL8_5fRI,x86_ROL;
  "ROR",8,false,sail_hl_X86_5fROR8_5fRI,x86_ROR;
  "ROL",16,false,sail_hl_X86_5fROL16_5fRI,x86_ROL;
  "ROR",16,false,sail_hl_X86_5fROR16_5fRI,x86_ROR;
  "ROL",32,false,sail_hl_X86_5fROL32_5fRI,x86_ROL;
  "ROR",32,false,sail_hl_X86_5fROR32_5fRI,x86_ROR;
  "ROL",8,true,sail_hl_X86_5fROL8_5fLEGACY_5fRI,x86_ROL;
  "ROR",8,true,sail_hl_X86_5fROR8_5fLEGACY_5fRI,x86_ROR;
  "SHL",32,false,sail_hl_X86_5fSHL32_5fRI,SAIL_HL_X86_SHL_DEF;
  "SHR",32,false,sail_hl_X86_5fSHR32_5fRI,SAIL_HL_X86_SHR_DEF;
  "SAR",32,false,sail_hl_X86_5fSAR32_5fRI,x86_SAR;
  "SHLD",32,false,sail_hl_X86_5fSHLD32_5fRRI,SAIL_HL_X86_SHLD_DEF;
  "SHRD",32,false,sail_hl_X86_5fSHRD32_5fRRI,SAIL_HL_X86_SHRD_DEF;
  "SAR",8,false,sail_hl_X86_5fSAR8_5fRI,x86_SAR;
  "SAR",16,false,sail_hl_X86_5fSAR16_5fRI,x86_SAR;
  "SAR",8,true,sail_hl_X86_5fSAR8_5fLEGACY_5fRI,x86_SAR;
  "SHL",8,false,sail_hl_X86_5fSHL8_5fRI,SAIL_HL_X86_SHL_DEF;
  "SHR",8,false,sail_hl_X86_5fSHR8_5fRI,SAIL_HL_X86_SHR_DEF;
  "SHL",16,false,sail_hl_X86_5fSHL16_5fRI,SAIL_HL_X86_SHL_DEF;
  "SHR",16,false,sail_hl_X86_5fSHR16_5fRI,SAIL_HL_X86_SHR_DEF;
  "SHL",8,true,sail_hl_X86_5fSHL8_5fLEGACY_5fRI,SAIL_HL_X86_SHL_DEF;
  "SHR",8,true,sail_hl_X86_5fSHR8_5fLEGACY_5fRI,SAIL_HL_X86_SHR_DEF;
  "SHLD",16,false,sail_hl_X86_5fSHLD16_5fRRI,SAIL_HL_X86_SHLD_DEF;
  "SHRD",16,false,sail_hl_X86_5fSHRD16_5fRRI,SAIL_HL_X86_SHRD_DEF;
  "RCL",32,false,sail_hl_X86_5fRCL32_5fRI,x86_RCL;
  "RCR",32,false,sail_hl_X86_5fRCR32_5fRI,x86_RCR];;

let SAIL_HL_X86_EXACT_CLAIMS = List.filter_map
 (fun (_,width,legacy,_,_ as form) ->
    SAIL_HL_X86_SHIFT_CLAIM (SAIL_HL_X86_CARRY_EXACT_TAC legacy)
      (if width = 8 then "val count MOD 32 = 9 \\/ val count MOD 32 = 18 \\/ \
                          val count MOD 32 = 27"
       else "val count MOD 32 = 17") form)
 ["RCL",8,false,sail_hl_X86_5fRCL8_5fRI,x86_RCL;
  "RCL",8,true,sail_hl_X86_5fRCL8_5fLEGACY_5fRI,x86_RCL;
  "RCL",16,false,sail_hl_X86_5fRCL16_5fRI,x86_RCL;
  "RCR",8,false,sail_hl_X86_5fRCR8_5fRI,x86_RCR;
  "RCR",8,true,sail_hl_X86_5fRCR8_5fLEGACY_5fRI,x86_RCR;
  "RCR",16,false,sail_hl_X86_5fRCR16_5fRI,x86_RCR];;

loadt "tools/sail/proofs/x86-rcl-rcr-claims.ml";;

(* Report differences explicitly as _DIFF, never as agreement. CI requires
   all 47 results: 35 complete-state equalities, and for the six other
   forms a closed counterexample and the exact relation. *)
let SAIL_HL_X86_SHIFT_RESULTS =
  map (fun (root,theorem) -> "SAIL_HL_" ^ root ^ "_EQ",theorem)
    SAIL_HL_X86_SHIFT_CLAIMS @
  map (fun (root,theorem) -> "SAIL_HL_" ^ root ^ "_DIFF",theorem)
    SAIL_HL_X86_DISCREPANCY_CLAIMS @
  map (fun (root,theorem) -> "SAIL_HL_" ^ root ^ "_EXACT",theorem)
    SAIL_HL_X86_EXACT_CLAIMS;;
if sail_hl_proof_whole () &&
   length(setify(map fst SAIL_HL_X86_SHIFT_RESULTS)) <> 47 then
  failwith "shift result count or duplicate";;
List.iter sail_hl_report SAIL_HL_X86_SHIFT_RESULTS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_X86_SHIFT_PROOFS_OK";;
