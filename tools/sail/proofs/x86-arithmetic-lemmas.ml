(* Shared arithmetic and state-normalization facts.
   Relate Sail's bit calculations to HOL flags, and reorder independent
   component writes using proved orthogonality. These are support lemmas,
   not instruction-conformance claims. Arithmetic and shift drivers prove
   complete-state agreement separately. *)
needs "x86/proofs/base.ml";;
needs "Library/words.ml";;
needs "tools/sail/proofs/x86-vector-lemmas.ml";;
needs "Library/bitmatch.ml";;
needs "common/for_hollight.ml";;
needs "common/words2.ml";;
needs "common/misc.ml";;

(* REWRITE_CONV, except that the basic rewrites EXISTS_SIMP and
   FORALL_SIMP apply only once vfree_in finds no occurrence of the bound
   variable. Generated relations bind unknown values with quantifiers that
   scope almost the whole instruction. On such a quantifier HOL's matcher
   renames the binder, collects the body's free variables and compares the
   whole body before the rewrite fails. Every rewrite and basic conversion
   is otherwise the same, so the results are those of REWRITE_CONV. *)
let SAIL_HL_X86_REWRITE_CONV =
  let quantifiers = map (concl o SPEC_ALL) [EXISTS_SIMP; FORALL_SIMP] in
  let vacuous term =
    match term with
    | Comb(Const(("?" | "!"),_),Abs(v,body)) when not (vfree_in v body) ->
        (REWR_CONV EXISTS_SIMP ORELSEC REWR_CONV FORALL_SIMP) term
    | _ -> failwith "SAIL_HL_X86_REWRITE_CONV: not a vacuous quantifier" in
  let cache = ref None in
  let basic_net () =
    let rewrites = basic_rewrites() and conversions = basic_convs() in
    match !cache with
    | Some(rewrites',conversions',net)
        when rewrites' == rewrites && conversions' == conversions -> net
    | _ ->
        let net = itlist (net_of_thm true)
          (filter (fun theorem ->
             not (exists (aconv (concl theorem)) quantifiers)) rewrites)
          (itlist (fun (_,(pattern,conversion)) ->
             net_of_conv pattern conversion) conversions
            (net_of_conv `?x:A. t` vacuous
              (net_of_conv `!x:A. t` vacuous empty_net))) in
        cache := Some(rewrites,conversions,net);
        net in
  fun theorems ->
    GENERAL_REWRITE_CONV true TOP_DEPTH_CONV (basic_net()) theorems;;

let SAIL_HL_X86_REWRITE_TAC theorems =
  CONV_TAC(SAIL_HL_X86_REWRITE_CONV theorems);;

let SAIL_HL_X86_REWRITE_RULE theorems =
  CONV_RULE(SAIL_HL_X86_REWRITE_CONV theorems);;

let SAIL_HL_X86_WRITE_COMMUTE = prove
 (`!c:(S,A)component. !d:(S,B)component. !x y s.
   orthogonal_components c d
   ==> write c x (write d y s) = write d y (write c x s)`,
  REWRITE_TAC[orthogonal_components] THEN MESON_TAC[]);;

(* Reorder independent writes through kernel-checked orthogonality facts.
   This changes only their presentation. It cannot delete a flag or move a
   write past a source read: those reads were captured before normalization. *)
let SAIL_HL_X86_ORDER_WRITES_CONV =
  let flags = [`ZF`; `SF`; `PF`; `CF`; `OF`; `AF`] in
  (* Parse the register pattern once, not at every ranked write. *)
  let register = `registers :> element (d:4 word)` in
  let rank component =
    if can (term_match [] register) component then -1
    else index component flags in
  let rule = PART_MATCH (lhand o rand) SAIL_HL_X86_WRITE_COMMUTE in
  fun tm ->
    let _, args = strip_comb tm in
    let outer, inner = match args with
      | [c; _; body] ->
          (match strip_comb body with
           | Const("write",_), [d; _; _] -> c,d
           | _ -> failwith "x86 write ordering")
      | _ -> failwith "x86 write ordering" in
    if compare (rank outer,outer) (rank inner,inner) >= 0 then
      failwith "x86 writes already ordered";
    let th = rule tm in
    MP th (ORTHOGONAL_COMPONENTS_CONV (lhand(concl th)));;

(* Delete a self-write only with strong validity for that exact component.
   A captured flag read can refer to an earlier state: first prove that
   intervening writes leave that read unchanged. A 32-bit zerotop component
   is not strongly valid, so this cannot erase its upper-register clearing.
   Depth traversal first collapses inner flag self-writes. *)
let SAIL_HL_X86_SELF_WRITE_CONV term =
  match strip_comb term with
  | Const("write",_), [component; value; state] ->
      (match strip_comb value with
       | Const("read",_), [same; _] when same = component -> ()
       | _ -> failwith "not a captured component read");
      let theorem = CONJUNCT1(CONJUNCT2(REWRITE_RULE
        [strongly_valid_component] (STRONGLY_VALID_COMPONENT_RULE component))) in
      let observation = DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV
        (mk_comb(rator value,state)) in
      if not(aconv (rand(concl observation)) value) then
        failwith "intervening writes change the captured read";
      (RATOR_CONV(RAND_CONV(REWR_CONV(SYM observation))) THENC
       REWR_CONV theorem) term
  | _ -> failwith "not a write";;

let SAIL_HL_X86_DIMS = List.map DIMINDEX_CONV
  [`dimindex(:4)`; `dimindex(:5)`; `dimindex(:64)`; `dimindex(:65)`];;

(* One extra bit holds the entire unsigned sum, including incoming carry.
   Establish that bound before reducing the wide result modulo its width. *)
let SAIL_HL_X86_UNSIGNED_WIDE = prove
 (`!x:N word. !y:N word. !c.
   dimindex(:M) = dimindex(:N) + 1
   ==> val(word_add (word_add (word_zx x:M word) (word_zx y))
              (word(bitval c))) = val x + val y + bitval c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[VAL_WORD_ADD; VAL_WORD_ZX; VAL_WORD_BITVAL;
               ARITH_RULE `n <= n + 1`] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[ADD_ASSOC] THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `x:N word` VAL_BOUND) THEN
  MP_TAC(ISPEC `y:N word` VAL_BOUND) THEN
  MP_TAC(SPEC `c:bool` BITVAL_BOUND) THEN
  ASM_REWRITE_TAC[EXP_ADD; EXP_1] THEN ARITH_TAC);;

let SAIL_HL_X86_UNSIGNED_AT source destination =
  CONV_RULE (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [source,`:N`; destination,`:M`] SAIL_HL_X86_UNSIGNED_WIDE);;

let SAIL_HL_X86_LOW_ADD source destination =
  CONV_RULE (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [source,`:M`; destination,`:N`] WORD_ZX_ADD);;

let SAIL_HL_X86_LOW_SUB source destination =
  CONV_RULE (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [source,`:M`; destination,`:N`] WORD_ZX_SUB);;

let SAIL_HL_X86_LOW_SUBWORD width =
  CONV_RULE (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [width,`:M`] (GSYM WORD_ZX_SUBWORD));;

let SAIL_HL_X86_MSB65 = CONV_RULE
  (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
  (INST_TYPE [`:65`,`:N`] MSB_VAL);;
let SAIL_HL_X86_MSB64 = CONV_RULE
  (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
  (INST_TYPE [`:64`,`:N`] MSB_VAL);;
let SAIL_HL_X86_MSB5 = CONV_RULE
  (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
  (INST_TYPE [`:5`,`:N`] MSB_VAL);;

let SAIL_HL_X86_CARRY64 = prove
 (`!x y:64 word. !c.
   bit 64 (word_add (word_add (word_zx x:65 word) (word_zx y))
             (word(bitval c))) <=>
   ~(val x + val y + bitval c =
     val(word_add (word_add x y) (word(bitval c))))`,
  SIMP_TAC (SAIL_HL_X86_MSB65 :: SAIL_HL_X86_UNSIGNED_AT `:64` `:65` ::
            CARRY_WORD_ADC :: SAIL_HL_X86_DIMS) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let SAIL_HL_X86_AUX_CARRY = prove
 (`!x y:64 word. !c.
   bit 4 (word_add (word_add
     (word_zx(word_subword x (0,4):4 word):5 word)
     (word_zx(word_subword y (0,4):4 word))) (word(bitval c))) <=>
   ~(val(word_zx x:4 word) + val(word_zx y:4 word) + bitval c =
     val(word_zx(word_add (word_add x y) (word(bitval c))):4 word))`,
  SIMP_TAC (SAIL_HL_X86_LOW_SUBWORD `:4` ::
            SAIL_HL_X86_LOW_ADD `:64` `:4` :: WORD_ZX_BITVAL ::
            SAIL_HL_X86_MSB5 :: SAIL_HL_X86_UNSIGNED_AT `:4` `:5` ::
            CARRY_WORD_ADC :: SAIL_HL_X86_DIMS) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let SAIL_HL_X86_OVERFLOW_ADD = prove
 (`!x y:64 word.
   ((bit 63 x <=> bit 63 y) /\ ~(bit 63 (word_add x y) <=> bit 63 x)) <=>
   ~(ival x + ival y = ival(word_add x y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SAIL_HL_X86_MSB64] THEN WORD_ARITH_TAC);;

let SAIL_HL_X86_SX_LOW = prove
 (`!x:64 word. word_zx(word_sx x:65 word):64 word = x`,
  BITBLAST_TAC);;

let SAIL_HL_X86_SIGNED_WIDE = prove
 (`!x:64 word. !y:64 word. !c.
   ival(word_add (word_add (word_sx x:65 word) (word_sx y))
                  (word(bitval c))) = ival x + ival y + &(bitval c)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_sx; WORD_IWORD; GSYM IWORD_INT_ADD; INT_ADD_ASSOC] THEN
  MATCH_MP_TAC IVAL_IWORD THEN
  MP_TAC(ISPEC `x:64 word` IVAL_BOUND) THEN
  MP_TAC(ISPEC `y:64 word` IVAL_BOUND) THEN
  MP_TAC(SPEC `c:bool` BITVAL_BOUND) THEN
  REWRITE_TAC (GSYM INT_OF_NUM_LE :: SAIL_HL_X86_DIMS) THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN INT_ARITH_TAC);;

(* A 65-bit signed value fits in 64 bits exactly when its two highest bits
   agree. This is independent of the calculation that produced the value. *)
let SAIL_HL_X86_WIDE_OVERFLOW =
  let sign_extension = CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [`:64`,`:M`; `:65`,`:N`] IVAL_WORD_SX) in
  prove
   (`!z:65 word.
     ~(bit 64 z <=> bit 63 z) <=>
     ~(ival z = ival(word_zx z:64 word))`,
    GEN_TAC THEN GEN_REWRITE_TAC
      (RAND_CONV o RAND_CONV o RAND_CONV) [GSYM sign_extension] THEN
    REWRITE_TAC[IVAL_EQ] THEN BITBLAST_TAC);;

let SAIL_HL_X86_OVERFLOW_ADC = prove
 (`!x y:64 word. !c.
   ~(bit 64 (word_add (word_add (word_sx x:65 word) (word_sx y))
       (word(bitval c))) <=>
     bit 63 (word_add (word_add (word_sx x:65 word) (word_sx y))
       (word(bitval c)))) <=>
   ~(ival x + ival y + &(bitval c) =
     ival(word_add (word_add x y) (word(bitval c))))`,
  SIMP_TAC (SAIL_HL_X86_WIDE_OVERFLOW :: SAIL_HL_X86_SIGNED_WIDE ::
            SAIL_HL_X86_LOW_ADD `:65` `:64` :: WORD_ZX_BITVAL :: SAIL_HL_X86_SX_LOW ::
            SAIL_HL_X86_DIMS));;

let SAIL_HL_X86_ZERO64 =
  let widen = CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [`:64`,`:M`; `:65`,`:N`] VAL_WORD_ZX) in
  prove
   (`!z:64 word. bit 64 (word_sub (word_zx z:65 word) (word 1)) <=>
                   val z = 0`,
    GEN_TAC THEN
    REWRITE_TAC (SAIL_HL_X86_MSB65 :: VAL_WORD_SUB_CASES :: widen ::
                 VAL_WORD_1 :: SAIL_HL_X86_DIMS) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPEC `z:64 word` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* Sail folds eight parity bits with XOR. The word conversion proves this
   exact fixed-size circuit, including the final inversion for even parity. *)
let SAIL_HL_X86_PARITY8 = prove
 (`!z:8 word.
   let r4:4 word = word_xor (word_subword z (4,4))
                            (word_subword z (0,4)) in
   let r2:2 word = word_xor (word_subword r4 (2,2))
                            (word_subword r4 (0,2)) in
   bit 0 (word_not (word_xor (word_subword r2 (1,1):1 word)
                             (word_subword r2 (0,1)))) <=>
   word_evenparity z`,
  REWRITE_TAC[LET_DEF; LET_END_DEF; word_evenparity] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_POPCOUNT_EXPAND_CONV) THEN
  REWRITE_TAC[EVEN_ADD; EVEN_BITVAL] THEN
  CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN CONV_TAC TAUT);;

let SAIL_HL_X86_JOIN_ZERO = prove
 (`!x:N word. word_join (word 0:1 word) x:M word = word_zx x`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_JOIN; VAL_WORD_0; VAL_WORD_ZX_GEN;
              MULT_CLAUSES; ADD_CLAUSES]);;

(* The extra bit represents the exact signed unsigned-operand difference,
   including incoming borrow. Its sign is therefore the borrow condition.
   Bounds are proved before any signed-word simplification. *)
let SAIL_HL_X86_UNSIGNED_DIFFERENCE_WIDE = prove
 (`!x:N word. !y:N word. !c.
   dimindex(:M) = dimindex(:N) + 1
   ==> ival(word_sub (word_sub (word_zx x:M word) (word_zx y))
                  (word(bitval c))) =
   &(val x) - (&(val y) + &(bitval c))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[word_zx; WORD_IWORD; GSYM IWORD_INT_SUB;
    INT_ARITH `x - y - z:int = x - (y + z)`] THEN
  MATCH_MP_TAC IVAL_IWORD THEN
  MP_TAC(ISPEC `x:N word` VAL_BOUND) THEN
  MP_TAC(ISPEC `y:N word` VAL_BOUND) THEN
  MP_TAC(SPEC `c:bool` BITVAL_BOUND) THEN
  ASM_REWRITE_TAC[ADD_SUB; GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_LE;
                  GSYM INT_OF_NUM_POW] THEN INT_ARITH_TAC);;

let SAIL_HL_X86_DIFFERENCE_AT source destination =
  CONV_RULE (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [source,`:N`; destination,`:M`]
      SAIL_HL_X86_UNSIGNED_DIFFERENCE_WIDE);;

let SAIL_HL_X86_UNSIGNED_DIFFERENCE =
  SAIL_HL_X86_DIFFERENCE_AT `:64` `:65`;;

let SAIL_HL_X86_SIGN65 = CONV_RULE
  (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
  (INST_TYPE [`:65`,`:N`] MSB_IVAL);;
let SAIL_HL_X86_SIGN5 = CONV_RULE
  (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
  (INST_TYPE [`:5`,`:N`] MSB_IVAL);;

let SAIL_HL_X86_BORROW64 = prove
 (`!x y:64 word. !c.
   bit 64 (word_sub (word_sub (word_zx x:65 word) (word_zx y))
             (word(bitval c))) <=>
   ~(&(val x) - (&(val y) + &(bitval c)):int =
     &(val(word_sub x (word_add y (word(bitval c))))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC (SAIL_HL_X86_SIGN65 :: SAIL_HL_X86_DIMS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_UNSIGNED_DIFFERENCE; CARRY_WORD_SBB] THEN
  ASM_CASES_TAC `c:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; INT_OF_NUM_CLAUSES] THEN ARITH_TAC);;

let SAIL_HL_X86_AUX_BORROW = prove
 (`!x y:64 word. !c.
   bit 4 (word_sub (word_sub
     (word_zx(word_subword x (0,4):4 word):5 word)
     (word_zx(word_subword y (0,4):4 word))) (word(bitval c))) <=>
   ~(&(val(word_zx x:4 word)) -
     (&(val(word_zx y:4 word)) + &(bitval c)):int =
     &(val(word_zx(word_sub x (word_add y (word(bitval c)))):4 word)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SAIL_HL_X86_LOW_SUBWORD `:4`;
    SAIL_HL_X86_LOW_SUB `:64` `:4`; SAIL_HL_X86_LOW_ADD `:64` `:4`;
    WORD_ZX_BITVAL; SAIL_HL_X86_SIGN5] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_DIFFERENCE_AT `:4` `:5`; CARRY_WORD_SBB] THEN
  ASM_CASES_TAC `c:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; INT_OF_NUM_CLAUSES] THEN ARITH_TAC);;

let SAIL_HL_X86_OVERFLOW_SUB = prove
 (`!x y:64 word.
   (~(bit 63 x <=> bit 63 y) /\ ~(bit 63 (word_sub x y) <=> bit 63 x)) <=>
   ~(ival x - ival y = ival(word_sub x y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SAIL_HL_X86_MSB64] THEN WORD_ARITH_TAC);;

let SAIL_HL_X86_SIGNED_DIFFERENCE = prove
 (`!x:64 word. !y:64 word. !c.
   ival(word_sub (word_sub (word_sx x:65 word) (word_sx y))
                  (word(bitval c))) = ival x - (ival y + &(bitval c))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_sx; WORD_IWORD; GSYM IWORD_INT_SUB;
    INT_ARITH `x - y - z:int = x - (y + z)`] THEN
  MATCH_MP_TAC IVAL_IWORD THEN
  MP_TAC(ISPEC `x:64 word` IVAL_BOUND) THEN
  MP_TAC(ISPEC `y:64 word` IVAL_BOUND) THEN
  MP_TAC(SPEC `c:bool` BITVAL_BOUND) THEN
  REWRITE_TAC (GSYM INT_OF_NUM_LE :: SAIL_HL_X86_DIMS) THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN INT_ARITH_TAC);;

let SAIL_HL_X86_OVERFLOW_SBB = prove
 (`!x y:64 word. !c.
   ~(bit 64 (word_sub (word_sub (word_sx x:65 word) (word_sx y))
       (word(bitval c))) <=>
     bit 63 (word_sub (word_sub (word_sx x:65 word) (word_sx y))
       (word(bitval c)))) <=>
   ~(ival x - (ival y + &(bitval c)) =
     ival(word_sub x (word_add y (word(bitval c)))))`,
  SIMP_TAC (SAIL_HL_X86_WIDE_OVERFLOW :: SAIL_HL_X86_SIGNED_DIFFERENCE ::
            SAIL_HL_X86_LOW_SUB `:65` `:64` :: WORD_ZX_BITVAL ::
            SAIL_HL_X86_SX_LOW :: SAIL_HL_X86_DIMS) THEN
  REWRITE_TAC[WORD_RULE
    `word_sub (word_sub x y) z:N word = word_sub x (word_add y z)`]);;

(* The unsigned subtraction 0-x wraps exactly when x is nonzero. NEG's
   documented carry condition is therefore the ordinary subtraction borrow,
   not a separate interpretation of the instruction's flag write. *)
let SAIL_HL_X86_NEG_CARRY = prove
 (`!x:N word. -- &(val x):int = &(val(word_neg x)) <=> x = word 0`,
  GEN_TAC THEN REWRITE_TAC[INT_VAL_WORD_NEG] THEN
  ASM_CASES_TAC `x:N word = word 0` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; INT_MUL_RZERO; INT_MUL_RID; INT_SUB_LZERO] THEN
  MP_TAC(SPEC `dimindex(:N)` INT_LT_POW2) THEN INT_ARITH_TAC);;

(* Integer and natural-number products give the same truncated word.
   Source widths need not equal the result width for this identity. *)
let SAIL_HL_X86_UNSIGNED_PRODUCT = prove
 (`!x:N word. !y:P word.
   (iword(&(val x) * &(val y)):M word) = word(val x * val y)`,
  REWRITE_TAC[WORD_IWORD; INT_OF_NUM_MUL]);;

let SAIL_HL_X86_ZERO_EXTEND64 =
  let widen = CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [`:64`,`:M`; `:512`,`:N`] VAL_WORD_ZX) in
  prove
   (`!x:64 word. (word_zx x:512 word = word 0) <=> x = word 0`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; widen]);;

(* Signed 64-bit operands have absolute value at most 2^63, so their
   product is bounded by 2^126 and fits within signed 128 bits. *)
let SAIL_HL_X86_SIGNED_PRODUCT128 = prove
 (`!x:64 word. !y:64 word.
   ival(iword(ival x * ival y):128 word) = ival x * ival y`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `abs(ival(x:64 word)) <= &2 pow 63 /\
    abs(ival(y:64 word)) <= &2 pow 63`
   STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `x:64 word` IVAL_BOUND) THEN
    MP_TAC(ISPEC `y:64 word` IVAL_BOUND) THEN
    REWRITE_TAC[INT_ABS_BOUNDS; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC IVAL_IWORD THEN
  MP_TAC(ISPECL
    [`abs(ival(x:64 word))`; `(&2 pow 63):int`;
     `abs(ival(y:64 word))`; `(&2 pow 63):int`] INT_LE_MUL2) THEN
  ASM_REWRITE_TAC[INT_ABS_POS; GSYM INT_ABS_MUL; INT_ABS_BOUNDS] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN INT_ARITH_TAC);;

(* A low 64-bit view forgets the 128-bit intermediate truncation. The integer
   is unrestricted: this cast identity does not require a product bound. *)
let SAIL_HL_X86_LOW_IWORD128 =
  let remainder = CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC INT_REDUCE_CONV)
    (INST_TYPE [`:64`,`:N`] IWORD_REM_SIZE) in
  prove
   (`!z:int. word_zx(iword z:128 word):64 word = iword z`,
    GEN_TAC THEN REWRITE_TAC[WORD_ZX_SUBWORD; DIMINDEX_64] THEN
    SIMP_TAC[SAIL_HL_X86_SUBWORD_IWORD; DIMINDEX_128;
             ARITH_RULE `0 + 64 <= 128`; INT_DIV_1] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[INT_DIV_1; remainder] THEN REFL_TAC);;

(* A 128-bit value fits signed 64 bits exactly when its high half repeats
   the sign of its low half. Bit reasoning sees an opaque value here. *)
let SAIL_HL_X86_SIGNED_FIT128 =
  let sign_extension = CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [`:64`,`:M`; `:128`,`:N`] IVAL_WORD_SX) in
  prove
   (`!z:128 word.
     ~(word_subword z (64,64):64 word =
       word_sx(word(bitval(bit 63 z)):1 word):64 word) <=>
     ~(ival z = ival(word_zx z:64 word))`,
    GEN_TAC THEN GEN_REWRITE_TAC
      (RAND_CONV o RAND_CONV o RAND_CONV) [GSYM sign_extension] THEN
    REWRITE_TAC[IVAL_EQ] THEN BITBLAST_TAC);;

(* An undefined one-bit source flag permits both Boolean flag values.
   This proves the exact choice set; it does not pick a convenient witness
   or make any other architectural component undefined. *)
let SAIL_HL_X86_ARBITRARY_BIT0 = prove
 (`!P:bool->bool. (?w:1 word. P(bit 0 w)) <=> (?b:bool. P b)`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `w:1 word`) THEN
    EXISTS_TAC `bit 0 (w:1 word)` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `b:bool`) THEN
    EXISTS_TAC `word(bitval b):1 word` THEN
    ASM_REWRITE_TAC[BIT_WORD_BITVAL]]);;
