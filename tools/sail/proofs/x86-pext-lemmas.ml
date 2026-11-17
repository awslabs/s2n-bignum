(* Facts about Sail's PEXT loop, for the x86-pext suite.

   Sail's PEXT scans the mask bit by bit. Step i reads bit i of the source
   and of the mask, stores their conjunction at position k of a temporary
   and adds mask bit i to k:

     temp[k] = src[i] & mask[i];  k = (k + unsigned(mask[i])) % 64

   The generated relation unrolls the 32 or 64 steps into a chain of lets.
   The proof folds each step into one application of an opaque function
   on the pair (k, temp). Passing the preceding pair once avoids copying
   it through separate FST and SND arguments, and leaves the steps
   recognizable. The proof then uses induction on the number of steps:
   after n steps, let c be the number of set mask bits below n. Then
   k = c modulo 64, and the temporary is the sum that s2n-bignum's
   word_condense takes, below 2^c. *)
needs "tools/sail/proofs/x86-scalar-lemmas.ml";;

(* One step of the loop, on the pair (k, temp), for source x and mask y. *)
let SAIL_HL_X86_PEXT_STEP = new_definition
 `sail_hl_x86_pext_step (i:num) (x:64 word) (y:64 word) (p:int#64 word) =
    ((FST p + &(val(word(bitval(bit i y)):1 word))) rem &64,
     (word_insert (SND p) (num_of_int (FST p),1)
        (word_and (word(bitval(bit i x)):1 word)
                  (word(bitval(bit i y)):1 word)):64 word))`;;

(* The body of one step as the generated relation has it. *)
let SAIL_HL_X86_PEXT_INNER = prove
 (`!i x y k t (s:A).
    (let u1 = word(bitval(bit i x)):1 word in
     let u2 = word(bitval(bit i y)):1 word in
     let u3 = word_and u1 u2 in
     let u4 = word_insert (t:64 word) (num_of_int k,1) u3 in
     let u5 = word(bitval(bit i y)):1 word in
     let u6 = &(val u5):int in
     let u7 = k + u6 in
     let u8 = u7 rem &64 in
     s,u8,u4) =
    (s,sail_hl_x86_pext_step i (x:64 word) (y:64 word) (k,t))`,
  REWRITE_TAC[LET_DEF; LET_END_DEF; SAIL_HL_X86_PEXT_STEP; FST; SND]);;

(* The let that destructs a step's result: the step's value is not a
   tuple of three, so the let is not reduced by beta-conversion. *)
let SAIL_HL_X86_PEXT_OUTER = prove
 (`!(f:S->int->64 word->A) s i x y p.
     (let (a,b,c) = (s,sail_hl_x86_pext_step i x y p) in f a b c) =
     f s (FST(sail_hl_x86_pext_step i x y p))
         (SND(sail_hl_x86_pext_step i x y p))`,
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM PAIR] THEN
  CONV_TAC(LAND_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* Rewrite the chain of step lets from its first let to its last. After
   each let the next step's argument is (FST p, SND p) for the pair p that
   the step before returned; fold it back to p before the next let, so
   that p is copied once and not twice. *)
let rec SAIL_HL_X86_PEXT_CHAIN_CONV tm =
  (REWR_CONV SAIL_HL_X86_PEXT_OUTER THENC
   RAND_CONV(DEPTH_CONV(REWR_CONV PAIR)) THENC
   TRY_CONV SAIL_HL_X86_PEXT_CHAIN_CONV) tm;;

(* The pair after n steps, for source x and mask y. *)
let SAIL_HL_X86_PEXT_STEPS = new_recursive_definition num_RECURSION
 `(sail_hl_x86_pext_steps x y 0 = (&0:int, word 0:64 word)) /\
  (!n. sail_hl_x86_pext_steps x y (SUC n) =
       sail_hl_x86_pext_step n x y (sail_hl_x86_pext_steps x y n))`;;

(* The chain of n steps that the generated relation unrolls: its steps are
   applied to each other, so the term has n applications and no copies. *)
let SAIL_HL_X86_PEXT_UNROLL n =
  let rec go k =
    if k = 0 then CONJUNCT1 SAIL_HL_X86_PEXT_STEPS else
    let eq = CONV_RULE(LAND_CONV(RAND_CONV NUM_SUC_CONV))
      (SPEC (mk_small_numeral (k-1)) (CONJUNCT2 SAIL_HL_X86_PEXT_STEPS)) in
    TRANS eq (AP_TERM (mk_comb(mk_comb(mk_comb(`sail_hl_x86_pext_step`,
      mk_small_numeral(k-1)),`x:64 word`),`y:64 word`)) (go (k-1))) in
  go n;;

(* Facts about the sums that the steps compute. *)
let SAIL_HL_X86_PEXT_POPCOUNT_PREFIX = prove
 (`!(y:N word) i. i <= dimindex(:N)
    ==> word_popcount(word_and y (word(2 EXP i - 1))) =
        nsum {j | j < i} (\j. bitval(bit j y))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_POPCOUNT_NSUM; BIT_WORD_AND; BIT_MASK_WORD; bitval;
              GSYM NSUM_RESTRICT_SET] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `j:num` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LTE_TRANS]);;

let SAIL_HL_X86_PEXT_PREFIX_BOUND = prove
 (`!(y:N word) n. nsum {j | j < n} (\j. bitval(bit j y)) <= n`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; NSUM_CLAUSES; LE_REFL];
    REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT] THEN
    MP_TAC(SPEC `bit n (y:N word)` BITVAL_BOUND) THEN ASM_ARITH_TAC]);;

(* Setting a bit of a sum that is below 2^k, at position k. *)
let SAIL_HL_X86_PEXT_INSERT_BIT = prove
 (`!s k (b:1 word). s < 2 EXP k /\ k < 64
     ==> (word_insert (word s:64 word) (k,1) b:64 word) =
         word(s + 2 EXP k * val b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_insert] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `val(word s:64 word) = s` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP k` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[DIMINDEX_64] THEN
    REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s DIV 2 EXP (k + 1) = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_LT THEN REWRITE_TAC[EXP_ADD] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s MOD 2 EXP k = s` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val(b:1 word) MOD 2 EXP 1 = val b` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `b:1 word` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_1]; ALL_TAC] THEN
  ARITH_TAC);;

let SAIL_HL_X86_PEXT_VAL_BITVAL = prove
 (`!b. val(word(bitval b):1 word) = bitval b`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV);;

let SAIL_HL_X86_PEXT_VAL_AND = prove
 (`!a b. val(word_and (word(bitval a):1 word) (word(bitval b))) = bitval(a /\ b)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `a:bool` THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV);;

(* After n <= 64 steps, let c be the number of set mask bits below n.
   Then k = c modulo 64, and the temporary is the sum of word_condense
   over the first n bits, below 2^c. Before another step, c <= n < 64
   implies k = c; after an all-ones mask's 64th step, k wraps to zero
   but no further bit is inserted. *)
let SAIL_HL_X86_PEXT_STEPS_INVARIANT = prove
 (`!(x:64 word) (y:64 word) n. n <= 64
   ==> FST(sail_hl_x86_pext_steps x y n) =
         &(nsum {j | j < n} (\j. bitval(bit j y))) rem &64 /\
       SND(sail_hl_x86_pext_steps x y n) =
         word(nsum {i | i < n}
                (\i. 2 EXP (nsum {j | j < i} (\j. bitval(bit j y))) *
                     bitval(bit i x /\ bit i y))) /\
       nsum {i | i < n}
         (\i. 2 EXP (nsum {j | j < i} (\j. bitval(bit j y))) *
              bitval(bit i x /\ bit i y))
       < 2 EXP (nsum {j | j < n} (\j. bitval(bit j y)))`,
  REPEAT GEN_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; NSUM_CLAUSES;
                SAIL_HL_X86_PEXT_STEPS] THEN
    REWRITE_TAC[EXP; LT_REFL; ARITH] THEN CONV_TAC INT_REDUCE_CONV;
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[CONJUNCT2 SAIL_HL_X86_PEXT_STEPS; SAIL_HL_X86_PEXT_STEP;
                FST; SND] THEN
    ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; SAIL_HL_X86_PEXT_VAL_BITVAL;
                    SAIL_HL_X86_PEXT_VAL_AND] THEN
    ABBREV_TAC `c = nsum {j | j < n} (\j. bitval(bit j (y:64 word)))` THEN
    ABBREV_TAC `s = nsum {i | i < n}
      (\i. 2 EXP (nsum {j | j < i} (\j. bitval(bit j (y:64 word)))) *
           bitval(bit i (x:64 word) /\ bit i y))` THEN
    SUBGOAL_THEN `c <= n` ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN MATCH_ACCEPT_TAC SAIL_HL_X86_PEXT_PREFIX_BOUND;
      ALL_TAC] THEN
    SUBGOAL_THEN `c < 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&c rem &64 = (&c:int)` SUBST_ALL_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_REM] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[NUM_OF_INT_OF_NUM; INT_OF_NUM_ADD] THEN
    MP_TAC(ISPECL [`s:num`; `c:num`;
      `word_and (word(bitval(bit n (x:64 word))):1 word)
                (word(bitval(bit n (y:64 word))))`]
      SAIL_HL_X86_PEXT_INSERT_BIT) THEN
    ASM_REWRITE_TAC[SAIL_HL_X86_PEXT_VAL_AND] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY BOOL_CASES_TAC [`bit n (x:64 word)`; `bit n (y:64 word)`] THEN
    REWRITE_TAC[BITVAL_CLAUSES; EXP_ADD; EXP_1; EXP; ADD_CLAUSES;
                MULT_CLAUSES] THEN ASM_ARITH_TAC]);;

let SAIL_HL_X86_PEXT_ZX_WORD = prove
 (`!s. dimindex(:N) <= 64
       ==> word_zx (word s:64 word) = (word s:N word)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ZX; BIT_WORD; DIMINDEX_64] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < 64` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

(* word_condense of two N-bit words (N <= 64) is the low N bits of the
   temporary after N steps on their zero extensions. *)
let SAIL_HL_X86_PEXT_CONDENSE = prove
 (`!(a:N word) (b:N word). dimindex(:N) <= 64
    ==> word_zx
          (SND(sail_hl_x86_pext_steps (word_zx a:64 word) (word_zx b:64 word)
                                      (dimindex(:N)))):N word =
        word_condense a b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`word_zx (a:N word):64 word`; `word_zx (b:N word):64 word`;
                `dimindex(:N)`] SAIL_HL_X86_PEXT_STEPS_INVARIANT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SAIL_HL_X86_PEXT_ZX_WORD] THEN
  REWRITE_TAC[word_condense] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `word_popcount(word_and (b:N word) (word(2 EXP i - 1))) =
    nsum {j | j < i} (\j. bitval(bit j (word_zx (b:N word):64 word)))`
   SUBST1_TAC THENL
   [MP_TAC(SPECL [`b:N word`; `i:num`] SAIL_HL_X86_PEXT_POPCOUNT_PREFIX) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[LT_IMP_LE]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM; BIT_WORD_ZX] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `j < dimindex(:N)` ASSUME_TAC THENL
     [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `j < 64` ASSUME_TAC THENL
     [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `dimindex(:N)` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[DIMINDEX_64];
    SUBGOAL_THEN `i < 64` ASSUME_TAC THENL
     [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `dimindex(:N)` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[BIT_WORD_AND; BIT_WORD_ZX; DIMINDEX_64]]);;

(* The two widths of the PEXT instruction, with dimindex evaluated. *)
let SAIL_HL_X86_PEXT_CONDENSE_32 =
  CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (REWRITE_RULE[DIMINDEX_CONV `dimindex(:32)`; ARITH]
      (INST_TYPE [`:32`,`:N`] SAIL_HL_X86_PEXT_CONDENSE));;

let SAIL_HL_X86_PEXT_CONDENSE_64 =
  REWRITE_RULE[WORD_ZX_TRIVIAL]
    (CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
      (REWRITE_RULE[DIMINDEX_CONV `dimindex(:64)`; ARITH]
        (INST_TYPE [`:64`,`:N`] SAIL_HL_X86_PEXT_CONDENSE)));;
