(* Facts about Sail's branchless bit counts, for the x86-count suite.

   Sail's popcount adds the bits of a 64-bit word in six masked steps, ctz
   is the popcount of ~x & (x - 1), and clz is the width minus the popcount
   of x smeared downwards from its top bit. s2n-bignum's definitions use
   word_popcount, word_ctz and word_clz, which HOL Light defines through
   sets of bit positions and minimal indices. This file proves, once and for
   every operand, that the branchless calculations compute those values.

   - The six-step popcount of y is word (word_popcount y). It is a
     statement about 64 independent bits, which the bit-blaster proves
     after word_popcount is written as a sum of 64 bits.
   - The smear of x has the bits below and including the top bit of x set.
     For each possible position of that bit, the bit-blaster proves that
     smear x is the mask of that many ones; word_clz fixes the position.

   The facts have the shape of the generated bodies after normalization, so
   that rewriting applies them to the operand of each root. *)
needs "tools/sail/proofs/x86-select-lemmas.ml";;

(* One masked addition step of the six-step popcount, on any word. *)
let sail_hl_swar_steps =
  ["6148914691236517205",1; "3689348814741910323",2;
   "1085102592571150095",4; "71777214294589695",8;
   "281470681808895",16; "4294967295",32];;

let sail_hl_swar_string operand =
  List.fold_left (fun x (mask,shift) ->
    Printf.sprintf "(word_add (word_and %s (word %s:64 word)) \
                    (word_and (word_ushr %s %d) (word %s:64 word)))"
      x mask x shift mask) operand sail_hl_swar_steps;;

let sail_hl_smear_string operand =
  List.fold_left (fun x shift ->
    Printf.sprintf "(word_or %s (word_ushr %s %d))" x x shift)
    operand [1;2;4;8;16;32];;

(* Replace one dimension type by a numeral and evaluate dimindex. *)
let sail_hl_instantiate_width width theorem =
  CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [mk_finty(num width),`:N`] theorem);;

(* The same for VAL_WORD_ZX, which has a source M and a target N. *)
let sail_hl_instantiate_width_to source target theorem =
  CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [mk_finty(num source),`:M`; mk_finty(num target),`:N`]
      theorem);;

let SAIL_HL_X86_SWAR64_POPCOUNT = prove
 (parse_term("!y:64 word. " ^ sail_hl_swar_string "y" ^
             " = word(word_popcount y)"),
  GEN_TAC THEN CONV_TAC(RAND_CONV(RAND_CONV WORD_POPCOUNT_EXPAND_CONV)) THEN
  BITBLAST_TAC);;

let SAIL_HL_X86_POPCOUNT_ZX = prove
 (`!y:N word. dimindex(:N) <= dimindex(:M)
    ==> word_popcount (word_zx y:M word) = word_popcount y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_popcount] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; bits_of_word; IN_ELIM_THM; BIT_WORD_ZX] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[BIT_GUARD; LTE_TRANS]);;

let SAIL_HL_X86_POPCOUNT_MASK = prove
 (`!k. k <= dimindex(:N) ==> word_popcount(word(2 EXP k - 1):N word) = k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[word_popcount; bits_of_word; BIT_MASK_WORD] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_ARITH_TAC);;

(* The six-step popcount of a word of the given width, zero-extended to
   64 bits as Sail does before counting. *)
let sail_hl_swar_popcount width =
  if width = 64 then SAIL_HL_X86_SWAR64_POPCOUNT else
  let operand = Printf.sprintf "(word_zx (y:%d word):64 word)" width in
  prove(parse_term(Printf.sprintf
    "!y:%d word. %s = word(word_popcount y)" width
    (sail_hl_swar_string operand)),
   GEN_TAC THEN REWRITE_TAC[SAIL_HL_X86_SWAR64_POPCOUNT] THEN
   AP_TERM_TAC THEN MATCH_ACCEPT_TAC(sail_hl_instantiate_width width
     (INST_TYPE [`:64`,`:M`] SAIL_HL_X86_POPCOUNT_ZX)));;

let SAIL_HL_X86_SWAR_POPCOUNTS =
  map (fun width -> width,sail_hl_swar_popcount width) [64;32;16];;
let SAIL_HL_X86_SWAR_POPCOUNT width = assoc width SAIL_HL_X86_SWAR_POPCOUNTS;;

(* The position of the top bit of x fixes the smear. *)
let SAIL_HL_X86_CLZ_SMEAR_FACTS = prove
 (`!x:N word. ~(x = word 0)
    ==> word_ushr x (dimindex(:N) - word_clz x) = word 0 /\
        word_ushr x (dimindex(:N) - word_clz x - 1) = word 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:N word`; `word_clz(x:N word)`] WORD_CLZ_UNIQUE_GEN) THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPEC `x:N word` WORD_CLZ_LT_DIMINDEX) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_0; BIT_WORD_1] THEN
  REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN
      `dimindex(:N) - word_clz(x:N word) <=
       i + dimindex(:N) - word_clz x` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_MESON_TAC[]];
    ASM_CASES_TAC `i = 0` THENL
     [ASM_REWRITE_TAC[ADD_CLAUSES] THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
        `dimindex(:N) - word_clz(x:N word) <=
         i + dimindex(:N) - word_clz x - 1` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ASM_MESON_TAC[]]]]);;

(* For each k from 1 to the width: if x has its top bit at position k - 1
   then the smear is the mask of k ones. One bit-blasting case per k. *)
let sail_hl_smear_cases width =
  prove(parse_term(Printf.sprintf
    "!x:%d word. !k. k <= %d ==> 1 <= k ==> word_ushr x k = word 0 ==> \
     word_ushr x (k-1) = word 1 ==> %s = word(2 EXP k - 1)"
    width width (sail_hl_smear_string "x")),
   GEN_TAC THEN REWRITE_TAC[ARITH_RULE `k <= n <=> k < n + 1`] THEN
   CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
   CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
   REPEAT CONJ_TAC THEN BITBLAST_TAC);;

(* The popcount of the smear is the width minus the leading zeros. *)
let sail_hl_clz_popcount width =
  let ty = mk_finty(num width) in
  let cases = sail_hl_smear_cases width in
  let facts = sail_hl_instantiate_width width SAIL_HL_X86_CLZ_SMEAR_FACTS in
  let mask = sail_hl_instantiate_width width SAIL_HL_X86_POPCOUNT_MASK in
  let below = sail_hl_instantiate_width width WORD_CLZ_LT_DIMINDEX in
  let x = parse_term(Printf.sprintf "x:%d word" width) in
  let clz = parse_term(Printf.sprintf "word_clz(x:%d word)" width) in
  let small = mk_comb(mk_comb(`(<):num->num->bool`,clz),
                      mk_small_numeral width) in
  let top = parse_term(Printf.sprintf "%d - word_clz(x:%d word)" width width) in
  ignore ty;
  prove(parse_term(Printf.sprintf
    "!x:%d word. word_popcount(%s) = %d - word_clz x" width
    (sail_hl_smear_string "x") width),
   GEN_TAC THEN ASM_CASES_TAC (parse_term(Printf.sprintf "x:%d word = word 0" width)) THENL
    [ASM_REWRITE_TAC[WORD_CLZ_0; WORD_POPCOUNT_0] THEN
     CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC WORD_REDUCE_CONV) THEN
     CONV_TAC NUM_REDUCE_CONV;
     FIRST_ASSUM(MP_TAC o MATCH_MP facts) THEN STRIP_TAC THEN
     SUBGOAL_THEN small ASSUME_TAC THENL
      [REWRITE_TAC[below] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MP_TAC(SPECL [x; top] cases) THEN
     ANTS_TAC THENL [UNDISCH_TAC small THEN ARITH_TAC; ALL_TAC] THEN
     ANTS_TAC THENL [UNDISCH_TAC small THEN ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC mask THEN
     UNDISCH_TAC small THEN ARITH_TAC]);;

let SAIL_HL_X86_CLZ_POPCOUNTS =
  map (fun width -> width,sail_hl_clz_popcount width) [64;32;16];;
let SAIL_HL_X86_CLZ_POPCOUNT width = assoc width SAIL_HL_X86_CLZ_POPCOUNTS;;

let SAIL_HL_X86_WORD_NOT_BITVAL = prove
 (`!b. word_not (word(bitval b):1 word) = word(bitval(~b))`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* Facts for one operand width, as rewrites that match the normalized
   generated bodies. In the bodies, a register read at width w is the
   low subword of the 64-bit register, a count is a 64-bit word that is
   cut to w bits, and Sail's nonzero test zero-extends to 512 bits. *)

(* x is zero iff its zero extension to 512 bits is. *)
let SAIL_HL_X86_ZERO_EXTEND_512 width =
  prove(parse_term(Printf.sprintf
    "!x:%d word. (word_zx x:512 word = word 0) <=> x = word 0" width),
   REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0;
     sail_hl_instantiate_width_to width 512 VAL_WORD_ZX]);;

(* Casting a numeral to a word of M bits and then to one of N <= M bits is
   casting it to N bits at once. *)
let SAIL_HL_X86_ZX_WORD_GENERIC = prove
 (`!k. dimindex(:N) <= dimindex(:M)
       ==> word_zx(word k:M word):N word = word k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ZX; BIT_WORD] THEN
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `i < dimindex(:M)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let SAIL_HL_X86_ZX_WORD target source =
  prove(parse_term(Printf.sprintf
    "!k. word_zx(word k:%d word):%d word = word k" source target),
   GEN_TAC THEN MATCH_MP_TAC
     (INST_TYPE [mk_finty(num target),`:N`; mk_finty(num source),`:M`]
       (SPEC_ALL SAIL_HL_X86_ZX_WORD_GENERIC)) THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV));;

let SAIL_HL_X86_CTZ_VAL width target =
  prove(parse_term(Printf.sprintf
    "!x:%d word. val(word(word_ctz x):%d word) = word_ctz x" width target),
   GEN_TAC THEN REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
   MP_TAC(ISPEC (parse_term(Printf.sprintf "x:%d word" width))
     WORD_CTZ_LE_DIMINDEX) THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN ARITH_TAC);;

let SAIL_HL_X86_CTZ_BOUND width =
  prove(parse_term(Printf.sprintf "!x:%d word. word_ctz x <= %d" width width),
   GEN_TAC THEN MP_TAC(ISPEC (parse_term(Printf.sprintf "x:%d word" width))
     WORD_CTZ_LE_DIMINDEX) THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN REWRITE_TAC[]);;

let SAIL_HL_X86_CLZ_VAL width target =
  prove(parse_term(Printf.sprintf
    "!x:%d word. val(word(word_clz x):%d word) = word_clz x" width target),
   GEN_TAC THEN REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
   MP_TAC(ISPEC (parse_term(Printf.sprintf "x:%d word" width))
     WORD_CLZ_LE_DIMINDEX) THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN ARITH_TAC);;

(* LZCNT's result is the width minus the popcount of the smear, computed
   in the integers and cast back. *)
let SAIL_HL_X86_SUB_VAL width target =
  prove(parse_term(Printf.sprintf
    "!x:%d word. val(word(%d - word_clz x):%d word) = %d - word_clz x"
    width width target width),
   GEN_TAC THEN REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN ARITH_TAC);;

let SAIL_HL_X86_SUB_BOUND width =
  prove(parse_term(Printf.sprintf "!c. %d - c <= %d" width width), ARITH_TAC);;

let SAIL_HL_X86_INT_SUB width =
  prove(parse_term(Printf.sprintf
    "!x:%d word. &%d - &(%d - word_clz x) = (&(word_clz x):int)"
    width width width),
   GEN_TAC THEN MP_TAC(ISPEC (parse_term(Printf.sprintf "x:%d word" width))
     WORD_CLZ_LE_DIMINDEX) THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
   DISCH_TAC THEN
   ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; ARITH_RULE (parse_term(Printf.sprintf
     "c <= %d ==> %d - c <= %d" width width width))] THEN INT_ARITH_TAC);;

(* A popcount is at most the width, so it survives a cast to a word of
   that width or more, and passes Sail's bound check on 64 bits. *)
let SAIL_HL_X86_POPCOUNT_VAL width target =
  prove(parse_term(Printf.sprintf
    "!x:%d word. val(word(word_popcount x):%d word) = word_popcount x"
    width target),
   GEN_TAC THEN REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
   MP_TAC(ISPEC (parse_term(Printf.sprintf "x:%d word" width))
     WORD_POPCOUNT_BOUND) THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN ARITH_TAC);;

let SAIL_HL_X86_POPCOUNT_BOUND width =
  prove(parse_term(Printf.sprintf
    "!x:%d word. word_popcount x <= 64" width),
   GEN_TAC THEN MP_TAC(ISPEC (parse_term(Printf.sprintf "x:%d word" width))
     WORD_POPCOUNT_BOUND) THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN ARITH_TAC);;

(* BSR: the leading zeros of zero_extend(x) | 1, for x nonzero, are those of
   x together with the extension. *)
let SAIL_HL_X86_CLZ_OR_ONE_GENERIC = prove
 (`!x:N word. ~(x = word 0) /\ dimindex(:N) <= dimindex(:M)
     ==> word_clz(word_or (word_zx x:M word) (word 1)) =
         dimindex(:M) - dimindex(:N) + word_clz x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:N word`; `word_clz(x:N word)`] WORD_CLZ_UNIQUE_GEN) THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPEC `x:N word` WORD_CLZ_LT_DIMINDEX) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[WORD_CLZ_UNIQUE_GEN; BIT_WORD_OR; BIT_WORD_ZX; BIT_WORD_1] THEN
  SUBGOAL_THEN
    `dimindex(:M) - (dimindex(:M) - dimindex(:N) + word_clz(x:N word)) =
     dimindex(:N) - word_clz x` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      DISJ1_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]]];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(i = 0)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_MESON_TAC[]]]);;

let SAIL_HL_X86_CLZ_OR_ONE width =
  let generic = INST_TYPE [mk_finty(num width),`:N`; `:64`,`:M`]
    SAIL_HL_X86_CLZ_OR_ONE_GENERIC in
  prove(parse_term(Printf.sprintf
    "!x:%d word. ~(x = word 0) ==> \
     word_clz(word_or (word_zx x:64 word) (word 1)) = %d + word_clz x"
    width (64 - width)),
   GEN_TAC THEN DISCH_TAC THEN
   MP_TAC(SPEC_ALL generic) THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
   ASM_REWRITE_TAC[]);;

(* BSR counts the leading zeros of y = zero_extend(x) | 1 with Sail's
   smear and six-step popcount. The generated body is a chain of lets,
   each of which uses the previous value twice, and the popcount that
   ends the chain occurs three times once the next lets are substituted
   (in the first bound check and, through 64 minus it, in the second check
   and in the index). Substituting the lets copies the operand 2^12 times
   for each occurrence: the goal grows to 660,000 nodes, and rewriting it
   overflows the 8 MiB stack of the compiled proof drivers.

   The fact below is about the chain as it stands, before any let is
   substituted. For every continuation P, the chain that ends in the
   popcount of the smear of y passes P the value word(64 - word_clz y).
   Rewriting the generated chain with it replaces 38 lets by one value,
   which stays small however often P uses it. The fact itself is proved
   on a variable y, where the substituted chain has about 4096 leaves. *)
let SAIL_HL_X86_BSR_CHAIN =
  let smear = String.concat " in " (map (fun k ->
    Printf.sprintf "let a%d = word_ushr b%d (num_of_int (&%d)) in \
                    let b%d = word_or b%d a%d" k (k/2) k k (k/2) k)
    [1;2;4;8;16;32]) in
  let popcount = String.concat " in " (map (fun (mask,k) ->
    Printf.sprintf "let p%d = word_and c%d (word %s:64 word) in \
                    let q%d = word_ushr c%d (num_of_int (&%d)) in \
                    let r%d = word_and q%d (word %s:64 word) in \
                    let c%d = word_add p%d r%d"
      k (k/2) mask k (k/2) k k k mask k k k) sail_hl_swar_steps) in
  prove(parse_term(
    "!y:64 word. !P:64 word->A. \
       (let b0 = word_or y (word 1) in " ^ smear ^
     " in let c0 = word_zx b32:64 word in " ^ popcount ^
     " in P c32) = P (word(64 - word_clz(word_or y (word 1))))"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF; WORD_ZX_TRIVIAL; NUM_OF_INT_OF_NUM] THEN
   AP_TERM_TAC THEN
   REWRITE_TAC[SAIL_HL_X86_SWAR_POPCOUNT 64; SAIL_HL_X86_CLZ_POPCOUNT 64]);;

(* The bit scan reverse of a zero-extended word has a leading-zero count
   below 64, so Sail's check `x < 'n` holds and the integer result is
   63 minus that count. *)
let SAIL_HL_X86_CLZ_OR_ONE_BOUND = prove
 (`!y:64 word. word_clz(word_or y (word 1)) < 64`,
  GEN_TAC THEN
  MP_TAC(ISPEC `word_or (y:64 word) (word 1)` WORD_CLZ_LT_DIMINDEX) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_WORD_0; BIT_WORD_1] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let SAIL_HL_X86_INT_SUB_63 = prove
 (`!y:64 word. &63 - &(word_clz(word_or y (word 1))) =
               (&(63 - word_clz(word_or y (word 1))):int)`,
  GEN_TAC THEN
  MP_TAC(SPEC `y:64 word` SAIL_HL_X86_CLZ_OR_ONE_BOUND) THEN DISCH_TAC THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; ARITH_RULE
    `c < 64 ==> c <= 63`]);;

(* 63 - (48 + c) is the width minus 1 minus c, for every c. *)
let SAIL_HL_X86_SCAN_ARITH width =
  prove(parse_term(Printf.sprintf
    "!c. 63 - (%d + c) = %d - c" (64 - width) (width - 1)), ARITH_TAC);;

(* A 16-bit destination is the low part of the register. *)
let SAIL_HL_X86_JOIN16 = prove
 (`!r:64 word. word_join (word_subword r (16,48):48 word) (word_zx r:16 word):64 word = r`,
  GEN_TAC THEN BITBLAST_TAC);;
let SAIL_HL_X86_JOINLOW16 = prove
 (`!h l:16 word. word_zx (word_join (h:48 word) l:64 word):16 word = l`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* The same for a 32-bit destination, whose upper half is undefined after
   a scan of a zero source: a register whose low half is the old one is
   the old low half with some upper half. *)
let SAIL_HL_X86_JOINLOW32 = prove
 (`!(h:32 word) (l:32 word). word_zx (word_join h l:64 word):32 word = l`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;
let SAIL_HL_X86_JOINSPLIT32 = prove
 (`!(y:64 word) (r:64 word). word_zx y:32 word = word_zx r
     ==> word_join (word_subword y (32,32):32 word) (word_zx r:32 word):64 word = y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN POP_ASSUM MP_TAC THEN BITBLAST_TAC);;
