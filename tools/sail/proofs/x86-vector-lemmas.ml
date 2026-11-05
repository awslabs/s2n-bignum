(* Mathematical bridges between integer calculations and word operations.
   These are kernel-proved identities, not instruction conformance claims.
   Keep lane products opaque: expanding their bits makes multiplication
   proofs unnecessarily expensive. The vector driver separately proves
   register writes, aliases, flags and the complete remaining state. *)
needs "Library/words.ml";;
needs "tools/sail/proofs/tuple-apply-conv.ml";;

(* The retained ModR/M decoder joins one extension bit to three low bits.
   These identities recover the original four-bit register number and its
   bounded index; they do not replace decoding in a generated definition. *)
let SAIL_HL_X86_REGISTER_BITS = prove
 (`!r:4 word.
   word_join (word(bitval(bit 3 r)):1 word)
             (word_subword r (0,3):3 word):4 word = r`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_JOIN; BIT_WORD_BITVAL;
              BIT_WORD_SUBWORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SAIL_HL_X86_REGISTER_MOD = prove
 (`!r:4 word. word(val r MOD 16):4 word = r`,
  GEN_TAC THEN
  MP_TAC(ISPEC `r:4 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_4] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN ASM_SIMP_TAC[MOD_LT; WORD_VAL]);;

let SAIL_HL_X86_REGISTER_INDEX = prove
 (`!r:M word. (word(val r):N word) = word_zx r`,
  REWRITE_TAC[word_zx]);;

(* Evaluate a binding's value before substituting it into the body.
   The upstream loops reuse an accumulator in both branches of a known
   operation choice; substituting before pruning that choice duplicates
   the accumulator at every lane. Handle LET applications directly:
   a let that returns a function may already have further arguments.
   Tuple-pattern functions use the shared small beta schema with its direct
   result: instantiate all fields together rather than build projections
   through the large continuation. Other patterns retain stock beta.
   Factor common applications before substitution: (if p then (s,x) else
   (s,y)) becomes (s,if p then x else y). The same rule factors a shared
   word-insertion accumulator, so independent lane guards do not duplicate
   all earlier lanes. Limit this sharing to pairs and insertion: factoring
   word/numeral constructors would hide word-mask branches from subsequent
   bit simplification.

   Cache reductions within this one invocation. Upstream accumulators recur
   in several lanes, so a tree walk without a cache repeats the same work.
   Keys compare immutable HOL term objects by physical identity: a fresh
   but equal term only misses the cache. Restore the exact original left
   side with ALPHA if generalized beta renamed a binder, and reject an
   equality with assumptions or a different left side. No cache or theorem
   result is saved between kernel processes. *)
module Sail_hl_x86_term_identity = Hashtbl.Make(struct
  type t = term
  let equal left right = left == right
  let hash = Hashtbl.hash
end);;

let SAIL_HL_X86_STRICT_LET_CONV term =
  let cache = Sail_hl_x86_term_identity.create 1024 in
  let tuple_beta = SAIL_HL_TUPLE_APPLY_CONV ~contract_result:true () in
  let factor = REWR_CONV (GSYM COND_RAND) in
  let common_application term =
    (match term with
     | Comb(Comb(Comb(Const("COND",_),_),_),_) -> ()
     | _ -> failwith "strict let: not a conditional");
    let theorem = factor term in
    match fst(strip_comb(rand(concl theorem))) with
    | Const(",",_) | Const("word_insert",_) -> theorem
    | _ -> failwith "strict let: not a shared pair or insertion" in
  let beta term =
    match term with
    | Comb(Abs(_,_),_) -> BETA_CONV term
    | Comb(Comb(Const("GABS",_),_),_) ->
        (tuple_beta ORELSEC GEN_BETA_CONV) term
    | _ -> failwith "strict let: not an abstraction application" in
  let basic = common_application ORELSEC
    GEN_REWRITE_CONV I (LET_END_DEF :: basic_rewrites()) in
  let rec normalize term =
    try Sail_hl_x86_term_identity.find cache term with Not_found ->
      let theorem =
        ((CHANGED_CONV basic ORELSEC beta ORELSEC
          (fun term -> match term with
           | Comb(Comb(Const("LET",_),_),_) ->
               (RAND_CONV normalize THENC REWR_CONV LET_DEF THENC beta) term
           | _ -> failwith "strict let: not a LET application"))
         THENC normalize ORELSEC
         (CHANGED_CONV (SUB_CONV normalize) THENC normalize) ORELSEC REFL) term in
      let left = lhand(concl theorem) in
      if hyp theorem <> [] || not(aconv left term) then
        failwith "strict let cache: open or mismatched equality";
      let theorem = if left = term then theorem
        else TRANS(ALPHA term left) theorem in
      Sail_hl_x86_term_identity.add cache term theorem;
      theorem in
  normalize term;;

(* Observe one conditional lane without distributing the entire insertion
   chain into branches. The common accumulator remains shared. *)
let SAIL_HL_X86_BIT_COND = prove
 (`!i:num. !p:bool. !x y:N word.
   bit i (if p then x else y) <=> if p then bit i x else bit i y`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* Library/words.ml's final WORD_SUBWORD_IWORD binding uses the same type
   for the source and result. Retain the cross-width version here: a
   32-bit product has a 16-bit high half. *)
let SAIL_HL_X86_SUBWORD_IWORD = prove
 (`!x pos len.
   pos + len <= dimindex(:N)
   ==> word_subword (iword x:N word) (pos,len):M word =
       iword((x div &2 pow pos) rem &2 pow len)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_SUBWORD_AS_IWORD] THEN
  SIMP_TAC[INT_DIV_REM; INT_POW_LE; INT_POS; GSYM INT_POW_ADD] THEN
  ASM_SIMP_TAC[INT_REM_IVAL_IWORD]);;

let SAIL_HL_X86_HIGH16_IWORD =
  let remove_remainder = CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC INT_REDUCE_CONV)
    (INST_TYPE [`:16`,`:N`] IWORD_REM_SIZE) in
  prove
 (`!x:int.
   word_subword (iword x:32 word) (16,16):16 word =
   iword(x div &65536)`,
  GEN_TAC THEN
  SIMP_TAC[SAIL_HL_X86_SUBWORD_IWORD; DIMINDEX_32;
           ARITH_RULE `16 + 16 <= 32`] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[remove_remainder]);;

(* Express HOL's high-half multiply as the source integer quotient. The
   32-bit product stays opaque; no multiplication bits are expanded. *)
let SAIL_HL_X86_SIGNED_HIGH16 = prove
 (`!a:16 word. !b:16 word.
   word_subword
     (word_mul (word_sx a:32 word) (word_sx b:32 word)) (16,16):16 word =
   iword((ival a * ival b) div &65536)`,
  REWRITE_TAC[word_sx; GSYM IWORD_INT_MUL; SAIL_HL_X86_HIGH16_IWORD]);;

let SAIL_HL_X86_UNSIGNED_HIGH16 = prove
 (`!a:16 word. !b:16 word.
   word_subword
     (word_mul (word_zx a:32 word) (word_zx b:32 word)) (16,16):16 word =
   iword((&(val a) * &(val b)) div &65536)`,
  REWRITE_TAC[word_zx; WORD_IWORD; GSYM IWORD_INT_MUL;
              SAIL_HL_X86_HIGH16_IWORD]);;

(* Sign-extending a single Boolean bit gives an all-zero/all-one mask.
   This is shared by absolute value and signed comparison calculations. *)
let SAIL_HL_X86_SIGN_MASK = prove
 (`!p. word_sx(word(bitval p):1 word):N word =
       word_neg(word(bitval p))`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SX; BIT_WORD_BITVAL;
              BIT_WORD_MASK; DIMINDEX_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `MIN i 0 = 0`]);;

let SAIL_HL_X86_ABS_MASK = prove
 (`!x:N word.
   word_sub
     (word_xor x (word_sx(word(bitval(bit (dimindex(:N)-1) x)):1 word)))
     (word_sx(word(bitval(bit (dimindex(:N)-1) x)):1 word)) =
   if word_igt (word 0) x then word_neg x else x`,
  GEN_TAC THEN REWRITE_TAC
    [SAIL_HL_X86_SIGN_MASK; WORD_MASK; WORD_IGT; IVAL_WORD_0;
     INT_ARITH `(&0:int) > z <=> z < &0`; GSYM MSB_IVAL] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[WORD_XOR_0; WORD_XOR_NOT0; WORD_SUB_0; WORD_NOT_AS_SUB] THEN
  CONV_TAC WORD_RULE);;

(* Source indexing has already reduced to 31 when the lane is compared. *)
let SAIL_HL_X86_ABS_MASK32 = CONV_RULE
  (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
  (INST_TYPE [`:32`,`:N`] SAIL_HL_X86_ABS_MASK);;

(* A signed difference needs one extra bit. Its sign then tests the
   original operands' order without signed overflow. These two fixed
   instances match 16- and 32-bit lanes; no operand is restricted. *)
let SAIL_HL_X86_SIGNED_GREATER_DIFFERENCE width =
  let wide = width + 1 in
  let statement = parse_term (Printf.sprintf
    "!a:%d word. !b:%d word. \
     bit %d (word_sub (word_sx b:%d word) (word_sx a:%d word)) \
     <=> word_igt a b" width width width wide wide) in
  let wide_type = mk_finty(Num.num_of_int wide) in
  let sign = CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [wide_type,`:N`] MSB_IVAL) in
  prove(statement,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[word_sx; GSYM IWORD_INT_SUB; sign; WORD_IGT] THEN
    SUBGOAL_THEN (parse_term (Printf.sprintf
      "ival(iword(ival(b:%d word) - ival(a:%d word)):%d word) = \
       ival b - ival a" width width wide)) SUBST1_TAC THENL
    [MATCH_MP_TAC IVAL_IWORD THEN
     MP_TAC(ISPEC (parse_term(Printf.sprintf "a:%d word" width)) IVAL_BOUND) THEN
     MP_TAC(ISPEC (parse_term(Printf.sprintf "b:%d word" width)) IVAL_BOUND) THEN
     CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
     CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN INT_ARITH_TAC;
     INT_ARITH_TAC]);;

let SAIL_HL_X86_SIGNED_GREATER16 =
  SAIL_HL_X86_SIGNED_GREATER_DIFFERENCE 16;;
let SAIL_HL_X86_SIGNED_GREATER32 =
  SAIL_HL_X86_SIGNED_GREATER_DIFFERENCE 32;;

(* Logical shifts give zero at and beyond the word width. Compare Sail's
   explicit cutoff with HOL's clamped count without restricting any count. *)
let SAIL_HL_X86_USHR_TRIVIAL = prove
 (`!x:N word. !k.
   dimindex(:N) <= k ==> word_ushr x k = word 0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_0] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[] BIT_TRIVIAL) THEN ASM_ARITH_TAC);;

let SAIL_HL_X86_SHL_MIN = prove
 (`!x:N word. !k.
   word_shl x (MIN k (dimindex(:N))) =
   if dimindex(:N) <= k then word 0 else word_shl x k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MIN] THEN
  COND_CASES_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[WORD_SHL_TRIVIAL; LE_REFL] THEN ASM_ARITH_TAC);;

let SAIL_HL_X86_USHR_MIN = prove
 (`!x:N word. !k.
   word_ushr x (MIN k (dimindex(:N))) =
   if dimindex(:N) <= k then word 0 else word_ushr x k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MIN] THEN
  COND_CASES_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[SAIL_HL_X86_USHR_TRIVIAL; LE_REFL] THEN ASM_ARITH_TAC);;

(* Instruction normalization has already turned dimindex into a literal.
   Give the rewrite matcher the same fixed lane widths; this specializes
   proved word identities, not an instruction or its allowed counts. *)
let SAIL_HL_X86_SHIFT_MIN_REWRITES =
  List.concat_map (fun width ->
    map (fun theorem -> CONV_RULE
      (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
      (INST_TYPE [width,`:N`] theorem))
      [SAIL_HL_X86_SHL_MIN; SAIL_HL_X86_USHR_MIN])
    [`:16`;`:32`;`:64`];;

(* Uniform immediate shifts clamp counts above a lane's width. HOL's word
   shifts already give zero, or sign fill, for those counts. Both sides
   agree for every natural count; no instruction count is excluded. *)
let SAIL_HL_X86_SHL_CLAMP = prove
 (`!x:N word. !k.
   (if dimindex(:N) < k then word_shl x (dimindex(:N))
    else word_shl x k) = word_shl x k`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WORD_SHL_TRIVIAL; LE_REFL;
               ARITH_RULE `w < k ==> w <= k`]);;

let SAIL_HL_X86_USHR_CLAMP = prove
 (`!x:N word. !k.
   (if dimindex(:N) < k then word_ushr x (dimindex(:N))
    else word_ushr x k) = word_ushr x k`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SAIL_HL_X86_USHR_TRIVIAL; LE_REFL;
               ARITH_RULE `w < k ==> w <= k`]);;

let SAIL_HL_X86_ISHR_CLAMP = prove
 (`!x:N word. !k.
   (if dimindex(:N) < k then word_ishr x (dimindex(:N))
    else word_ishr x k) = word_ishr x k`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ISHR] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `~(i + w < w)`;
               ARITH_RULE `w < k ==> ~(i + k < w)`]);;

(* A conditional can enclose the whole insertion chain. Observe one lane
   bit first, then use the same clamping identity on that observation. *)
let SAIL_HL_X86_SHIFT_CLAMP_BITS theorem =
  let x,k = `x:N word`,`k:num` in
  let equality = SPECL [x;k] theorem in
  let bit_equality = AP_TERM `\w:N word. bit i w` equality in
  (* Distribute only the observed conditional. A global COND_RAND rewrite
     also distributes the equality function and hides this rewrite shape. *)
  GENL [x;k;`i:num`]
    (CONV_RULE (LAND_CONV (REWR_CONV COND_RAND))
      (CONV_RULE(DEPTH_CONV BETA_CONV) bit_equality));;

let SAIL_HL_X86_SHIFT_CLAMP_REWRITES =
  List.concat_map (fun width ->
    map (fun theorem -> CONV_RULE
      (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
      (INST_TYPE [width,`:N`] theorem))
      [SAIL_HL_X86_SHL_CLAMP; SAIL_HL_X86_USHR_CLAMP;
       SAIL_HL_X86_ISHR_CLAMP;
       SAIL_HL_X86_SHIFT_CLAMP_BITS SAIL_HL_X86_SHL_CLAMP;
       SAIL_HL_X86_SHIFT_CLAMP_BITS SAIL_HL_X86_USHR_CLAMP;
       SAIL_HL_X86_SHIFT_CLAMP_BITS SAIL_HL_X86_ISHR_CLAMP])
    [`:16`;`:32`;`:64`;`:128`];;

(* Arithmetic shift complements negative inputs, zero-extends by 64 bits,
   shifts and restores the sign mask. The source's temporaries are 80 bits
   for 16-bit lanes and 96 bits for 32-bit lanes. Every natural count is
   included. Apply this before normalizing shifted subword windows. *)
let SAIL_HL_X86_ARITHMETIC_SHIFT width =
  let wide = width + 64 in
  let sign = width - 1 in
  let statement = parse_term (Printf.sprintf
    "!x:%d word. !k. \
     word_xor \
       (word_subword \
         (word_ushr \
           (word_zx (word_xor x \
             (word_sx (word_subword x (%d,1):1 word):%d word)):%d word) \
           k) (0,%d):%d word) \
       (word_sx (word_subword x (%d,1):1 word):%d word) = \
     word_ishr x k" width sign width wide width width sign width) in
  prove(statement,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_XOR; BIT_WORD_SUBWORD;
                BIT_WORD_SX; BIT_WORD_ZX; BIT_WORD_USHR; BIT_WORD_ISHR] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `MIN i 0 = 0`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC (parse_term(Printf.sprintf "i + k < %d" width)) THEN
    ASM_SIMP_TAC[ARITH_RULE(parse_term(Printf.sprintf
      "i + k < %d ==> i + k < %d" width wide))] THEN CONV_TAC TAUT);;

let SAIL_HL_X86_ARITHMETIC_SHIFT16 = SAIL_HL_X86_ARITHMETIC_SHIFT 16;;
let SAIL_HL_X86_ARITHMETIC_SHIFT32 = SAIL_HL_X86_ARITHMETIC_SHIFT 32;;

let SAIL_HL_X86_ISHR_LOW16 = prove
 (`!x:32 word.
   word_subword (word_ishr x 1) (0,16):16 word =
   word_subword x (1,16)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_ISHR] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; ADD_SYM] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 16 ==> i + 1 < 32`]);;

let SAIL_HL_X86_ISHR_LOW17 = prove
 (`!x:32 word.
   word_subword (word_ishr x 14) (0,17):17 word =
   word_subword (word_ushr x 14) (0,17)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD;
              BIT_WORD_ISHR; BIT_WORD_USHR] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 17 ==> i + 14 < 32`]);;

let SAIL_HL_X86_ADD_LOW17 = prove
 (`!x y:32 word.
   word_subword (word_add x y) (0,17):17 word =
   word_add (word_subword x (0,17)) (word_subword y (0,17))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_SUBWORD_ADD THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_1] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Rounding needs only the low seventeen bits of the shifted sum. Compare
   those bits before retaining bits1..16, so lane multiplication remains
   opaque and no 32-bit adder or multiplier bit-blast is needed. *)
let SAIL_HL_X86_ROUNDED_LOW16 = prove
 (`!x:32 word.
   word_subword
     (word_ishr (word_add (word_ishr x 14) (word 1:32 word)) 1)
     (0,16):16 word =
   word_subword
     (word_add (word_ushr x 14) (word 1:32 word)) (1,16)`,
  GEN_TAC THEN REWRITE_TAC[SAIL_HL_X86_ISHR_LOW16] THEN
  SUBGOAL_THEN
   `word_subword
      (word_add (word_ishr (x:32 word) 14) (word 1:32 word)) (0,17):17 word =
    word_subword
      (word_add (word_ushr (x:32 word) 14) (word 1:32 word)) (0,17)`
   MP_TAC THENL
    [REWRITE_TAC[SAIL_HL_X86_ADD_LOW17; SAIL_HL_X86_ISHR_LOW17];
     DISCH_THEN(MP_TAC o AP_TERM
       `\y:17 word. word_subword y (1,16):16 word`) THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[]]);;

(* Sail's nonzero test folds a zero-extended 512-bit word into bit zero.
   Scalar multiply and VPTEST share this wiring proof. The input stays
   opaque: neither products nor vector operand bits are expanded here. *)
let SAIL_HL_X86_OR_REDUCTION_512 =
  let x = `x:512 word` in
  let expression = List.fold_left (fun term shift ->
    let shifted = mk_comb(mk_comb(`word_ushr:512 word->num->512 word`,term),
                          mk_small_numeral shift) in
    mk_comb(mk_comb(`word_or:512 word->512 word->512 word`,term),shifted))
    x [1;2;4;8;16;32;64;128;256] in
  let bit_zero = mk_comb(mk_comb(`bit:num->512 word->bool`,`0`),expression) in
  let statement = mk_forall(x,mk_eq(bit_zero,mk_neg(mk_eq(x,`word 0:512 word`)))) in
  prove(statement,
    GEN_TAC THEN REWRITE_TAC
      [BIT_WORD_OR; BIT_WORD_USHR; WORD_EQ_BITS_ALT; BIT_WORD_0] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(RAND_CONV(RAND_CONV EXPAND_CASES_CONV)) THEN
    REWRITE_TAC[DE_MORGAN_THM; DISJ_ASSOC] THEN
    (REFL_TAC ORELSE REWRITE_TAC[DISJ_ACI]));;

(* Signed saturation.
   The extra sign bit detects overflow when narrowing 17 bits to 16.
   These lemmas compare masks and sign extension with the target's branch
   calculation; the word being saturated remains opaque. *)
let SAIL_HL_X86_SINGLE_BIT_SUBWORD = prove
 (`!x:N word. !i.
   word_subword x (i,1):1 word = word(bitval(bit i x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_BITVAL] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES]);;

let SAIL_HL_X86_SIGNED_SATURATION17_MASK = prove
 (`!w:17 word.
   word_or
     (word_and
       (word_xor (word_sx(word_subword w (16,1):1 word):16 word)
                 (word 32767:16 word))
       (word_sx
         (word_xor (word_subword w (16,1):1 word)
                   (word_subword w (15,1):1 word)):16 word))
     (word_and
       (word_subword w (0,16):16 word)
       (word_not
         (word_sx
           (word_xor (word_subword w (16,1):1 word)
                     (word_subword w (15,1):1 word)):16 word))) =
   if bit 16 w = bit 15 w then word_subword w (0,16)
   else if bit 16 w then word 32768 else word 32767`,
  GEN_TAC THEN REWRITE_TAC[SAIL_HL_X86_SINGLE_BIT_SUBWORD] THEN
  ASM_CASES_TAC `bit 16 (w:17 word)` THEN
  ASM_CASES_TAC `bit 15 (w:17 word)` THEN ASM_REWRITE_TAC[bitval] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_WORD_AND;
              BIT_WORD_SUBWORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let SAIL_HL_X86_SIGNED_SATURATION17_SX32 = prove
 (`!w:17 word.
   (if bit 16 w = bit 15 w then word_subword w (0,16):16 word
    else if bit 16 w then word 32768 else word 32767) =
   (if bit 31 (word_sx w:32 word) = bit 15 (word_sx w:32 word)
    then word_subword (word_sx w:32 word) (0,16):16 word
    else if bit 31 (word_sx w:32 word) then word 32768 else word 32767)`,
  GEN_TAC THEN REWRITE_TAC[BIT_WORD_SX] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `word_subword (word_sx (w:17 word):32 word) (0,16):16 word =
    word_subword w (0,16)` SUBST1_TAC THENL
    [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_SX] THEN
     CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
     CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
     REPEAT STRIP_TAC THEN ASM_SIMP_TAC
       [ARITH_RULE `i < 16 ==> i < 17 /\ i < 32 /\ MIN i 16 = i`];
     REFL_TAC]);;

(* Byte products.
   The first operand is unsigned and the second signed. Two such products
   fit in signed 17 bits, so extension to 32 bits retains their
   mathematical sum. *)
let SAIL_HL_X86_BYTE_PRODUCT_RANGE = prove
 (`!a:8 word. !b:8 word.
   -- &32640 <= &(val a) * ival b /\
   &(val a) * ival b <= &32385`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(&(val(a:8 word)):int) <= &255` ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LE] THEN MP_TAC(ISPEC `a:8 word` VAL_BOUND) THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `-- &128 <= ival(b:8 word) /\ ival b <= &127`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `b:8 word` IVAL_BOUND) THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&(val(a:8 word)) * -- &128 <= &(val a) * ival(b:8 word)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_LMUL THEN ASM_REWRITE_TAC[INT_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&(val(a:8 word)) * ival(b:8 word) <= &(val a) * &127`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_LMUL THEN ASM_REWRITE_TAC[INT_POS]; ALL_TAC] THEN
  ASM_INT_ARITH_TAC);;

let SAIL_HL_X86_BYTE_PAIR_RANGE = prove
 (`!a:8 word. !b:8 word. !c:8 word. !d:8 word.
   -- &65280 <= &(val a) * ival b + &(val c) * ival d /\
   &(val a) * ival b + &(val c) * ival d <= &64770`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`a:8 word`; `b:8 word`] SAIL_HL_X86_BYTE_PRODUCT_RANGE) THEN
  MP_TAC(SPECL [`c:8 word`; `d:8 word`] SAIL_HL_X86_BYTE_PRODUCT_RANGE) THEN
  INT_ARITH_TAC);;

let SAIL_HL_X86_BYTE_PAIR_SX32 =
  let signed17 = CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV THENC INT_REDUCE_CONV)
    (INST_TYPE [`:17`,`:N`] IVAL_IWORD) in
  prove
 (`!a:8 word. !b:8 word. !c:8 word. !d:8 word.
   word_sx
     (iword(&(val a) * ival b + &(val c) * ival d):17 word):32 word =
   iword(&(val a) * ival b + &(val c) * ival d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_sx] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC signed17 THEN
  MP_TAC(SPECL [`a:8 word`; `b:8 word`; `c:8 word`; `d:8 word`]
    SAIL_HL_X86_BYTE_PAIR_RANGE) THEN INT_ARITH_TAC);;

let SAIL_HL_X86_BYTE_PAIR_VALUE32 = prove
 (`!a:8 word. !b:8 word. !c:8 word. !d:8 word.
   word_add
     (word_mul (word_zx a:32 word) (word_sx b:32 word))
     (word_mul (word_zx c:32 word) (word_sx d:32 word)) =
   iword(&(val a) * ival b + &(val c) * ival d)`,
  REWRITE_TAC[word_zx; WORD_IWORD; word_sx;
              GSYM IWORD_INT_MUL; GSYM IWORD_INT_ADD]);;

(* Match the source's branchless saturation before generic rewrites turn
   its 17-bit integer sum into word multiplication. No product bits are
   expanded. Normalize the statement's let bindings as well as its proof
   so the theorem can rewrite an already unfolded instruction body. *)
let SAIL_HL_X86_BYTE_PAIR_SATURATED = CONV_RULE
  SAIL_HL_X86_STRICT_LET_CONV (prove
 (`!a:8 word. !b:8 word. !c:8 word. !d:8 word.
   let w:17 word = iword(&(val a) * ival b + &(val c) * ival d) in
   word_or
     (word_and
       (word_xor
         (word_sx(word(bitval(bit 16 w)):1 word):16 word)
         (word 32767:16 word))
       (word_sx
         (word_xor (word(bitval(bit 16 w)):1 word)
                   (word(bitval(bit 15 w)):1 word)):16 word))
     (word_and
       (word_subword w (0,16):16 word)
       (word_not
         (word_sx
           (word_xor (word(bitval(bit 16 w)):1 word)
                     (word(bitval(bit 15 w)):1 word)):16 word))) =
   let tot:32 word =
     word_add
       (word_mul (word_zx a:32 word) (word_sx b:32 word))
       (word_mul (word_zx c:32 word) (word_sx d:32 word)) in
   if bit 31 tot = bit 15 tot then word_subword tot (0,16):16 word
   else if bit 31 tot then word 32768 else word 32767`,
  CONV_TAC SAIL_HL_X86_STRICT_LET_CONV THEN
  REWRITE_TAC
   [REWRITE_RULE[SAIL_HL_X86_SINGLE_BIT_SUBWORD]
      SAIL_HL_X86_SIGNED_SATURATION17_MASK;
    SAIL_HL_X86_SIGNED_SATURATION17_SX32;
    SAIL_HL_X86_BYTE_PAIR_SX32; SAIL_HL_X86_BYTE_PAIR_VALUE32]));;

(* Unsigned saturation.
   Blend masks first reduce to conditional choices. A signed 16-bit input is
   then clamped to 0..255 and narrowed to a byte, matching the target MIN. *)
let SAIL_HL_X86_BLEND_MASK = prove
 (`!a b:N word. !p.
   word_or
     (word_and a (word_not (word_sx (word(bitval p):1 word):N word)))
     (word_and b (word_sx (word(bitval p):1 word):N word)) =
   if p then b else a`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SAIL_HL_X86_SIGN_MASK; WORD_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE);;

let SAIL_HL_X86_UNSIGNED_SATURATION8 = prove
 (`!x:16 word.
   word_subword
     (if word_igt
           (if word_igt (word 0:16 word) x then word 0 else x)
           (word 255:16 word)
      then word 255
      else if word_igt (word 0:16 word) x then word 0 else x)
     (0,8):8 word =
   word(MIN (if bit 15 x then 0 else val x) 255)`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_IGT; INT_GT; IVAL_WORD_0] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[GSYM MSB_IVAL] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `bit 15 (x:16 word)` THEN
  ASM_REWRITE_TAC[IVAL_VAL; bitval; VAL_WORD_0; BIT_WORD_0] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[bitval; INT_MUL_RZERO; INT_SUB_RZERO] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[INT_SUB_RZERO; INT_OF_NUM_LT; MIN;
              ARITH_RULE `n <= 255 <=> ~(255 < n)`] THEN
  ((CONV_TAC WORD_REDUCE_CONV THEN REFL_TAC) ORELSE
   (COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM DIMINDEX_8; WORD_SUBWORD_DIMINDEX;
                WORD_USHR_ZERO; word_zx] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN REFL_TAC)));;

let SAIL_HL_X86_UNSIGNED_PACK_LANE = CONV_RULE
  SAIL_HL_X86_STRICT_LET_CONV (prove
 (`!x:16 word.
   let negative = bit 16
     (word_sub (word_sx x:17 word) (word_sx(word 0:16 word):17 word)) in
   let positive:16 word = word_or
     (word_and x
       (word_not(word_sx(word(bitval negative):1 word):16 word)))
     (word_and (word 0)
       (word_sx(word(bitval negative):1 word):16 word)) in
   let too_large = bit 16
     (word_sub (word_sx(word 255:16 word):17 word)
               (word_sx positive:17 word)) in
   word_subword
     (word_or
       (word_and positive
         (word_not(word_sx(word(bitval too_large):1 word):16 word)))
       (word_and (word 255)
         (word_sx(word(bitval too_large):1 word):16 word)))
     (0,8):8 word =
   word(MIN (if bit 15 x then 0 else val x) 255)`,
  CONV_TAC SAIL_HL_X86_STRICT_LET_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_SIGNED_GREATER16; SAIL_HL_X86_BLEND_MASK;
              SAIL_HL_X86_UNSIGNED_SATURATION8]));;

(* Byte assembly.
   The target packs a weighted natural sum; the source inserts each byte.
   Convert the sum to balanced joins once, keeping every byte opaque.
   The statement generator chooses only widths and byte positions. *)
let SAIL_HL_X86_JOIN_VALUES =
  map (fun bits ->
    let half = mk_finty(Num.num_of_int bits)
    and whole = mk_finty(Num.num_of_int (2 * bits)) in
    REWRITE_RULE [] (CONV_RULE
      (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
      (INST_TYPE [half,`:M`; half,`:N`; whole,`:P`] VAL_WORD_JOIN_SIMPLE)))
    [8;16;32;64;128];;

let SAIL_HL_X86_BYTE_ASSEMBLY count =
  let rec joined first count =
    if count = 1 then Printf.sprintf "b%d" first else
    let half = count / 2 in
    Printf.sprintf "(word_join %s %s:%d word)"
      (joined (first + half) half) (joined first half) (8 * count) in
  let quantifiers = String.concat "" (List.init count (fun index ->
    Printf.sprintf "!b%d:8 word. " index)) in
  let sum = String.concat " + " (List.init count (fun index ->
    Printf.sprintf "val b%d * 2 EXP %d" index (8 * index))) in
  let statement = parse_term (Printf.sprintf
    "%s(word(%s):%d word) = %s" quantifiers sum (8 * count)
    (joined 0 count)) in
  prove(statement,
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [word_join] THEN
    REWRITE_TAC SAIL_HL_X86_JOIN_VALUES THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN AP_TERM_TAC THEN ARITH_TAC);;

let SAIL_HL_X86_BYTES16 = SAIL_HL_X86_BYTE_ASSEMBLY 16;;
let SAIL_HL_X86_BYTES32 = SAIL_HL_X86_BYTE_ASSEMBLY 32;;
