(* Shift and rotate support for the REMS x86 claims.

   The group-2 and double-shift bodies take an arbitrary count byte, mask
   it and compute with Sail's integer shift primitives. These facts
   normalize the masked count to a word k, turn the integer calculations
   into word shifts, split a claim on the cases v = 0, v = 1, the remaining
   counts below the operand width and, where reachable, the width itself
   and larger counts, and decide each count comparison in a case by trying
   the values below k's bound. Value equalities that remain are bit-blasted, at each count if
   necessary. Counterexample tactics evaluate a relation on literal
   operands. These are support facts, not instruction claims. *)
needs "tools/sail/proofs/x86-rems-lemmas.ml";;

(* Shifts and rotates. The group-2 and double-shift bodies zero-extend the
   count byte to 128 bits, mask it with 63 for 64-bit operands or 31
   otherwise, and pass its low six bits on: the low six or five bits of
   the count. The claims name that masked count k. *)
let SAIL_HL_X86_REMS_COUNT bits =
  let mask = mk_small_numeral (1 lsl bits - 1) and p = mk_finty(num bits) in
  prove(subst [mask,`m:num`] (inst [p,`:P`]
    `!c:8 word. word_zx (word_and (word m) (word_zx c:128 word)):6 word =
                word_zx (word_zx c:P word)`), BITBLAST_TAC);;

let SAIL_HL_X86_REMS_VAL_ZX = prove
 (`!x:N word. dimindex(:N) <= dimindex(:M) ==> val(word_zx x:M word) = val x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN] THEN
  MATCH_MP_TAC MOD_LT THEN TRANS_TAC LTE_TRANS `2 EXP dimindex(:N)` THEN
  REWRITE_TAC[VAL_BOUND; LE_EXP; ARITH_EQ] THEN ASM_REWRITE_TAC[]);;

(* Sail's ash on the unsigned value, read back as a word. *)
let SAIL_HL_X86_REMS_SHL_RESULT = prove
 (`!x:M word n. iword(&(val x) * &(2 EXP n)):N word = word_shl (word_zx x) n`,
  REWRITE_TAC[word_shl; VAL_WORD_ZX_GEN; INT_OF_NUM_MUL; GSYM WORD_IWORD] THEN
  REWRITE_TAC[WORD_EQ; CONG] THEN CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

let SAIL_HL_X86_REMS_SHR_RESULT = prove
 (`!x:M word n. iword(&(val x) div &(2 EXP n)):N word = word_zx (word_ushr x n)`,
  REWRITE_TAC[word_zx; VAL_WORD_USHR; INT_OF_NUM_DIV; GSYM WORD_IWORD]);;

let SAIL_HL_X86_REMS_IWORD_VAL = prove
 (`!x:M word. iword(&(val x)):N word = word_zx x`,
  REWRITE_TAC[word_zx; GSYM WORD_IWORD]);;

let SAIL_HL_X86_REMS_IWORD_COND = prove
 (`!b x y. iword(if b then x else y):N word = if b then iword x else iword y`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* The right-shift bodies negate the count into a signed word and test
   the sign of the result. *)
let SAIL_HL_X86_REMS_IVAL_NEG = prove
 (`!k:P word. dimindex(:P) < dimindex(:N)
     ==> ival(iword(--(&(val k))):N word) = --(&(val k))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
  SUBGOAL_THEN `val(k:P word) < 2 EXP (dimindex(:N) - 1)` MP_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP dimindex(:P)` THEN
    REWRITE_TAC[VAL_BOUND; LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW] THEN
    MP_TAC(ISPEC `val(k:P word)` INT_POS) THEN INT_ARITH_TAC]);;

let SAIL_HL_X86_REMS_COUNT_INT = prove
 (`(!n. --(&n):int = &0 <=> n = 0) /\ (!n. --(&n):int > &0 <=> F) /\
   (!x:int. --(--x) = x)`,
  REWRITE_TAC[INT_NEG_EQ_0; INT_OF_NUM_EQ; INT_NEG_NEG] THEN INT_ARITH_TAC);;

let SAIL_HL_X86_REMS_SHL_LEFT = prove
 (`!x:M word n. iword(&(2 EXP n) * &(val x)):N word = word_shl (word_zx x) n`,
  ONCE_REWRITE_TAC[INT_MUL_SYM] THEN REWRITE_TAC[SAIL_HL_X86_REMS_SHL_RESULT]);;

(* SAR: REMS sign-extends with binary_logext, the low bits plus the sign
   bit's weight, tests the sign with logbitp, and shifts the integer. *)
let SAIL_HL_X86_REMS_LOGEXT = prove
 (`!x:N word. dimindex(:M) + 1 = dimindex(:N)
     ==> &(val(word_zx x:M word)) +
         (if bit (dimindex(:N) - 1) x then -- &1 else &0) * &(2 EXP dimindex(:M)) =
         ival x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN] THEN
  MP_TAC(ISPEC `x:N word` IVAL_VAL) THEN MP_TAC(ISPEC `x:N word` MSB_VAL) THEN
  MP_TAC(ISPEC `x:N word` VAL_BOUND) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ADD_SUB; EXP_ADD; EXP_1; INT_POW_ADD; INT_POW_1; INT_OF_NUM_POW] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
  SPEC_TAC(`val(x:N word)`,`v:num`) THEN SPEC_TAC(`2 EXP dimindex(:M)`,`p:num`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
   [SUBGOAL_THEN `v MOD p = v - p` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN INT_ARITH_TAC];
    SUBGOAL_THEN `v MOD p = v` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; INT_ARITH_TAC]]);;

let SAIL_HL_X86_REMS_SIGN_TEST = prove
 (`!x:N word n. iword(&(val x) div &(2 EXP n)):1 word = word 1 <=> bit n x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SAIL_HL_X86_REMS_SHR_RESULT] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD;
              DIMINDEX_1; BIT_VAL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM ODD_MOD]);;

let SAIL_HL_X86_REMS_SAR_RESULT = prove
 (`!x:N word n. iword(ival x div &(2 EXP n)):N word = word_ishr x n`,
  REWRITE_TAC[word_ishr; INT_OF_NUM_POW]);;

let SAIL_HL_X86_REMS_COND_NESTED = prove
 (`(!b x y z:A. (if b then (if b then x else y) else z) = (if b then x else z)) /\
   (!b x y z:A. (if b then x else (if b then y else z)) = (if b then x else z))`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* REMS shifts a nonnegative operand logically and a negative one
   arithmetically. The two agree when the sign bit is clear, so the
   branches can be merged. *)
let SAIL_HL_X86_REMS_USHR_ISHR = prove
 (`!x:N word n. ~bit (dimindex(:N) - 1) x ==> word_ushr x n = word_ishr x n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ishr; word_ushr; IVAL_VAL] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; INT_MUL_RZERO; INT_SUB_RZERO; INT_OF_NUM_POW;
                  INT_OF_NUM_DIV; GSYM WORD_IWORD]);;

let SAIL_HL_X86_REMS_SIGN_MERGE_CONV =
  let lemmas = map (fun w -> CONV_RULE (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [mk_finty(num w),`:N`] SAIL_HL_X86_REMS_USHR_ISHR)) [8;16;32;64] in
  fun tm ->
    let c,(a,b) = dest_cond tm in
    if not(can (term_match [] `bit (i:num) (x:N word)`) c) || compare a b = 0 then
      failwith "SAIL_HL_X86_REMS_SIGN_MERGE_CONV" else
    prove(mk_eq(tm,a), ASM_CASES_TAC c THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC lemmas);;

(* RCL/RCR: REMS inserts CF above the operand. *)
let SAIL_HL_X86_REMS_CARRY_JOIN w =
  BITBLAST_RULE (parse_term (Printf.sprintf
    "!x:%d word c. word_insert (word_zx x:%d word) (%d,1) (word(bitval c):1 word) = \
     (word_join (word(bitval c):1 word) (x:%d word):%d word)"
    w (w+1) w w (w+1)));;

(* CBV evaluates 2 EXP n to a numeral; state the facts at each n used. *)
let sail_hl_x86_rems_numeral th n =
  let x,_ = dest_forall(concl th) in
  GEN x (CONV_RULE NUM_REDUCE_CONV (SPEC (mk_small_numeral n) (SPEC x th)));;

(* Facts for the normalized count k:bits word, an operand of width bits
   and the signed words REMS forms from the negated count. *)
let SAIL_HL_X86_REMS_SHIFT_FACTS bits =
  let p = mk_finty(num bits) in
  let signed = map (fun w ->
    sail_hl_x86_rems_at [p,`:P`; mk_finty(num w),`:N`] SAIL_HL_X86_REMS_IVAL_NEG)
    [9; 17; 33; 65] in
  (* The masked count is widened again before it is used. *)
  let widened = List.concat_map (fun n -> map (fun w ->
    sail_hl_x86_rems_at [mk_finty(num n),`:N`; mk_finty(num w),`:M`]
      SAIL_HL_X86_REMS_VAL_ZX) [6; 8; 16; 32; 64; 128]) [bits; 6] in
  let logext = map (fun w ->
    sail_hl_x86_rems_at [mk_finty(num (w-1)),`:M`; mk_finty(num w),`:N`]
      SAIL_HL_X86_REMS_LOGEXT) [8; 16; 32; 64] in
  [SAIL_HL_X86_REMS_COUNT bits] @ widened @ signed @ logext @
  map (sail_hl_x86_rems_numeral SAIL_HL_X86_REMS_SIGN_TEST) [7; 15; 31; 63] @
  map (sail_hl_x86_rems_numeral SAIL_HL_X86_REMS_SHL_RESULT) [8; 16; 32; 64] @
  map (sail_hl_x86_rems_numeral SAIL_HL_X86_REMS_SHL_LEFT) [8; 16; 32; 64] @
  map SAIL_HL_X86_REMS_CARRY_JOIN [8; 16; 32; 64] @
  [SAIL_HL_X86_REMS_COUNT_INT; NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ;
   INT_OF_NUM_LE; INT_OF_NUM_LT; WORD_ZX_TRIVIAL; WORD_ZX_ZX;
   SAIL_HL_X86_REMS_IWORD_COND; SAIL_HL_X86_REMS_SHL_RESULT;
   SAIL_HL_X86_REMS_SHL_LEFT; SAIL_HL_X86_REMS_SHR_RESULT;
   SAIL_HL_X86_REMS_SAR_RESULT; SAIL_HL_X86_REMS_IWORD_VAL; IWORD_IVAL;
   SAIL_HL_X86_REMS_SIGN_TEST; SAIL_HL_X86_REMS_COND_NESTED; COND_ID];;

(* Decide each comparison on the count from the case assumptions: try
   every value below the count's bound. *)
let SAIL_HL_X86_REMS_DECIDE_CONV asl =
  let hyps = map concl asl in
  if hyps = [] then ALL_CONV else
  let outer = itlist (union o frees) hyps [] in
  let bounds = mapfilter (fun th ->
    let x,b = dest_binop `(<):num->num->bool` (concl th) in
    if is_numeral b && not(is_numeral x) then (x,th) else failwith "bound") asl in
  let reduce = NUM_REDUCE_CONV THENC INT_REDUCE_CONV THENC SAIL_HL_X86_REWRITE_CONV[] in
  let comparison t =
    match t with
    | Comb(Comb(Const(op,_),l),_) ->
        mem op ["="; "<"; "<="; ">"; ">="; "int_lt"; "int_le"; "int_gt";
                "int_ge"] &&
        (type_of l = `:num` || type_of l = `:int`) &&
        frees t <> [] && subset (frees t) outer
    | _ -> false in
  let enumerate t =
    let x,bound = find (fun (x,_) -> free_in x t) bounds in
    let related = filter (fun th -> free_in x (concl th)) asl in
    let n = genvar `:num` in
    let goal = subst [n,x] (mk_imp(list_mk_conj(map concl related), t)) in
    let th = prove(mk_forall(n,
        mk_imp(mk_binop `(<):num->num->bool` n (rand(concl bound)), goal)),
      CONV_TAC(EXPAND_CASES_CONV THENC reduce)) in
    MP (MP (SPEC x th) bound) (end_itlist CONJ related) in
  let decide t =
    if not(comparison t) then failwith "not a count comparison" else
    try EQT_INTRO (enumerate t) with Failure _ ->
    EQF_INTRO (enumerate (mk_neg t)) in
  DEPTH_CONV decide THENC SAIL_HL_X86_REWRITE_CONV[];;

(* Prove a value equality that holds under the case assumptions on the
   count k by trying each value of k. *)
let SAIL_HL_X86_REMS_WORD_CASES = prove
 (`!P. (!k:N word. P k) <=> (!n. n < 2 EXP dimindex(:N) ==> P (word n:N word))`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `k:N word` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `val(k:N word)`) THEN
  REWRITE_TAC[WORD_VAL; VAL_BOUND]);;

(* REMS compares one-bit flag words. *)
let SAIL_HL_X86_REMS_BITVAL_WORD_EQ = prove
 (`!a b. (word(bitval a):1 word = word(bitval b)) <=> (a <=> b)`,
  REPEAT GEN_TAC THEN MAP_EVERY BOOL_CASES_TAC [`a:bool`; `b:bool`] THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV);;

(* Prove a literal value equality: equal heads such as word_evenparity
   reduce to their arguments; otherwise bit-blast. *)
let rec SAIL_HL_X86_REMS_VALUE_EQ_RULE tm =
  let l,r = dest_eq tm in
  if l = r then REFL l else
  match l,r with
  | Comb(Const(f,_) as c,a), Comb(Const(g,_),b)
      when f = g && mem f ["word_evenparity"] ->
      AP_TERM c (SAIL_HL_X86_REMS_VALUE_EQ_RULE (mk_eq(a,b)))
  | _ -> SAIL_HL_X86_REMS_WORD_EQ_GEN_RULE true tm;;

let SAIL_HL_X86_REMS_COUNT_EQ_RULE k asl tm =
  let reduce = DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV THENC
    INT_REDUCE_CONV THENC WORD_REDUCE_CONV THENC
    SAIL_HL_X86_REWRITE_CONV[VAL_EQ_0; BITVAL_EQ_0; WORD_SHL_ZERO; WORD_USHR_ZERO;
                 SAIL_HL_X86_REMS_BITVAL_WORD_EQ] in
  if not(free_in k tm) then
    prove(tm, CONV_TAC reduce THEN (REFL_TAC ORELSE
      W(fun (_,w) -> ACCEPT_TAC(SAIL_HL_X86_REMS_VALUE_EQ_RULE w)))) else
  let hyps = filter (free_in k) (map concl asl) in
  let v = genvar (type_of k) in
  let body = subst [v,k] (if hyps = [] then tm else mk_imp(list_mk_conj hyps, tm)) in
  if free_in k body then failwith "SAIL_HL_X86_REMS_COUNT_EQ_RULE" else
  let th = prove(mk_forall(v, body),
    REWRITE_TAC[SAIL_HL_X86_REMS_WORD_CASES] THEN CONV_TAC reduce THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[VAL_WORD; NUM_OF_INT_OF_NUM] THEN CONV_TAC reduce THEN
    REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN CONV_TAC reduce THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    (REFL_TAC ORELSE
     W(fun (_,w) -> ACCEPT_TAC(SAIL_HL_X86_REMS_VALUE_EQ_RULE w)))) in
  let th = SPEC k th in
  if hyps = [] then th else MP th (end_itlist CONJ
    (map (fun h -> find (fun a -> concl a = h) asl) hyps));;

(* Above the operand width, REMS's double shifts write an unknown integer
   as the result. Every word, and every narrower word, is such a value. *)
let SAIL_HL_X86_REMS_UNKNOWN_WORD = prove
 (`(!P. (?v:int. P (iword v:N word)) <=> (?w. P w)) /\
   (!P. (?v:int. if &0 <= v then P (iword v:N word) else F) <=> (?w. P w))`,
  CONJ_TAC THEN GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `w:N word`) THEN EXISTS_TAC `ival(w:N word)` THEN
    ASM_REWRITE_TAC[IWORD_IVAL];
    MESON_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `w:N word`) THEN EXISTS_TAC `&(val(w:N word)):int` THEN
    ASM_REWRITE_TAC[INT_POS; GSYM WORD_IWORD; WORD_VAL]]);;

let SAIL_HL_X86_REMS_UNKNOWN_NARROW = prove
 (`!P. dimindex(:M) <= dimindex(:N)
       ==> ((?w:N word. P (word_zx w:M word)) <=> (?y. P y))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MESON_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `y:M word`) THEN EXISTS_TAC `word_zx(y:M word):N word` THEN
    ASM_SIMP_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL]]);;

let SAIL_HL_X86_REMS_UNKNOWN_WORD_CONV tm =
  let v,body = dest_exists tm in
  if type_of v <> `:int` then failwith "SAIL_HL_X86_REMS_UNKNOWN_WORD_CONV" else
  let guarded,p = match body with
    | Comb(Comb(Comb(Const("COND",_),Comb(Comb(Const("int_le",_),z),v')),p),f)
        when v' = v && z = `&0:int` && f = `F` -> true,p
    | _ -> false,body in
  let occs = setify (find_terms (fun t -> is_comb t && rand t = v &&
    (try fst(dest_const(rator t)) = "iword" with Failure _ -> false)) p) in
  if length occs <> 1 then failwith "SAIL_HL_X86_REMS_UNKNOWN_WORD_CONV" else
  let x = hd occs in
  let w = variant (frees tm) (mk_var("w", type_of x)) in
  let p' = subst [w,x] p in
  if free_in v p' then failwith "SAIL_HL_X86_REMS_UNKNOWN_WORD_CONV" else
  let n = hd(snd(dest_type(type_of x))) in
  let lemma = INST_TYPE [n,`:N`]
    ((if guarded then CONJUNCT2 else CONJUNCT1) SAIL_HL_X86_REMS_UNKNOWN_WORD) in
  let th = CONV_RULE (DEPTH_CONV BETA_CONV) (ISPEC (mk_abs(w,p')) lemma) in
  TRANS (ALPHA tm (lhs(concl th))) th;;

let SAIL_HL_X86_REMS_UNKNOWN_NARROW_CONV tm =
  let w,p = dest_exists tm in
  let occs = setify (find_terms (fun t -> is_comb t && rand t = w &&
    (try fst(dest_const(rator t)) = "word_zx" with Failure _ -> false)) p) in
  if length occs <> 1 then failwith "SAIL_HL_X86_REMS_UNKNOWN_NARROW_CONV" else
  let x = hd occs in
  let y = variant (frees tm) (mk_var("y", type_of x)) in
  let p' = subst [y,x] p in
  if free_in w p' then failwith "SAIL_HL_X86_REMS_UNKNOWN_NARROW_CONV" else
  let m = hd(snd(dest_type(type_of x))) and n = hd(snd(dest_type(type_of w))) in
  let lemma = SPEC (mk_abs(y,p'))
    (INST_TYPE [m,`:M`; n,`:N`] SAIL_HL_X86_REMS_UNKNOWN_NARROW) in
  let bound = EQT_ELIM ((DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (lhand(concl lemma))) in
  let th = CONV_RULE (DEPTH_CONV BETA_CONV) (MP lemma bound) in
  TRANS (ALPHA tm (lhs(concl th))) th;;

(* Normalize an applied REMS shift root: the arithmetic normalization,
   then the count and Sail shift primitives of SAIL_HL_X86_REMS_SHIFT_FACTS
   as words. *)
let SAIL_HL_X86_REMS_SHIFT_NORMALIZE cs facts bits root =
  let _,_,narrowing = facts in
  let shift = SAIL_HL_X86_REMS_SHIFT_FACTS bits in
  CONV_RULE (RAND_CONV
    (SAIL_HL_X86_REWRITE_CONV shift THENC
     DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV THENC
     SAIL_HL_X86_REWRITE_CONV (shift @ narrowing) THENC
     (* An 8-bit result is the parity byte only once it is a word. *)
     SAIL_HL_X86_REWRITE_CONV[PF] THENC SAIL_HL_X86_REMS_PF_CONV cs THENC
     SAIL_HL_X86_REWRITE_CONV[GSYM CF; GSYM PF; GSYM AF; GSYM ZF; GSYM SF; GSYM OF] THENC
     TOP_DEPTH_CONV (SAIL_HL_X86_REMS_UNKNOWN_WORD_CONV ORELSEC
                     SAIL_HL_X86_REMS_UNKNOWN_NARROW_CONV) THENC
     SAIL_HL_X86_REMS_JOIN_CONV THENC
     TOP_DEPTH_CONV SAIL_HL_X86_REMS_SIGN_MERGE_CONV))
    (SAIL_HL_X86_REMS_NORMALIZE cs facts root);;

(* Compare a REMS shift with an s2n-bignum shift by count v, the low bits
   of the count byte. Split on v = 0, v = 1, 2 <= v < width and, where the
   masked count can reach it, width <= v. Each case decides the count
   tests in both relations and compares sign tests as top bits. *)
let SAIL_HL_X86_REMS_SHIFT_CLAIM_TAC normalized instruction narrowing legacy bits width =
  let p = mk_finty(num bits) and limit = 1 lsl bits in
  let k = inst [p,`:P`] `word_zx (count:8 word):P word` in
  let v = mk_comb(inst [p,`:N`] `val:N word->num`, k) in
  let count_value = prove(subst [mk_small_numeral limit,`m:num`]
      (inst [p,`:P`] `!c:8 word. val(word_zx c:P word) = val c MOD m`),
    REWRITE_TAC[VAL_WORD_ZX_GEN] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)) in
  let bound = CONV_RULE (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (ISPEC k VAL_BOUND) in
  let n = mk_small_numeral in
  (* Single shifts change at the width, double shifts after it. *)
  let classes =
    [mk_eq(v, n 0); mk_eq(v, n 1);
     mk_conj(mk_binop `(<=):num->num->bool` (n 2) v,
             mk_binop `(<):num->num->bool` v (n width))] @
    (if width < limit then [mk_eq(v, n width)] else []) @
    (if width + 1 < limit then [mk_binop `(<):num->num->bool` (n width) v] else []) in
  let cases = prove(list_mk_disj (map (fun c -> mk_conj(concl bound, c)) classes),
    MP_TAC bound THEN ARITH_TAC) in
  let split =
    REWRITE_TAC[GSYM count_value] THEN
    MAP_EVERY (fun v -> ASM_CASES_TAC (mk_comb(mk_comb(
      `(<=):num->num->bool`,`4`), mk_comb(`val:3 word->num`, v)))) legacy THEN
    REPEAT_TCL DISJ_CASES_THEN (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))
      cases in
  let decide asl =
    SAIL_HL_X86_REWRITE_CONV[GSYM MSB_IVAL; DIMINDEX_FINITE_SUM] THENC DEPTH_CONV DIMINDEX_CONV THENC
    NUM_REDUCE_CONV THENC SAIL_HL_X86_REMS_DECIDE_CONV asl THENC
    INT_REDUCE_CONV THENC
    SAIL_HL_X86_REWRITE_CONV[NUM_OF_INT_OF_NUM; WORD_SHL_ZERO; WORD_USHR_ZERO;
                 WORD_ISHR_ZERO; WORD_ROL_ZERO; WORD_ROR_ZERO;
                 BIT_WORD_JOIN; BIT_WORD_BITVAL; DIMINDEX_FINITE_SUM] THENC
    DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV THENC SAIL_HL_X86_REWRITE_CONV[COND_ID] THENC
    TOP_DEPTH_CONV SAIL_HL_X86_REMS_SIGN_MERGE_CONV THENC
    (* A case can leave a state choice on a flag test; merge its branches. *)
    SAIL_HL_X86_REMS_UNDEFINED_VALUES_CONV in
  SAIL_HL_X86_REMS_CASES_CLAIM_TAC normalized instruction narrowing
    (Some split) decide (SAIL_HL_X86_REMS_COUNT_EQ_RULE k);;

(* Counterexamples. A witness relates an initial and a final state, both
   explicit writes over an arbitrary state s. These conversions and tactics
   evaluate a relation on literal operands; they choose an undefined value
   only to exhibit one permitted final state. *)
let SAIL_HL_X86_REMS_STATE_NORM_CONV =
  REPEATC (CHANGED_CONV
   (DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
    GEN_REWRITE_CONV DEPTH_CONV [BITVAL_CLAUSES] THENC
    DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV THENC
    TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV THENC
    DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV THENC
    TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV THENC
    SAIL_HL_X86_REWRITE_CONV[SAIL_HL_X86_RIP_TWICE]));;

(* Unfold an s2n-bignum instruction applied to literal operands. *)
let SAIL_HL_X86_REMS_UNFOLD_TAC definitions =
  CONV_TAC(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  REWRITE_TAC definitions THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV THENC
           WORD_REDUCE_CONV) THEN
  REWRITE_TAC[assign; SEQ; UNDEFINED_VALUES; SAIL_HL_X86_REMS_UNDEFINED_SEQ;
              SEQ_ID; ASSIGNS_SEQ; ASSIGNS_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[GPR8; GPR16; GPR32_Z; GPR64; READ_SHORT; WRITE_SHORT;
              READ_ZEROTOP_32; WRITE_ZEROTOP_32] THEN
  REWRITE_TAC SAIL_HL_X86_GPR_SHORT_REWRITES THEN
  REWRITE_TAC SAIL_HL_X86_GPR_INSERT_REWRITES THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV THENC
           WORD_REDUCE_CONV) THEN
  REWRITE_TAC[UNWIND_THM1; UNWIND_THM2] THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV;;

(* Unfold the core observation of a REMS root with its normalized
   relation. *)
let SAIL_HL_X86_REMS_CORE_UNFOLD_TAC normalized =
  REWRITE_TAC[sail_hl_x86_core; normalized; LEFT_AND_EXISTS_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV SAIL_HL_X86_REMS_PUSH_EXISTS_CONV) THEN
  REWRITE_TAC[UNWIND_THM1; UNWIND_THM2] THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV;;

(* Prove ?ys. t = W(ys) for explicit write chains: take each chosen value
   from the corresponding write in t, or its value in t's base state. A
   value that is not itself written, such as an unknown shift result
   inside a register value, takes the first hint of its type. *)
let rec SAIL_HL_X86_REMS_CHOOSE_TAC hints (asl,w) =
  let vs,body = strip_exists w in
  if vs = [] then ALL_TAC (asl,w) else
  let l,r = dest_eq body in
  let chain,target = if free_in (hd vs) r then r,l else l,r in
  let rec writes t acc = match t with
    | Comb(Comb(Comb(Const("write",_),c),x),rest) -> writes rest ((c,x)::acc)
    | _ -> acc,t in
  let ws,_ = writes chain [] and tws,base = writes target [] in
  let value = try
      let c = fst(find (fun (_,x) -> x = hd vs) ws) in
      (try snd(find (fun (c',_) -> c' = c) tws)
       with Failure _ -> mk_icomb(mk_icomb(`read:(A,B)component->A->B`, c), base))
    with Failure _ -> find (fun h -> type_of h = type_of (hd vs)) hints in
  (EXISTS_TAC value THEN SAIL_HL_X86_REMS_CHOOSE_TAC hints) (asl,w);;

let SAIL_HL_X86_REMS_PERMITS_WITH_TAC hints =
  CONV_TAC SAIL_HL_X86_REMS_STATE_NORM_CONV THEN
  SAIL_HL_X86_REMS_CHOOSE_TAC hints THEN
  CONV_TAC SAIL_HL_X86_REMS_STATE_NORM_CONV THEN
  (REFL_TAC ORELSE (PRINT_GOAL_TAC THEN FAIL_TAC "witness state differs"));;

(* Refute ?ys. t = W(ys) by the value of component c in both states. *)
let SAIL_HL_X86_REMS_REJECTS_TAC c =
  REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM (mk_icomb(`read:(A,B)component->A->B`, c))) THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  CONV_TAC(GEN_REWRITE_CONV DEPTH_CONV [BITVAL_CLAUSES] THENC
           DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) THEN
  ((REWRITE_TAC[] THEN NO_TAC) ORELSE
   (PRINT_GOAL_TAC THEN FAIL_TAC "witness not rejected"));;

