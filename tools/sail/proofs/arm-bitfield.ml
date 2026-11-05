(* Agreement with the original decoded bitfield bodies and DecodeBitMasks.
   Mathematical facts normalize the generated calculations; they do not
   replace source helpers. Register 31, overlaps, wrapping immediate pairs
   and the zero-count LSL encoding retain their complete domains. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-bitfield.ml";;
needs "tools/sail/proofs/arm-shift-lemmas.ml";;

(* The original SBFM execute body repeats the selected source sign bit.
   This identity handles arbitrary destination widths without selecting a
   particular source/destination register or a value for the sign bit. *)
let SAIL_HL_BITFIELD_SIGN_REPLICATE = prove
 (`!sign.
     (word_duplicate (word(bitval sign):1 word):N word) =
     word_neg(word(bitval sign))`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_DUPLICATE; BIT_WORD_MASK;
    BIT_WORD_BITVAL; DIMINDEX_1; MOD_1]);;

(* For insertion, the destination bits survive unless both masks select
   the bit. The source execute body's two-mask update is retained verbatim
   on the left; this is a word identity, not a replacement instruction. *)
let SAIL_HL_BITFIELD_INSERT_SELECTION = prove
 (`!destination value wmask tmask:N word.
     word_or
       (word_and destination (word_not tmask))
       (word_and
         (word_or (word_and destination (word_not wmask))
                  (word_and value wmask)) tmask) =
     word_or (word_and destination (word_not(word_and wmask tmask)))
             (word_and value (word_and wmask tmask))`,
  CONV_TAC WORD_BITWISE_RULE);;

(* With len=log2(width), diff[len-1..0] keeps the low bits of a possibly
   negative integer difference. The remainder is nonnegative; natural
   subtraction alone would lose the wrapped case. *)
let SAIL_HL_BITFIELD_DIFF_REMAINDER = prove
 (`!width r s.
     0 < width /\ r < width /\ s < width
     ==> num_of_int ((&s - &r) rem &width) + 1 =
         if r <= s then s - r + 1 else width - r + s + 1`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r:num <= s` THENL
   [SUBGOAL_THEN `s-r < width` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_REM_LT; INT_POS; INT_OF_NUM_LT;
      NUM_OF_INT_OF_NUM];
    SUBGOAL_THEN
     `(&s - &r) rem &width = &(width - r + s)` SUBST1_TAC THENL
     [MATCH_MP_TAC INT_REM_UNIQ THEN EXISTS_TAC `-- &1:int` THEN
      SUBGOAL_THEN `(&s:int) < &r` ASSUME_TAC THENL
       [REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `r:num <= width` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(&r:int) <= &width` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[INT_OF_NUM_LE]; ALL_TAC] THEN
      ASM_SIMP_TAC[INT_ABS_NUM; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_SUB;
        LT_IMP_LE; INT_MUL_LNEG; INT_MUL_LID] THEN
      ASM_INT_ARITH_TAC;
      ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM]]] THEN
  REWRITE_TAC[ADD_ASSOC]);;

(* The conjunction of the rotated write mask and the low transfer mask
   selects exactly the insertion interval. Both wrapping and nonwrapping
   immediate pairs are covered, including r=0 and s=width-1. *)
let SAIL_HL_BITFIELD_EFFECTIVE_MASK = prove
 (`!r s.
     r < dimindex(:N) /\ s < dimindex(:N)
     ==> word_and
           (word_ror (word(2 EXP (s+1)-1):N word) r)
           (word(2 EXP
              (if r <= s then s-r+1 else dimindex(:N)-r+s+1)-1)) =
         if r <= s then word(2 EXP (s-r+1)-1)
         else word_shl (word(2 EXP (s+1)-1)) (dimindex(:N)-r)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r:num <= s` THEN
  ASM_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_AND; BIT_WORD_ROR; BIT_MASK_WORD;
    BIT_WORD_SHL] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* Once word operations have been expanded, split the remaining source
   bits as Boolean values. The arithmetic solver then sees only interval
   conditions; it need not reason about uninterpreted bit predicates. *)
let SAIL_HL_BITFIELD_BIT_CASES_TAC =
  REPEAT(W(fun (_,goal) ->
    let source_bit = find_term (fun term ->
      let head, arguments = strip_comb term in
      is_const head && fst(dest_const head) = "bit" &&
      length arguments = 2) goal in
    ASM_CASES_TAC source_bit THEN ASM_REWRITE_TAC[]));;

(* After rotating within the register width, the selected interval is
   exactly HOL's nonwrapping extract or its wrapping left-shifted extract. *)
let SAIL_HL_BITFIELD_UNSIGNED_VALUE = prove
 (`!x:N word. !r s.
     r < dimindex(:N) /\ s < dimindex(:N)
     ==> word_and (word_ror x r)
           (word_and
             (word_ror (word(2 EXP (s+1)-1):N word) r)
             (word(2 EXP
                (if r <= s then s-r+1 else dimindex(:N)-r+s+1)-1))) =
         if r <= s then word_subword x (r,s-r+1)
         else word_shl (word_subword x (0,s+1)) (dimindex(:N)-r)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SAIL_HL_BITFIELD_EFFECTIVE_MASK] THEN
  ASM_CASES_TAC `r:num <= s` THEN
  ASM_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_AND; BIT_WORD_ROR; BIT_MASK_WORD;
    BIT_WORD_SHL; BIT_WORD_SUBWORD; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `r <= s /\ s < n ==> MIN (s-r+1) n = s-r+1`;
    ARITH_RULE `s < n ==> MIN (s+1) n = s+1`;
    ARITH_RULE `r < n ==> (i+r)-n = i-(n-r)`] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[ADD_AC] THEN
  SAIL_HL_BITFIELD_BIT_CASES_TAC THEN ASM_ARITH_TAC);;

(* The insertion value retains every bit outside the selected interval.
   This identity is instantiated after the actual source's masks are
   normalized; no register-state assumption is needed. *)
let SAIL_HL_BITFIELD_INSERT_VALUE = prove
 (`!destination x:N word. !r s.
     r < dimindex(:N) /\ s < dimindex(:N)
     ==> word_or
           (word_and destination
             (word_not(word_and
               (word_ror (word(2 EXP (s+1)-1):N word) r)
               (word(2 EXP
                  (if r <= s then s-r+1 else dimindex(:N)-r+s+1)-1)))))
           (word_and (word_ror x r)
             (word_and
               (word_ror (word(2 EXP (s+1)-1):N word) r)
               (word(2 EXP
                  (if r <= s then s-r+1 else dimindex(:N)-r+s+1)-1)))) =
         if r <= s then
           word_insert destination (0,s-r+1) (word_ushr x r)
         else word_insert destination (dimindex(:N)-r,s+1) x`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SAIL_HL_BITFIELD_EFFECTIVE_MASK] THEN
  ASM_CASES_TAC `r:num <= s` THEN
  ASM_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_NOT;
    BIT_WORD_ROR; BIT_MASK_WORD; BIT_WORD_SHL; BIT_WORD_INSERT;
    BIT_WORD_USHR; ADD_CLAUSES; SUB_0; LE_0] THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `r < n ==> (i+r)-n = i-(n-r)`] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[ADD_AC] THEN
  SAIL_HL_BITFIELD_BIT_CASES_TAC THEN ASM_ARITH_TAC);;

(* Sign extension replaces only the bits above the selected sign position.
   It is expressed using the same all-zero/all-one sign mask as the source
   one-bit replication primitive. *)
let SAIL_HL_BITFIELD_SIGN_EXTEND_MASK = prove
 (`!x:N word. !position.
     position < dimindex(:N)
     ==> word_or
           (word_and (word_neg(word(bitval(bit position x))))
                     (word_not(word(2 EXP (position+1)-1))))
           (word_and x (word(2 EXP (position+1)-1))) =
         word_sxfrom position x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_NOT; BIT_MASK_WORD;
    BIT_WORD_MASK; BIT_WORD_SXFROM] THEN
  ASM_CASES_TAC `i:num <= position` THEN
  ASM_SIMP_TAC[
    ARITH_RULE `i <= p ==> MIN p i = i`;
    ARITH_RULE `~(i <= p) ==> MIN p i = p`] THEN
  SAIL_HL_BITFIELD_BIT_CASES_TAC THEN
  ASM_ARITH_TAC);;

(* The unsigned result has no bits above the transfer interval; its highest
   retained bit is precisely the original source bit s, even when r>s. *)
let SAIL_HL_BITFIELD_UNSIGNED_TRANSFER_MASK = prove
 (`!x:N word. !r s.
     r < dimindex(:N) /\ s < dimindex(:N)
     ==> word_and
           (if r <= s then (word_subword x (r,s-r+1):N word)
            else word_shl (word_subword x (0,s+1):N word) (dimindex(:N)-r))
           (word(2 EXP
              (if r <= s then s-r+1 else dimindex(:N)-r+s+1)-1)) =
         if r <= s then (word_subword x (r,s-r+1):N word)
         else word_shl (word_subword x (0,s+1):N word) (dimindex(:N)-r)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r:num <= s` THEN
  ASM_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_AND; BIT_MASK_WORD; BIT_WORD_SHL;
    BIT_WORD_SUBWORD; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[
    ARITH_RULE `r <= s /\ s < n ==> MIN (s-r+1) n = s-r+1`;
    ARITH_RULE `s < n ==> MIN (s+1) n = s+1`] THEN
  SAIL_HL_BITFIELD_BIT_CASES_TAC THEN
  ASM_ARITH_TAC);;

let SAIL_HL_BITFIELD_UNSIGNED_TOP_BIT = prove
 (`!x:N word. !r s.
     r < dimindex(:N) /\ s < dimindex(:N)
     ==> bit (if r <= s then s-r else dimindex(:N)-r+s)
           (if r <= s then (word_subword x (r,s-r+1):N word)
            else word_shl (word_subword x (0,s+1):N word) (dimindex(:N)-r)) =
         bit s x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r:num <= s` THEN
  ASM_REWRITE_TAC[BIT_WORD_SHL; BIT_WORD_SUBWORD; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[
    ARITH_RULE `r <= s /\ s < n ==> MIN (s-r+1) n = s-r+1`;
    ARITH_RULE `s < n ==> MIN (s+1) n = s+1`;
    ARITH_RULE `r <= s ==> r+(s-r) = s`;
    ARITH_RULE `r <= s /\ s < n ==> s-r < n`;
    ARITH_RULE `~(r <= s) /\ r < n ==> n-r+s < n`;
    ARITH_RULE `n-r <= n-r+s`;
    ARITH_RULE `(n-r+s)-(n-r) = s`;
    ARITH_RULE `s-r < s-r+1`;
    ARITH_RULE `s < s+1`] THEN
  REWRITE_TAC[ADD_CLAUSES]);;

(* The source sign fill and retained rotated bits equal HOL's two signed
   extraction forms. Register-width and immediate bounds are explicit;
   no favorable sign, immediate ordering or operand overlap is assumed. *)
let SAIL_HL_BITFIELD_SIGNED_VALUE = prove
 (`!x:N word. !r s.
     r < dimindex(:N) /\ s < dimindex(:N)
     ==> word_or
           (word_and (word_neg(word(bitval(bit s x))))
             (word_not(word(2 EXP
                (if r <= s then s-r+1 else dimindex(:N)-r+s+1)-1))))
           (word_and (word_ror x r)
             (word_and
               (word_ror (word(2 EXP (s+1)-1):N word) r)
               (word(2 EXP
                  (if r <= s then s-r+1 else dimindex(:N)-r+s+1)-1)))) =
         if r <= s then word_sxfrom (s-r) (word_subword x (r,s-r+1))
         else word_sxfrom (dimindex(:N)-(r-s))
                (word_shl (word_subword x (0,s+1)) (dimindex(:N)-r))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `r:num <= s` THEN
  MP_TAC(SPECL [`x:N word`; `r:num`; `s:num`]
    SAIL_HL_BITFIELD_UNSIGNED_VALUE) THEN
  MP_TAC(SPECL [`x:N word`; `r:num`; `s:num`]
    SAIL_HL_BITFIELD_UNSIGNED_TOP_BIT) THEN
  MP_TAC(SPECL [`x:N word`; `r:num`; `s:num`]
    SAIL_HL_BITFIELD_UNSIGNED_TRANSFER_MASK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_ASSOC]) THEN
  ASM_SIMP_TAC[SAIL_HL_BITFIELD_UNSIGNED_VALUE] THEN
  ASM_SIMP_TAC[
    ARITH_RULE `r <= s /\ s < n ==> s-r < n`;
    ARITH_RULE `~(r <= s) /\ r < n ==> n-(r-s) = n-r+s`;
    ARITH_RULE `~(r <= s) /\ r < n ==> n-r+s < n`;
    GSYM SAIL_HL_BITFIELD_SIGN_EXTEND_MASK; ADD_ASSOC]);;

(* The encoded LSL alias has an explicit zero-count branch: r=0,s=width-1
   gives a full-word extract. Positive counts use r=width-amount and a
   wrapping extract. Neither branch discards an encoded amount. *)
let SAIL_HL_BITFIELD_LSL_VALUE = prove
 (`!x:N word. !amount.
     amount < dimindex(:N)
     ==> (let r = if amount = 0 then 0 else dimindex(:N)-amount in
          let s = dimindex(:N)-1-amount in
          if r <= s then word_subword x (r,s-r+1)
          else word_shl (word_subword x (0,s+1)) (dimindex(:N)-r)) =
         word_shl x amount`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `amount = 0` THENL
   [ASM_SIMP_TAC[SUB_0; LE_0; WORD_SHL_ZERO; WORD_SUBWORD_TRIVIAL;
      DIMINDEX_NONZERO; ARITH_RULE `~(n=0) ==> n-1+1 = n`; LE_REFL];
    ASM_SIMP_TAC[
      ARITH_RULE `a < n /\ ~(a=0) ==> ~(n-a <= n-1-a)`;
      ARITH_RULE `a < n ==> n-1-a+1 = n-a`;
      ARITH_RULE `a < n ==> n-(n-a) = a`] THEN
    MATCH_MP_TAC WORD_SHL_SUBWORD THEN ASM_ARITH_TAC]);;

(* UInt of the sliced signed difference is its Euclidean remainder.
   This holds for every integer, including negative wrapping differences. *)
let SAIL_HL_BITFIELD_IWORD_VALUE = prove
 (`!x. val(iword x:N word) =
       num_of_int(x rem &2 pow dimindex(:N))`,
  GEN_TAC THEN REWRITE_TAC[iword; VAL_WORD; INT_OF_NUM_POW] THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL [`x:int`; `(&(2 EXP dimindex(:N)):int)`] INT_DIVISION) THEN
  REWRITE_TAC[INT_OF_NUM_EQ; EXP_EQ_0; ARITH_EQ; INT_ABS_NUM] THEN
  STRIP_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT]);;

let SAIL_HL_BITFIELD_PADDED_VALUE = prove
 (`!x:5 word. val(word_join (word 0:1 word) x:6 word) = val x`,
  GEN_TAC THEN
  MP_TAC(ISPEC `x:5 word` VAL_BOUND) THEN
  REWRITE_TAC[VAL_WORD_JOIN; VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
  CONV_TAC (DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 32 ==> x < 64`]);;

(* W encodings pad their five-bit fields to six bits. Their original mask
   is31, so the source's AND and UInt leave the field value unchanged. *)
let SAIL_HL_BITFIELD_PADDED_FIELD = prove
 (`!x:5 word.
     val(word_and (word_join (word 0:1 word) x:6 word) (word 31)) =
     val x`,
  GEN_TAC THEN
  MP_TAC(ISPEC `x:5 word` VAL_BOUND) THEN
  CONV_TAC (DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`word_join (word 0:1 word) (x:5 word):6 word`; `5`]
    VAL_WORD_AND_MASK_WORD) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[SAIL_HL_BITFIELD_PADDED_VALUE; MOD_LT]);;

let SAIL_HL_BITFIELD_FULL_FIELD_MASK = prove
 (`!x:N word. word_and x (word(2 EXP dimindex(:N)-1)) = x`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_AND_MASK_WORD] THEN
  SIMP_TAC[MOD_LT; VAL_BOUND]);;

let SAIL_HL_BITFIELD_FIELD6_MASK =
  CONV_RULE NUM_REDUCE_CONV
    (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
      (INST_TYPE[`:6`,`:N`] SAIL_HL_BITFIELD_FULL_FIELD_MASK));;

(* The generated ROR helper tests the original count against zero. For
   decoded counts below the register width this is its ordinary rotation. *)
let SAIL_HL_BITFIELD_ROTATE = prove
 (`!x:N word. !r.
     r < dimindex(:N)
     ==> (if r = 0 then x else
          word_or (word_ushr x r) (word_shl x (dimindex(:N)-r))) =
         word_ror x r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:N word`; `r:num`] SAIL_HL_ARM_SHIFT_ROTATE) THEN
  ASM_SIMP_TAC[MOD_LT; INT_OF_NUM_SUB; LT_IMP_LE; NUM_OF_INT_OF_NUM]);;

let SAIL_HL_BITFIELD_FIXED width theorem =
  CONV_RULE NUM_REDUCE_CONV
    (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
      (INST_TYPE[parse_type(string_of_int width),`:N`] theorem));;

let SAIL_HL_ARM_BITFIELD_TAC width definition target =
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun name ->
    let field = parse_term(name ^ ":" ^ (if width = 32 then "5" else "6") ^
      " word") in
    ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV
      (CONV_RULE (DEPTH_CONV DIMINDEX_CONV) (ISPEC field VAL_BOUND))))
    ["immr"; "imms"] THEN
  REWRITE_TAC[definition; target; assign; LET_DEF; LET_END_DEF;
    FST; SND; XREG'; WREG'; NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ;
    INT_OF_NUM_REM; INT_OF_NUM_ADD; SUB_0;
    SAIL_HL_BITFIELD_PADDED_VALUE; SAIL_HL_BITFIELD_PADDED_FIELD;
    SAIL_HL_BITFIELD_FIELD6_MASK; SAIL_HL_BITFIELD_IWORD_VALUE] THEN
  CONV_TAC (DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_POW] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_AND_0; WORD_OR_0; ARITH_RULE `0 = r <=> r = 0`] THEN
  ASM_SIMP_TAC[MOD_LT; INT_OF_NUM_SUB; LT_IMP_LE; NUM_OF_INT_OF_NUM;
    SAIL_HL_BITFIELD_SIGN_REPLICATE; SUB_0] THEN
  ASM_SIMP_TAC[SAIL_HL_BITFIELD_DIFF_REMAINDER; ARITH;
    SAIL_HL_BITFIELD_FIXED width SAIL_HL_BITFIELD_ROTATE] THEN
  REWRITE_TAC[SAIL_HL_BITFIELD_INSERT_SELECTION; GSYM WORD_AND_ASSOC; GE] THEN
  ASM_SIMP_TAC[
    SAIL_HL_BITFIELD_FIXED width SAIL_HL_BITFIELD_INSERT_VALUE;
    SAIL_HL_BITFIELD_FIXED width SAIL_HL_BITFIELD_UNSIGNED_VALUE;
    SAIL_HL_BITFIELD_FIXED width SAIL_HL_BITFIELD_SIGNED_VALUE] THEN
  REWRITE_TAC[EQ_SYM_EQ];;

let SAIL_HL_ARM_BFM32_EQ = prove
 (`!d n:5 word. !immr imms:5 word. !s t:armstate.
     sail_hl_arm_5fBFM32 d n immr imms s t <=>
     arm_BFM (WREG' d) (WREG' n) (val immr) (val imms) s t`,
  SAIL_HL_ARM_BITFIELD_TAC 32 sail_hl_arm_5fBFM32 arm_BFM);;

let SAIL_HL_ARM_SBFM32_EQ = prove
 (`!d n:5 word. !immr imms:5 word. !s t:armstate.
     sail_hl_arm_5fSBFM32 d n immr imms s t <=>
     arm_SBFM (WREG' d) (WREG' n) (val immr) (val imms) s t`,
  SAIL_HL_ARM_BITFIELD_TAC 32 sail_hl_arm_5fSBFM32 arm_SBFM);;

let SAIL_HL_ARM_UBFM32_EQ = prove
 (`!d n:5 word. !immr imms:5 word. !s t:armstate.
     sail_hl_arm_5fUBFM32 d n immr imms s t <=>
     arm_UBFM (WREG' d) (WREG' n) (val immr) (val imms) s t`,
  SAIL_HL_ARM_BITFIELD_TAC 32 sail_hl_arm_5fUBFM32 arm_UBFM);;

let SAIL_HL_ARM_BFM64_EQ = prove
 (`!d n:5 word. !immr imms:6 word. !s t:armstate.
     sail_hl_arm_5fBFM64 d n immr imms s t <=>
     arm_BFM (XREG' d) (XREG' n) (val immr) (val imms) s t`,
  SAIL_HL_ARM_BITFIELD_TAC 64 sail_hl_arm_5fBFM64 arm_BFM);;

let SAIL_HL_ARM_SBFM64_EQ = prove
 (`!d n:5 word. !immr imms:6 word. !s t:armstate.
     sail_hl_arm_5fSBFM64 d n immr imms s t <=>
     arm_SBFM (XREG' d) (XREG' n) (val immr) (val imms) s t`,
  SAIL_HL_ARM_BITFIELD_TAC 64 sail_hl_arm_5fSBFM64 arm_SBFM);;

let SAIL_HL_ARM_UBFM64_EQ = prove
 (`!d n:5 word. !immr imms:6 word. !s t:armstate.
     sail_hl_arm_5fUBFM64 d n immr imms s t <=>
     arm_UBFM (XREG' d) (XREG' n) (val immr) (val imms) s t`,
  SAIL_HL_ARM_BITFIELD_TAC 64 sail_hl_arm_5fUBFM64 arm_UBFM);;

(* These equalities reduce BOTH actual generated definitions. They establish
   that the exported alias enters the same original decoder with these
   encoded fields; they do not supply replacement instruction semantics. *)
let SAIL_HL_BITFIELD_SOURCE_ALIAS_TAC definitions =
  REWRITE_TAC(definitions @ [LET_DEF; LET_END_DEF; FST; SND]) THEN
  CONV_TAC WORD_REDUCE_CONV;;

let SAIL_HL_BITFIELD_SOURCE_ASR32 = prove
 (`!d n:5 word. !amount:5 word.
     sail_hl_arm_5fASR32 d n amount =
     sail_hl_arm_5fSBFM32 d n amount (word 31)`,
  SAIL_HL_BITFIELD_SOURCE_ALIAS_TAC
    [sail_hl_arm_5fASR32; sail_hl_arm_5fSBFM32]);;
let SAIL_HL_BITFIELD_SOURCE_LSR32 = prove
 (`!d n:5 word. !amount:5 word.
     sail_hl_arm_5fLSR32 d n amount =
     sail_hl_arm_5fUBFM32 d n amount (word 31)`,
  SAIL_HL_BITFIELD_SOURCE_ALIAS_TAC
    [sail_hl_arm_5fLSR32; sail_hl_arm_5fUBFM32]);;
let SAIL_HL_BITFIELD_SOURCE_LSL32 = prove
 (`!d n:5 word. !amount:5 word.
     sail_hl_arm_5fLSL32 d n amount =
     sail_hl_arm_5fUBFM32 d n (word_sub (word 0) amount)
       (word_sub (word 31) amount)`,
  SAIL_HL_BITFIELD_SOURCE_ALIAS_TAC
    [sail_hl_arm_5fLSL32; sail_hl_arm_5fUBFM32]);;
let SAIL_HL_BITFIELD_SOURCE_ASR64 = prove
 (`!d n:5 word. !amount:6 word.
     sail_hl_arm_5fASR64 d n amount =
     sail_hl_arm_5fSBFM64 d n amount (word 63)`,
  SAIL_HL_BITFIELD_SOURCE_ALIAS_TAC
    [sail_hl_arm_5fASR64; sail_hl_arm_5fSBFM64]);;
let SAIL_HL_BITFIELD_SOURCE_LSR64 = prove
 (`!d n:5 word. !amount:6 word.
     sail_hl_arm_5fLSR64 d n amount =
     sail_hl_arm_5fUBFM64 d n amount (word 63)`,
  SAIL_HL_BITFIELD_SOURCE_ALIAS_TAC
    [sail_hl_arm_5fLSR64; sail_hl_arm_5fUBFM64]);;
let SAIL_HL_BITFIELD_SOURCE_LSL64 = prove
 (`!d n:5 word. !amount:6 word.
     sail_hl_arm_5fLSL64 d n amount =
     sail_hl_arm_5fUBFM64 d n (word_sub (word 0) amount)
       (word_sub (word 63) amount)`,
  SAIL_HL_BITFIELD_SOURCE_ALIAS_TAC
    [sail_hl_arm_5fLSL64; sail_hl_arm_5fUBFM64]);;

let SAIL_HL_BITFIELD_AMOUNT_BOUND_TAC width =
  let amount = parse_term
    ("amount:" ^ (if width = 32 then "5" else "6") ^ " word") in
  ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV
    (CONV_RULE (DEPTH_CONV DIMINDEX_CONV) (ISPEC amount VAL_BOUND)));;

(* The ordinary HOL ASR/LSR alias facts apply to all decoded counts. *)
let SAIL_HL_BITFIELD_RIGHT_ALIAS_TAC width source_alias core_graph target_alias =
  REPEAT GEN_TAC THEN SAIL_HL_BITFIELD_AMOUNT_BOUND_TAC width THEN
  REWRITE_TAC[source_alias; core_graph] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  ASM_SIMP_TAC[SAIL_HL_BITFIELD_FIXED width target_alias];;

(* LSL0 has r=0 rather than width: the five-/six-bit subtraction wraps.
   The generic LSL_VALUE fact covers that full-word extract as well as all
   positive counts, so the state-writing behavior is preserved even at0. *)
let SAIL_HL_BITFIELD_LEFT_ALIAS_TAC width =
  REPEAT GEN_TAC THEN SAIL_HL_BITFIELD_AMOUNT_BOUND_TAC width THEN
  REWRITE_TAC[arm_UBFM; arm_LSL; LET_DEF; LET_END_DEF; VAL_WORD_SUB_CASES] THEN
  CONV_TAC (DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  ASM_SIMP_TAC[ARITH_RULE `a < 32 ==> a <= 31`;
    ARITH_RULE `a < 64 ==> a <= 63`;
    ARITH_RULE `a <= 0 <=> a = 0`; ADD_CLAUSES; SUB_0; GE;
    SAIL_HL_BITFIELD_FIXED width
      (REWRITE_RULE[LET_DEF; LET_END_DEF] SAIL_HL_BITFIELD_LSL_VALUE)];;

let SAIL_HL_BITFIELD_TARGET_LSL32 = prove
 (`!d n:5 word. !amount:5 word.
     arm_UBFM (WREG' d) (WREG' n)
       (val(word_sub (word 0) amount))
       (val(word_sub (word 31) amount)) =
     arm_LSL (WREG' d) (WREG' n) (val amount)`,
  SAIL_HL_BITFIELD_LEFT_ALIAS_TAC 32);;
let SAIL_HL_BITFIELD_TARGET_LSL64 = prove
 (`!d n:5 word. !amount:6 word.
     arm_UBFM (XREG' d) (XREG' n)
       (val(word_sub (word 0) amount))
       (val(word_sub (word 63) amount)) =
     arm_LSL (XREG' d) (XREG' n) (val amount)`,
  SAIL_HL_BITFIELD_LEFT_ALIAS_TAC 64);;

let SAIL_HL_ARM_ASR32_EQ = prove
 (`!d n:5 word. !amount:5 word. !s t:armstate.
     sail_hl_arm_5fASR32 d n amount s t <=>
     arm_ASR (WREG' d) (WREG' n) (val amount) s t`,
  SAIL_HL_BITFIELD_RIGHT_ALIAS_TAC 32 SAIL_HL_BITFIELD_SOURCE_ASR32
    SAIL_HL_ARM_SBFM32_EQ arm_ASR_ALIAS);;
let SAIL_HL_ARM_LSR32_EQ = prove
 (`!d n:5 word. !amount:5 word. !s t:armstate.
     sail_hl_arm_5fLSR32 d n amount s t <=>
     arm_LSR (WREG' d) (WREG' n) (val amount) s t`,
  SAIL_HL_BITFIELD_RIGHT_ALIAS_TAC 32 SAIL_HL_BITFIELD_SOURCE_LSR32
    SAIL_HL_ARM_UBFM32_EQ arm_LSR_ALIAS);;
let SAIL_HL_ARM_LSL32_EQ = prove
 (`!d n:5 word. !amount:5 word. !s t:armstate.
     sail_hl_arm_5fLSL32 d n amount s t <=>
     arm_LSL (WREG' d) (WREG' n) (val amount) s t`,
  REWRITE_TAC[SAIL_HL_BITFIELD_SOURCE_LSL32; SAIL_HL_ARM_UBFM32_EQ;
    SAIL_HL_BITFIELD_TARGET_LSL32]);;
let SAIL_HL_ARM_ASR64_EQ = prove
 (`!d n:5 word. !amount:6 word. !s t:armstate.
     sail_hl_arm_5fASR64 d n amount s t <=>
     arm_ASR (XREG' d) (XREG' n) (val amount) s t`,
  SAIL_HL_BITFIELD_RIGHT_ALIAS_TAC 64 SAIL_HL_BITFIELD_SOURCE_ASR64
    SAIL_HL_ARM_SBFM64_EQ arm_ASR_ALIAS);;
let SAIL_HL_ARM_LSR64_EQ = prove
 (`!d n:5 word. !amount:6 word. !s t:armstate.
     sail_hl_arm_5fLSR64 d n amount s t <=>
     arm_LSR (XREG' d) (XREG' n) (val amount) s t`,
  SAIL_HL_BITFIELD_RIGHT_ALIAS_TAC 64 SAIL_HL_BITFIELD_SOURCE_LSR64
    SAIL_HL_ARM_UBFM64_EQ arm_LSR_ALIAS);;
let SAIL_HL_ARM_LSL64_EQ = prove
 (`!d n:5 word. !amount:6 word. !s t:armstate.
     sail_hl_arm_5fLSL64 d n amount s t <=>
     arm_LSL (XREG' d) (XREG' n) (val amount) s t`,
  REWRITE_TAC[SAIL_HL_BITFIELD_SOURCE_LSL64; SAIL_HL_ARM_UBFM64_EQ;
    SAIL_HL_BITFIELD_TARGET_LSL64]);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_BFM32_EQ", SAIL_HL_ARM_BFM32_EQ;
  "SAIL_HL_ARM_SBFM32_EQ", SAIL_HL_ARM_SBFM32_EQ;
  "SAIL_HL_ARM_UBFM32_EQ", SAIL_HL_ARM_UBFM32_EQ;
  "SAIL_HL_ARM_BFM64_EQ", SAIL_HL_ARM_BFM64_EQ;
  "SAIL_HL_ARM_SBFM64_EQ", SAIL_HL_ARM_SBFM64_EQ;
  "SAIL_HL_ARM_UBFM64_EQ", SAIL_HL_ARM_UBFM64_EQ;
  "SAIL_HL_ARM_ASR32_EQ", SAIL_HL_ARM_ASR32_EQ;
  "SAIL_HL_ARM_LSR32_EQ", SAIL_HL_ARM_LSR32_EQ;
  "SAIL_HL_ARM_LSL32_EQ", SAIL_HL_ARM_LSL32_EQ;
  "SAIL_HL_ARM_ASR64_EQ", SAIL_HL_ARM_ASR64_EQ;
  "SAIL_HL_ARM_LSR64_EQ", SAIL_HL_ARM_LSR64_EQ;
  "SAIL_HL_ARM_LSL64_EQ", SAIL_HL_ARM_LSL64_EQ
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_BITFIELD_PROOFS_OK";;
