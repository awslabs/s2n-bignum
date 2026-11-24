(* Lane facts and tactics for the AVX2 and legacy SSE suites: byte
   shuffles, blends, element inserts and the views of general registers
   that their instructions share. They are kernel-proved identities and
   proof tactics; the claims are in x86-avx2.ml and x86-sse.ml. *)
needs "x86/proofs/base.ml";;
needs "tools/sail/proofs/x86-vector-lemmas.ml";;

(* branchless.sail reduces a zero-extended word by OR-ing shifted copies.
   Prove the 16-bit case once before expanding vector lane placement. The
   final one-bit complement sign-extends to the equality mask. These are
   word identities, not replacement instruction semantics. *)
let SAIL_HL_X86_OR_FOLD512 value =
  List.fold_left (fun value shift ->
    mk_comb(mk_comb(`word_or:512 word->512 word->512 word`,value),
      mk_comb(mk_comb(`word_ushr:512 word->num->512 word`,value),
              mk_numeral(num shift))))
    value [1;2;4;8;16;32;64;128;256];;

let SAIL_HL_X86_OR_REDUCE16 = prove
 (mk_forall(`x:16 word`,
   mk_iff(mk_comb(mk_comb(`bit:num->512 word->bool`,`0`),
     SAIL_HL_X86_OR_FOLD512 `word_zx (x:16 word):512 word`),
     mk_neg(mk_eq(`x:16 word`,`word 0:16 word`)))),
  GEN_TAC THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_USHR; BIT_WORD_ZX;
              WORD_EQ_BITS_ALT; BIT_WORD_0] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[BIT_TRIVIAL; DIMINDEX_16; ARITH] THEN CONV_TAC TAUT);;

let SAIL_HL_X86_EQUAL16 = prove
 (list_mk_forall([`x:16 word`;`y:16 word`],
   mk_eq(vsubst
    [SAIL_HL_X86_OR_FOLD512 `word_zx (word_xor (x:16 word) y):512 word`,
     `v:512 word`]
    `word_sx
      (word_not
        (word(bitval(bit 0 (word(bitval(bit 0 (v:512 word))):1 word)))
         :1 word)):16 word`,
    `if x:16 word = y then word 65535:16 word else word 0`)),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BIT_WORD_BITVAL; ARITH; SAIL_HL_X86_OR_REDUCE16;
              WORD_XOR_EQ_0] THEN
  BOOL_CASES_TAC `x:16 word = y` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV);;

let SAIL_HL_X86_AVX2_MASK_BIT = prove
 (`!k b. k < 8 ==>
    (bit k (word_sx (word_not (word (bitval b):1 word)):8 word) <=> ~b)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[BIT_WORD_SX; BIT_WORD_NOT; BIT_WORD_BITVAL; DIMINDEX_8;
                  DIMINDEX_1] THEN
  REWRITE_TAC[ARITH_RULE `MIN k 0 = 0`; DIMINDEX_1; ARITH] THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

let SAIL_HL_X86_AVX2_COND_FALSE = prove
 (`!b x. (if b then F else x) <=> x /\ ~b`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

let SAIL_HL_X86_AVX2_LANE_BOUND = prove
 (`!(w:4 word) k. k < 8 ==> 8 * val w + k < 128`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `w:4 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_4] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;
let SAIL_HL_X86_AVX2_MOD32_MOD8 = prove(`!a. a MOD 4294967296 MOD 8 = a MOD 8`,
  GEN_TAC THEN
  SUBGOAL_THEN `4294967296 = 8 * 536870912` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; REWRITE_TAC[MOD_MOD]]);;
let SAIL_HL_X86_AVX2_PERM_INDEX = prove
 (`!(w:256 word) pos.
    num_of_int(&(val(word_subword w (pos,32):32 word)) rem &8 * &32) =
    32 * val(word_subword w (pos,3):3 word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_32; DIMINDEX_3; INT_OF_NUM_REM;
              INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[SAIL_HL_X86_AVX2_MOD32_MOD8] THEN ARITH_TAC);;
let SAIL_HL_X86_AVX2_COND_BOOL = prove(`!c. (if c then T else F) <=> c`, GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[]);;
let SAIL_HL_X86_AVX2_COND_BLEND = prove
 (`!c x y. (if c then y else x) <=> x /\ ~c \/ y /\ c`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[]);;
let SAIL_HL_X86_AVX2_BLEND_ONE = prove
 (`!(imm:N word) j. (!i. i < 1 ==>
      (bit i (word 1:1 word) <=> i < 1 /\ bit (j + i) imm)) <=> bit j imm`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[BIT_LSB_WORD; ODD; ARITH; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `1 = 1`; ODD];
    DISCH_TAC THEN REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BIT_LSB_WORD; ODD; ARITH; ADD_CLAUSES]]);;

(* The immediate selects a lane by its low bit or low three bits. *)
let SAIL_HL_X86_AVX2_SELECT_BIT = prove
 (`!imm:8 word. val imm MOD 2 = bitval(bit 0 imm)`,
  GEN_TAC THEN REWRITE_TAC[BIT_LSB; bitval] THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[ODD_MOD] THEN ARITH_TAC);;

let SAIL_HL_X86_AVX2_BIT_IS_ZERO = prove
 (`!b. (word (bitval b):1 word = word 0) <=> ~b`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV);;

(* Two branches that write the same component become one write. *)
let SAIL_HL_X86_AVX2_IF_WRITE = prove
 (`!c d x y (s:A) (t:A).
    (if c then (write d x s = t) else (write d y s = t)) <=>
    (write d (if c then x else y) s = t)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let SAIL_HL_X86_AVX2_IF_WRITE_VALUE = prove
 (`!c d x y (s:A).
    (if c then write d x s else write d y s) = write d (if c then x else y) s`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let SAIL_HL_X86_AVX2_IF_WRITE_SYM = prove
 (`!c d x y (s:A) (t:A).
    (if c then (t = write d x s) else (t = write d y s)) <=>
    (t = write d (if c then x else y) s)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let SAIL_HL_X86_AVX2_BIT_IS_ZERO_SYM = prove
 (`!b. (word 0:1 word = word (bitval b)) <=> ~b`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV);;

let SAIL_HL_X86_AVX2_VAL_SUBWORD3 = prove
 (`!imm:8 word. val (word_subword imm (0,3):3 word) = val imm MOD 8`,
  REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_1; EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL]);;

let SAIL_HL_X86_AVX2_BIT8 = prove
 (`!k. k < 8 ==> bit k (word 255:8 word)`,
  GEN_TAC THEN DISCH_TAC THEN UNDISCH_TAC `k < 8` THEN
  SPEC_TAC(`k:num`,`k:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[BIT_WORD] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ARITH]);;

let SAIL_HL_X86_AVX2_BIT16 = prove
 (`!k. k < 16 ==> bit k (word 65535:16 word)`,
  GEN_TAC THEN DISCH_TAC THEN UNDISCH_TAC `k < 16` THEN
  SPEC_TAC(`k:num`,`k:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[BIT_WORD] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ARITH]);;

let SAIL_HL_X86_AVX2_BIT32 = prove
 (`!k. k < 32 ==> bit k (word 4294967295:32 word)`,
  GEN_TAC THEN DISCH_TAC THEN UNDISCH_TAC `k < 32` THEN
  SPEC_TAC(`k:num`,`k:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[BIT_WORD] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ARITH]);;

(* Blends: the immediate bit selects the source; the mask word has every
   bit set. *)
let SAIL_HL_X86_AVX2_BLEND_TAC =
  SIMP_TAC[SAIL_HL_X86_AVX2_BLEND_ONE; SAIL_HL_X86_AVX2_BIT8;
           SAIL_HL_X86_AVX2_BIT16; SAIL_HL_X86_AVX2_BIT32; ARITH;
           SAIL_HL_X86_AVX2_COND_BLEND] THEN
  REWRITE_TAC[];;

let SAIL_HL_X86_AVX2_PSHUFB_TAC =
  SIMP_TAC[SAIL_HL_X86_AVX2_MASK_BIT; ARITH; SAIL_HL_X86_AVX2_COND_FALSE;
           SAIL_HL_X86_AVX2_LANE_BOUND];;

(* Duplicated lanes: a bit of word_duplicate is a source bit modulo the
   lane width. *)
let SAIL_HL_X86_AVX2_DUPLICATE_TAC =
  REWRITE_TAC[BIT_WORD_DUPLICATE; BIT_WORD_SUBWORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[];;

(* An inserted lane's bounds: the 32-bit register view adds a redundant
   range test to the 16-bit one. *)
let SAIL_HL_X86_AVX2_LANE_RANGE = prove
 (`(!a P. (a < 16 /\ a < 32 /\ P) <=> (a < 16 /\ P)) /\
   (!a P. (a < 32 /\ a < 32 /\ P) <=> (a < 32 /\ P))`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let SAIL_HL_X86_AVX2_INSERT_TAC =
  REWRITE_TAC[ADD_CLAUSES; SAIL_HL_X86_AVX2_LANE_RANGE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[SAIL_HL_X86_AVX2_LANE_RANGE];;

(* VPINSRD builds its lane with a shifted mask. Fix the lane number, then
   every shift amount is a numeral. *)
let SAIL_HL_X86_AVX2_VAL_SUBWORD2 = prove
 (`!imm:8 word. val (word_subword imm (0,2):2 word) = val imm MOD 4`,
  REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_1; EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL]);;

let SAIL_HL_X86_AVX2_PINSRD_TAC =
  REWRITE_TAC[SAIL_HL_X86_AVX2_VAL_SUBWORD2] THEN
  MP_TAC(ARITH_RULE `val(imm:8 word) MOD 4 < 4`) THEN
  SPEC_TAC(`val(imm:8 word) MOD 4`,`v:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[BIT_WORD_SHL; BIT_WORD_ZX; BIT_WORD_SUBWORD; BIT_WORD;
              DIMINDEX_128; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ARITH] THEN
  REWRITE_TAC[SAIL_HL_X86_AVX2_LANE_RANGE];;

(* A 32-bit general register view is the zero-extended low half. *)
let SAIL_HL_X86_AVX2_ZEROTOP_TAC =
  REWRITE_TAC[COMPONENT_COMPOSE_ASSOC; READ_ZEROTOP_32; BIT_WORD_ZX] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[];;

(* 128-bit lane inserts and extracts: split on the selecting bit. *)
let SAIL_HL_X86_AVX2_LANE_TAC =
  BOOL_CASES_TAC `bit 0 (imm:8 word)` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

(* VPERMD selects a dword by the low three bits of each index: Sail
   reduces the index modulo 8 as an integer. *)
let SAIL_HL_X86_AVX2_PERMD_TAC =
  REWRITE_TAC[SAIL_HL_X86_AVX2_PERM_INDEX];;


(* Two branches that write the same component, and a lane chosen by one
   bit of the immediate (VINSERTI128, VEXTRACTI128, VPINSRQ, PINSRQ). *)
let SAIL_HL_X86_AVX2_LANE_REWRITES =
  [SAIL_HL_X86_AVX2_IF_WRITE; SAIL_HL_X86_AVX2_IF_WRITE_SYM;
   SAIL_HL_X86_AVX2_IF_WRITE_VALUE;
   SAIL_HL_X86_AVX2_SELECT_BIT; SAIL_HL_X86_AVX2_BIT_IS_ZERO;
   SAIL_HL_X86_AVX2_BIT_IS_ZERO_SYM];;

(* ---- Register-to-general mask extracts: VMOVMSKPS, VPMOVMSKB, PMOVMSKB ---- *)
(* Sum of eight weighted bits: bit j of the byte is the j-th Boolean. *)
let SAIL_HL_X86_AVX2_BYTE_SUM_BITS =
  let names = map (fun i -> "b" ^ string_of_int i) (0--7) in
  (* The model's sum is left associated: ((b0 + 2 * b1) + 4 * b2) + ... *)
  let sum = List.fold_left (fun acc i ->
    Printf.sprintf "(%s + %d * bitval b%d)" acc (1 lsl i) i) "bitval b0" (1--7) in
  map (fun j ->
    prove(parse_term (Printf.sprintf "!%s. bit %d (word (%s):8 word) <=> b%d"
        (String.concat " " names) j sum j),
      REPEAT GEN_TAC THEN
      MAP_EVERY BOOL_CASES_TAC (map (fun n -> mk_var(n,`:bool`)) names) THEN
      REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[BIT_WORD] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ARITH])) (0--7);;
let SAIL_HL_X86_AVX2_BIT0_BITVAL = prove
 (`!b. bit 0 (word (bitval b):1 word) <=> b`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV);;

(* VPMOVMSKB: bit k of the 32-bit sum of 2 EXP i * bitval (f i) is f k. *)
let SAIL_HL_X86_AVX2_NSUM_BIT = prove
 (`!(f:num->bool) k. k < 32 ==>
     (bit k (word (nsum (0..31) (\i. 2 EXP i * bitval (f i))):32 word) <=> f k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `\i. bitval ((f:num->bool) i)`; `0..31`; `k:num`]
    DIGITSUM_DIV_MOD) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; BITVAL_BOUND_ALT] THEN
  ASM_REWRITE_TAC[LE_0; ARITH_RULE `k <= 31 <=> k < 32`] THEN
  ASM_REWRITE_TAC[BIT_WORD; DIMINDEX_32; ODD_MOD] THEN
  ASM_SIMP_TAC[BIT_WORD] THEN
  DISCH_TAC THEN
  REWRITE_TAC[ODD_MOD; GSYM (REWRITE_RULE[] (SPEC `2` MOD_MOD_REFL))] THEN
  ASM_REWRITE_TAC[] THEN BOOL_CASES_TAC `(f:num->bool) k` THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC);;

(* ---- VPERM2I128 ---- *)
(* A property of every byte follows from its 256 values. *)
let SAIL_HL_X86_AVX2_BYTE_CASES = prove
 (`!P:8 word->bool. (!n. n < 256 ==> P(word n)) ==> !imm. P imm`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `val(imm:8 word)`) THEN
  REWRITE_TAC[WORD_VAL] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPEC `imm:8 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* VPERM2I128: the immediate holds two nibbles, each a lane number in its
   low two bits and a zeroing flag in its top bit. s2n-bignum reads a
   nibble as an integer; Sail takes a two-bit field and a bit. Every
   value of the immediate is checked. *)
let SAIL_HL_X86_AVX2_PERM2_NIBBLE_FACTS = prove
 (`!imm:8 word.
    ((val (word_subword imm (4,4):4 word) DIV 8) MOD 2 = 1 <=> bit 7 imm) /\
    ((val (word_subword imm (0,4):4 word) DIV 8) MOD 2 = 1 <=> bit 3 imm) /\
    val (word_subword imm (4,4):4 word) MOD 4 =
    val (word_subword imm (4,2):2 word) /\
    val (word_subword imm (0,4):4 word) MOD 4 =
    val (word_subword imm (0,2):2 word)`,
  MATCH_MP_TAC SAIL_HL_X86_AVX2_BYTE_CASES THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV)) THEN
  REWRITE_TAC[BIT_WORD] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* The zeroing mask of vperm2_select: the sign extension of the inverted
   flag, in every bit position of the lane. *)
let SAIL_HL_X86_AVX2_FLAG_MASK_BIT = prove
 (`!k b. k < dimindex(:N) ==>
    (bit k (word_sx (word_not (word (bitval b):1 word)):N word) <=> ~b)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[BIT_WORD_SX; BIT_WORD_NOT; BIT_WORD_BITVAL; DIMINDEX_1] THEN
  REWRITE_TAC[ARITH_RULE `MIN k 0 = 0`; DIMINDEX_1; ARITH] THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

(* Sail zeroes a lane with a mask; s2n-bignum tests the flag. *)
let SAIL_HL_X86_AVX2_FLAG_MASK = prove
 (`!(a:128 word) z. word_and a (word_sx (word_not (word (bitval z):1 word))) =
                    if z then word 0 else a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_AND] THEN
  MP_TAC(SPECL [`k:num`; `z:bool`]
    (INST_TYPE [`:128`,`:N`] SAIL_HL_X86_AVX2_FLAG_MASK_BIT)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  BOOL_CASES_TAC `z:bool` THEN REWRITE_TAC[BIT_WORD_0]);;

(* Both lane numbers and both flags are split, then every output bit is a
   propositional identity. *)
let SAIL_HL_X86_AVX2_FOUR_CASES = prove
 (`!w:2 word. val w = 0 \/ val w = 1 \/ val w = 2 \/ val w = 3`,
  GEN_TAC THEN MP_TAC(ISPEC `w:2 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_2] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let SAIL_HL_X86_AVX2_PERM2_BIT_TAC =
  STRIP_ASSUME_TAC(SPEC `word_subword (imm:8 word) (4,2):2 word`
    SAIL_HL_X86_AVX2_FOUR_CASES) THEN
  STRIP_ASSUME_TAC(SPEC `word_subword (imm:8 word) (0,2):2 word`
    SAIL_HL_X86_AVX2_FOUR_CASES) THEN
  ASM_CASES_TAC `bit 7 (imm:8 word)` THEN
  ASM_CASES_TAC `bit 3 (imm:8 word)` THEN
  ASM_REWRITE_TAC[ARITH];;

(* ---- VPBLENDVB ---- *)
(* A word assembled from bytes as nsum of 2 EXP (i * 8) * val (f i), as in
   VPBLENDVB: bit k is bit k MOD 8 of byte k DIV 8. The sum is a base-256
   digit sum whose digits are the byte values. [n] is the byte count. *)
let SAIL_HL_X86_AVX2_BYTE_NSUM_BIT n =
  let rec replace pattern value text =
    let lp = String.length pattern and lt = String.length text in
    let rec find i =
      if i + lp > lt then None
      else if String.sub text i lp = pattern then Some i else find (i + 1) in
    match find 0 with
    | None -> text
    | Some i -> String.sub text 0 i ^ value ^
        replace pattern value (String.sub text (i + lp) (lt - i - lp)) in
  let subst text =
    replace "@BITS" (string_of_int (8 * n))
      (replace "@COUNT" (string_of_int n)
        (replace "@LAST" (string_of_int (n - 1)) text)) in
  let q text = parse_term (subst text) in
  let th_digit = prove(q "!f:num->8 word.
     nsum (0..@LAST) (\\i. 2 EXP (i * 8) * val (f i)) =
     nsum {i | i < @COUNT} (\\i. 256 EXP i * val (f i))",
    GEN_TAC THEN REWRITE_TAC[NUMSEG_LT] THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    REWRITE_TAC[ARITH_EQ] THEN
    MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `x * 8 = 8 * x` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV) in
  let th_bound = prove(q "!f:num->8 word.
     nsum {i | i < @COUNT} (\\i. 256 EXP i * val (f i)) < 2 EXP @BITS",
    GEN_TAC THEN
    MP_TAC(SPECL [`256`; `\i. val((f:num->8 word) i)`; q "@COUNT"]
      DIGITSUM_BOUND) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN MP_TAC(ISPEC `(f:num->8 word) i` VAL_BOUND) THEN
      REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV;
      CONV_TAC NUM_REDUCE_CONV]) in
  let th_digitj = prove(q "!f:num->8 word j. j < @COUNT ==>
     (nsum {i | i < @COUNT} (\\i. 256 EXP i * val (f i))) DIV (256 EXP j) MOD 256
     = val (f j)",
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`256`; `\i. val((f:num->8 word) i)`;
                  q "{i | i < @COUNT}"; `j:num`] DIGITSUM_DIV_MOD) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN MP_TAC(ISPEC `(f:num->8 word) i` VAL_BOUND) THEN
      REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[]]) in
  let th_bound' = CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) th_bound in
  let th_byte = prove(q "!f:num->8 word j. j < @COUNT ==>
     word_subword (word (nsum {i | i < @COUNT} (\\i. 256 EXP i * val (f i))):@BITS word)
       (8 * j,8) = (f j:8 word)",
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
    REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8;
                DIMINDEX_128; DIMINDEX_256] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[MOD_LT; th_bound'] THEN
    SUBGOAL_THEN `2 EXP (8 * j) = 256 EXP j` SUBST1_TAC THENL
     [REWRITE_TAC[EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    MP_TAC(SPECL [`f:num->8 word`; `j:num`] th_digitj) THEN
    ASM_REWRITE_TAC[]) in
  prove(q "!f:num->8 word k.
    bit k (word (nsum (0..@LAST) (\\i. 2 EXP (i * 8) * val (f i))):@BITS word) <=>
    k < @BITS /\\ bit (k MOD 8) (f (k DIV 8))",
    REPEAT GEN_TAC THEN REWRITE_TAC[th_digit] THEN
    ASM_CASES_TAC (q "k < @BITS") THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN (q "k DIV 8 < @COUNT") ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`f:num->8 word`; `k DIV 8`] th_byte) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[BIT_WORD_SUBWORD; DIMINDEX_8] THEN
      SUBGOAL_THEN `8 * (k DIV 8) + k MOD 8 = k` SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ARITH_RULE `k MOD 8 < 8`) THEN
      REWRITE_TAC[ARITH_RULE `MIN 8 8 = 8`] THEN SIMP_TAC[];
      SUBGOAL_THEN (q "@BITS <= k") ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[BIT_TRIVIAL; DIMINDEX_128; DIMINDEX_256]]);;

let SAIL_HL_X86_AVX2_BYTE_NSUM_BITS =
  [SAIL_HL_X86_AVX2_BYTE_NSUM_BIT 16; SAIL_HL_X86_AVX2_BYTE_NSUM_BIT 32];;

let SAIL_HL_X86_AVX2_BLENDV_TAC =
  REWRITE_TAC SAIL_HL_X86_AVX2_BYTE_NSUM_BITS THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_BIT_COND; BIT_WORD_SUBWORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[SAIL_HL_X86_AVX2_BIT8; SAIL_HL_X86_AVX2_COND_BOOL;
           SAIL_HL_X86_AVX2_COND_BLEND; ARITH] THEN
  REPEAT CONJ_TAC THEN CONV_TAC TAUT;;

(* ---- VPCLMULQDQ ---- *)
(* Sail's pclmulqdq folds 64 steps result ^ ((zero_extend(y) << i) &
   sign_extend(x[i])) over a zero accumulator. Each step contributes y
   shifted by i when bit i of x is set, which is what 64 applications of
   WORD_PMUL_STEP produce for word_pmul x y. *)
let SAIL_HL_X86_AVX2_PMUL_MASK = prove
 (`!(v:N word) c. word_and v (word_sx (word (bitval c):1 word)) =
                  if c then v else word 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[BIT_WORD_AND; BIT_WORD_SX; BIT_WORD_BITVAL; DIMINDEX_1] THEN
  REWRITE_TAC[ARITH_RULE `MIN k 0 = 0`; ARITH] THEN
  BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[BIT_WORD_0]);;

let SAIL_HL_X86_AVX2_PMUL_USHR64 = prove
 (`!x:64 word. word_ushr x 64 = word 0`,
  REWRITE_TAC[WORD_USHR_EQ_0] THEN
  GEN_TAC THEN MP_TAC(ISPEC `x:64 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_64]);;

let rec SAIL_HL_X86_AVX2_PMUL_UNROLL_CONV count =
  if count = 0 then
    REWRITE_CONV[SAIL_HL_X86_AVX2_PMUL_USHR64; WORD_PMUL_0]
  else GEN_REWRITE_CONV I [WORD_PMUL_STEP] THENC
    REWRITE_CONV[BIT_WORD_USHR; WORD_USHR_COMPOSE;
      WORD_SHL_COMPOSE; DIMINDEX_64] THENC
    NUM_REDUCE_CONV THENC
    RAND_CONV(SAIL_HL_X86_AVX2_PMUL_UNROLL_CONV(count - 1));;

(* The unrolled loop, in the form the translated body has after its
   shifts and extensions are normalized: a left-nested xor of the 64 masked
   shifts. *)

let SAIL_HL_X86_AVX2_PMUL_CHAINS =
  let step i = Printf.sprintf
    "word_and (word_shl (word_zx (b:64 word):128 word) %d) (word_sx (word (bitval (bit %d (a:64 word))):1 word))" i i in
  (* The first step may or may not keep its xor with the zero accumulator. *)
  let rec chain zero i =
    if i = 0 then
      (if zero then Printf.sprintf "word_xor (word 0) (%s)" (step 0) else step 0)
    else Printf.sprintf "word_xor (%s) (%s)" (chain zero (i - 1)) (step i) in
  map (fun zero ->
  prove(parse_term ("!a b. " ^ chain zero 63 ^ " = (word_pmul a b:128 word)"),
    REPEAT GEN_TAC THEN
    CONV_TAC(RAND_CONV
      (GEN_REWRITE_CONV I [GSYM(CONJUNCT2 WORD_PMUL_ZX)] THENC
       SAIL_HL_X86_AVX2_PMUL_UNROLL_CONV 64)) THEN
    REWRITE_TAC[SAIL_HL_X86_AVX2_PMUL_MASK; WORD_SHL_ZERO; WORD_XOR_0] THEN
    REWRITE_TAC[GSYM WORD_XOR_ASSOC; WORD_XOR_SYM;
      WORD_BITWISE_RULE `word_xor (x:N word) (word_xor y z) =
                         word_xor y (word_xor x z)`])) [false; true];;

(* The quadword choice of VPCLMULQDQ: Sail's blend with an all-ones or
   all-zeros mask is a conditional. *)
let SAIL_HL_X86_AVX2_QWORD_BLEND = prove
 (`!(x:64 word) y c.
    word_or (word_and x (word_not (if c then word 18446744073709551615 else word 0)))
            (word_and y (if c then word 18446744073709551615 else word 0)) =
    if c then y else x`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `word 18446744073709551615:64 word = word_not (word 0)`
    SUBST1_TAC THENL [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[] THEN
  CONV_TAC WORD_BITWISE_RULE);;
