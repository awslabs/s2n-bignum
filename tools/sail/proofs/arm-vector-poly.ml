(* The four widening PMULL/PMULL2 forms, at lane sizes 8 and 64.
   Non-widening byte PMUL is proved in arm-vector-polynomial-multiply.ml.
   The export uses the common enabled-AdvSIMD access interpretation and
   the checked FEAT_PMULL=true capability fact for the 64-bit forms.

   The intended comparison retains the original PolynomialMult XOR loop
   and uses HOL word_pmul, not ordinary integer multiplication. Register
   fields, data and overlaps remain universal in these statements. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;
(* Normalize a binding's value before substituting it into later source
   updates. Expanding all lets first duplicates the old accumulator into
   both arms of each XOR update. fresh-model.ml evaluates by value, and
   the model's unfolding here also applies SAIL_HL_ARM_WORD_XOR_STEP, which
   keeps each old value once. Without these two the suite runs many times
   longer. The definition command still declares the exact Sail body. *)
loadt "tools/sail/proofs/fresh-model.ml";;
let sail_hl_arm_poly_saved_rewrite_rule = REWRITE_RULE;;
module Sail_poly_model = struct
open Sail_hl_fresh_model;;
let REWRITE_RULE equations theorem =
  Sail_hl_fresh_model.REWRITE_RULE
    (SAIL_HL_ARM_WORD_XOR_STEP ::
     SAIL_HL_ARM_BIT_WORD_ONE :: WORD_XOR_0 ::
     WORD_SHL_ZERO :: equations) theorem;;
loadt "tools/sail/_build/arm-vector-poly.ml";;
end;;
include Sail_poly_model;;
let REWRITE_RULE = sail_hl_arm_poly_saved_rewrite_rule;;
needs "tools/sail/proofs/arm-vector-model-parameters.ml";;

(* Upstream PolynomialMult(8,8) starts from zero and visits bits0 through7.
   ITLIST applies its tail first, hence the descending concrete list. The
   proof compares all sixteen output bits with HOL's polynomial convolution,
   including high input-bit terms which must vanish because x and y are
   bytes. It assumes no input values and no favorable source condition. *)
let SAIL_HL_ARM_VECTOR_POLY_BYTE_LANE = prove
 (`!(x:8 word) (y:8 word).
   ITLIST (\i previous.
     if bit i x
     then word_xor previous (word_shl (word_zx y:16 word) i)
     else previous) [7;6;5;4;3;2;1;0] (word 0:16 word) =
   (word_pmul x y:16 word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ITLIST; SAIL_HL_ARM_WORD_XOR_STEP] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV
    (BIT_WORD_CONV ORELSEC
     GEN_REWRITE_CONV I [SAIL_HL_ARM_CONDITIONAL_BIT])) THEN
  REWRITE_TAC[BIT_WORD_PMUL] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ODD_ADD; ODD_MULT; SAIL_HL_ARM_ODD_BITVAL;
    BIT_WORD_SUBWORD; BIT_WORD_ZX;
    SAIL_HL_ARM_CONDITIONAL_BIT] THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC TAUT);;

let SAIL_HL_ARM_VECTOR_POLY_BYTE_UNROLLED =
  REWRITE_RULE[ITLIST; SAIL_HL_ARM_WORD_XOR_STEP;
    WORD_XOR_0; WORD_SHL_ZERO] SAIL_HL_ARM_VECTOR_POLY_BYTE_LANE;;

(* WORD_PMUL_STEP removes one source bit without splitting over its value.
   After 64 steps the shifted first operand is zero. This yields the same
   conditional shifts as Sail's loop. Associativity and commutativity align
   the loop's accumulator order with the library's recursive product order;
   no 128-by-64 bit convolution or case split is needed. *)
let SAIL_HL_ARM_VECTOR_POLY_USHR64 = prove
 (`!x:64 word. word_ushr x 64 = word 0`,
  REWRITE_TAC[WORD_USHR_EQ_0] THEN
  GEN_TAC THEN MP_TAC(ISPEC `x:64 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_64]);;

let rec SAIL_HL_ARM_VECTOR_POLY_UNROLL_CONV count =
  if count = 0 then
    REWRITE_CONV[SAIL_HL_ARM_VECTOR_POLY_USHR64; WORD_PMUL_0]
  else GEN_REWRITE_CONV I [WORD_PMUL_STEP] THENC
    REWRITE_CONV[BIT_WORD_USHR; WORD_USHR_COMPOSE;
      WORD_SHL_COMPOSE; DIMINDEX_64] THENC
    NUM_REDUCE_CONV THENC
    RAND_CONV(SAIL_HL_ARM_VECTOR_POLY_UNROLL_CONV(count - 1));;

let SAIL_HL_ARM_VECTOR_POLY_64_LANE = prove
 (parse_term
  ("!(x:64 word) (y:64 word). ITLIST (\\i previous. " ^
   "if bit i x then word_xor previous (word_shl (word_zx y:128 word) i) " ^
   "else previous) [" ^
   String.concat ";" (map string_of_int (rev(0--63))) ^
   "] (word 0:128 word) = (word_pmul x y:128 word)"),
  REPEAT GEN_TAC THEN
  CONV_TAC(RAND_CONV
    (GEN_REWRITE_CONV I [GSYM(CONJUNCT2 WORD_PMUL_ZX)] THENC
     SAIL_HL_ARM_VECTOR_POLY_UNROLL_CONV 64)) THEN
  REWRITE_TAC[ITLIST; SAIL_HL_ARM_WORD_XOR_STEP;
    WORD_SHL_ZERO; WORD_XOR_0; GSYM WORD_XOR_ASSOC; WORD_XOR_SYM;
    WORD_BITWISE_RULE
     `word_xor (x:N word) (word_xor y z) =
      word_xor y (word_xor x z)`]);;

let SAIL_HL_ARM_VECTOR_POLY_64_UNROLLED =
  REWRITE_RULE[ITLIST; SAIL_HL_ARM_WORD_XOR_STEP;
    WORD_XOR_0; WORD_SHL_ZERO] SAIL_HL_ARM_VECTOR_POLY_64_LANE;;

let SAIL_HL_ARM_VECTOR_POLY_VALUE_TAC element =
  W(fun (_,goal) ->
    let is_write term =
      let head,arguments = strip_comb term in
      is_const head && fst(dest_const head) = "write" &&
      length arguments = 3 in
    let _,source = strip_comb(find_term is_write(lhand goal)) in
    let _,target = strip_comb(find_term is_write(rand goal)) in
    SUBGOAL_THEN(mk_eq(el 1 source,el 1 target))
      (fun theorem -> SUBST1_TAC theorem THEN REWRITE_TAC[EQ_SYM_EQ]) THEN
    REWRITE_TAC[SAIL_HL_ARM_VECTOR_POLY_BYTE_UNROLLED;
      SAIL_HL_ARM_VECTOR_POLY_64_UNROLLED; WORD_PMUL_ZX] THEN
    (if element = 64 then
      REWRITE_TAC[WORD_ZX_SUBWORD] THEN
      CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
      CONV_TAC(REDEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
      CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
      CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
      CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]
    else
    REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
    (* Enter only the lane containing this concrete output-bit position;
       other inserted lanes do not need their eight XOR steps expanded. *)
    CONV_TAC(TOP_DEPTH_CONV
      (BIT_WORD_CONV ORELSEC
       GEN_REWRITE_CONV I [SAIL_HL_ARM_CONDITIONAL_BIT])) THEN
    REWRITE_TAC[SAIL_HL_ARM_XOR_STEP; BIT_WORD_PMUL] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ODD_ADD; ODD_MULT; SAIL_HL_ARM_ODD_BITVAL;
      BIT_WORD_SUBWORD; BIT_WORD_ZX;
      SAIL_HL_ARM_CONDITIONAL_BIT;
      SAIL_HL_ARM_XOR_STEP] THEN
    ONCE_REWRITE_TAC[BIT_GUARD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SAIL_HL_ARM_XOR_STEP] THEN
    CONV_TAC TAUT));;

let SAIL_HL_ARM_VECTOR_POLY_TAC element definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; SAIL_HL_ARM_CONDITIONAL_PAIR; COND_ID;
    SAIL_HL_ARM_WORD_XOR_STEP; arm_PMULL_VEC_ALT;
    arm_PMULL2_VEC_ALT; assign; LET_DEF; LET_END_DEF; FST; SND;
    NUM_OF_INT_OF_NUM; QREG'; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    SAIL_HL_ARM_BIT_WORD_ONE; WORD_PMUL_ZX] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(REDEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[SAIL_HL_ARM_BIT_WORD_ONE; WORD_PMUL_ZX; EQ_SYM_EQ] THEN
  SAIL_HL_ARM_VECTOR_POLY_VALUE_TAC element;;

let SAIL_HL_ARM_VECTOR_POLY_CLAIM operation width element definition =
  let configuration,source =
    SAIL_HL_ARM_VECTOR_MODEL_APPLICATION 3 definition in
  let statement = parse_term(
    configuration ^ "!d n m:5 word. !s t:armstate. " ^
    source ^ " d n m s t <=> arm_" ^
    operation ^ " (QREG' d) (QREG' n) (QREG' m) " ^
    string_of_int element ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_POLY_TAC element definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s%dE%d_EQ" operation width element in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_POLY_CLAIMS = map
  (fun (operation,width,element,definition) ->
    SAIL_HL_ARM_VECTOR_POLY_CLAIM operation width element definition) [
  "PMULL_VEC",128,8,sail_hl_arm_5fPMULL_5fVEC128E8;
  "PMULL_VEC",128,64,sail_hl_arm_5fPMULL_5fVEC128E64;
  "PMULL2_VEC",128,8,sail_hl_arm_5fPMULL2_5fVEC128E8;
  "PMULL2_VEC",128,64,sail_hl_arm_5fPMULL2_5fVEC128E64;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_POLY_PROOFS_OK";;
