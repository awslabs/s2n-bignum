(* TBL/TBL2/TBL3 at D64 and Q128. Multi-register tables use the exact
   consecutive encoded register layout, including wrapping through Q31.
   Byte indices and all register data remain symbolic, including out-of-range
   indices and every destination/table/index-register overlap. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
(* Evaluate fixed helper choices before observing individual table bits.
   The loader checks and declares the supplied fresh kernel bodies; its
   definition/rewrite commands are local to this generated-model module. *)
loadt "tools/sail/proofs/fresh-model.ml";;
module Sail_vector_table_model = struct
open Sail_hl_fresh_model;;
loadt "tools/sail/_build/arm-vector-table.ml";;
end;;
include Sail_vector_table_model;;
needs "tools/sail/proofs/arm-lemmas.ml";;
needs "tools/sail/proofs/proof-fork.ml";;
needs "tools/sail/proofs/arm-vector-model-parameters.ml";;
needs "tools/sail/proofs/arm-vector-duplicate-lemmas.ml";;

let SAIL_HL_ARM_VECTOR_TABLE_PACK1 = prove
 (`!(x:128 word).
   (word_insert (word 0:128 word) (0,128) x:128 word) = x`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_INSERT; BIT_WORD_0] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SAIL_HL_ARM_VECTOR_TABLE_PACK2 = prove
 (`!(x:128 word) (y:128 word).
   (word_insert
     (word_insert (word 0:256 word) (0,128) x:256 word)
     (128,128) y:256 word) =
   (word_join y x:256 word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_INSERT; BIT_WORD_JOIN;
    BIT_WORD_0] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SAIL_HL_ARM_VECTOR_TABLE_PACK3 = prove
 (`!(x:128 word) (y:128 word) (z:128 word).
   (word_insert
     (word_insert
       (word_insert (word 0:384 word) (0,128) x:384 word)
       (128,128) y:384 word)
     (256,128) z:384 word) =
   (word_join z (word_join y x:256 word):384 word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_INSERT; BIT_WORD_JOIN;
    BIT_WORD_0] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* Sail advances its integer register number twice, reducing modulo32
   after each step. HOL's third table component adds two to the five-bit
   encoded register. This includes both wrap cases, Q30 and Q31. *)
let SAIL_HL_ARM_VECTOR_TABLE_NEXT2 = prove
 (`!n:num. ((n + 1) MOD 32 + 1) MOD 32 = (n + 2) MOD 32`,
  GEN_TAC THEN
  MP_TAC(SPECL [`n + 1`; `1`; `32`] MOD_ADD_MOD) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* The upstream fmod_int body subtracts divisor times quotient. For the
   literal positive divisor32, its checked division primitive is HOL div.
   This identity keeps that source calculation and rewrites its result
   to the register-number remainder used by the five-bit HOL component. *)
let SAIL_HL_ARM_VECTOR_TABLE_REM32 = prove
 (`!n:int. n - &32 * (n div &32) = n rem &32`,
  GEN_TAC THEN REWRITE_TAC[INT_REM_DIV] THEN INT_ARITH_TAC);;

(* Extraction beyond a table's bit width is already zero in the HOL word
   library. This proves that the source's explicit bounds branch agrees
   with that definition; it is not an instruction replacement template. *)
let SAIL_HL_ARM_VECTOR_TABLE_OUTSIDE = prove
 (`!(table:N word) byte_index.
   dimindex(:N) <= 8 * byte_index
   ==> word_subword table (8 * byte_index,8):8 word = word 0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_0] THEN
  REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[BIT_TRIVIAL; ARITH_RULE
    `N <= 8 * byte_index ==> N <= 8 * byte_index + i`]);;

let SAIL_HL_ARM_VECTOR_TABLE_LOOKUPS = map
  (fun (width,bytes) ->
    prove(parse_term(
      "!(table:" ^ string_of_int width ^ " word) (byte_index:8 word). " ^
      "(if val byte_index < " ^ string_of_int bytes ^
      " then word_subword table (8 * val byte_index,8):8 word else word 0) = " ^
      "word_subword table (8 * val byte_index,8)"),
      REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SAIL_HL_ARM_VECTOR_TABLE_OUTSIDE THEN
      CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC))
  [128,16; 256,32; 384,48];;

(* Every bit of an in-range byte is inside the table, and every bit of an
   out-of-range byte is outside it. These arithmetic identities cover each
   bit position; the byte index itself remains an arbitrary natural. *)
let SAIL_HL_ARM_VECTOR_TABLE_BYTE_BOUNDS = List.concat(map
  (fun bytes -> map
    (fun i -> ARITH_RULE(parse_term(
      "!n:num. 8 * n + " ^ string_of_int i ^ " < " ^
      string_of_int (8 * bytes) ^ " <=> n < " ^ string_of_int bytes)))
    (0--7))
  [16;32;48]);;

(* Observe an already selected output bit before following a packing branch.
   BIT_WORD_CONV decides an insert's literal position/range immediately.
   If both source branches therefore expose the same old bit, COND_ID closes
   that branch before visiting the earlier accumulator. The byte-index
   branch that affects this bit remains, including its out-of-range case.
   Every conversion returns a theorem; no register/data condition is assumed. *)
let SAIL_HL_ARM_VECTOR_TABLE_BIT_OBSERVATION_CONV =
  let conditional =
    GEN_REWRITE_CONV I [SAIL_HL_ARM_CONDITIONAL_BIT] THENC
    RATOR_CONV(RAND_CONV(TRY_CONV BIT_WORD_CONV)) THENC
    RAND_CONV(TRY_CONV BIT_WORD_CONV) THENC
    TRY_CONV(GEN_REWRITE_CONV I [COND_ID]) in
  conditional ORELSEC BIT_WORD_CONV;;

(* Expand the finite-bit rule on small variables, not the large conditional
   table value. Applying it at the equality root gives exactly the same
   64/128 bit obligations without scanning that value during dimension
   reduction and every step of finite-case expansion. Observe each selected
   bit before doing any further whole-term arithmetic rewriting. *)
let SAIL_HL_ARM_VECTOR_TABLE_BITS = map (fun width ->
  let ty = Printf.sprintf "%d word" width in
  let theorem = ISPECL [parse_term("x:" ^ ty); parse_term("y:" ^ ty)]
    WORD_EQ_BITS_ALT in
  GEN_ALL(CONV_RULE
    (RAND_CONV
      (BINDER_CONV(LAND_CONV(RAND_CONV DIMINDEX_CONV)) THENC
       EXPAND_CASES_CONV))
    theorem)) [64;128];;

let SAIL_HL_ARM_VECTOR_TABLE_VALUE_TAC =
  W(fun (_, goal) ->
    let is_write term =
      let head, arguments = strip_comb term in
      is_const head && fst(dest_const head) = "write" &&
      length arguments = 3 in
    let _, source = strip_comb(find_term is_write (lhand goal)) in
    let _, target = strip_comb(find_term is_write (rand goal)) in
    (* Substitute the established value equality directly. Registering its
       large source expression as a rewrite pattern overflows HOL's rewrite
       net for the128-bit, sixteen-byte lookup; substitution has no such
       indexing step and retains exactly the same equality obligation. *)
    SUBGOAL_THEN (mk_eq(el 1 source,el 1 target))
      (fun theorem -> SUBST1_TAC theorem THEN REWRITE_TAC[EQ_SYM_EQ]) THEN
    GEN_REWRITE_TAC I SAIL_HL_ARM_VECTOR_TABLE_BITS THEN
    REPEAT CONJ_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV SAIL_HL_ARM_VECTOR_TABLE_BIT_OBSERVATION_CONV) THEN
    REWRITE_TAC[SAIL_HL_ARM_CONDITIONAL_BIT;
      BIT_WORD_INSERT; BIT_WORD_JOIN; BIT_WORD_SUBWORD; BIT_WORD_ZX;
      BIT_WORD_0] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[COND_ID; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM;
      ARITH_RULE `(n:num) * 8 = 8 * n`] THEN
    REWRITE_TAC SAIL_HL_ARM_VECTOR_TABLE_BYTE_BOUNDS THEN
    REWRITE_TAC[COND_ID] THEN REPEAT CONJ_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    TRY(MATCH_MP_TAC (REWRITE_RULE[] BIT_TRIVIAL) THEN
      CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC));;

let SAIL_HL_ARM_VECTOR_TABLE_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_TBL; arm_TBL2; arm_TBL3;
    assign; LET_DEF; LET_END_DEF; FST; SND;
    SAIL_HL_ARM_CONDITIONAL_PAIR;
    SAIL_HL_ARM_CONDITIONAL_INSERT;
    COND_ID;
    NUM_OF_INT_OF_NUM; QREG'; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64;
    SAIL_HL_ARM_VECTOR_TABLE_REM32; INT_OF_NUM_ADD;
    INT_OF_NUM_MUL; INT_OF_NUM_REM; INT_OF_NUM_LT;
    VAL_WORD_ADD; VAL_WORD; WORD_VAL; usimd16; usimd8; usimd4; usimd2;
    SAIL_HL_ARM_VECTOR_TABLE_PACK1;
    SAIL_HL_ARM_VECTOR_TABLE_PACK2; SAIL_HL_ARM_VECTOR_TABLE_PACK3] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(REDEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM; INT_OF_NUM_LT;
    ARITH_RULE `(n:num) * 8 = 8 * n`;
    SAIL_HL_ARM_VECTOR_TABLE_NEXT2] THEN
  REWRITE_TAC SAIL_HL_ARM_VECTOR_TABLE_LOOKUPS THEN
  REWRITE_TAC[SAIL_HL_ARM_VECTOR_TABLE_PACK1;
    SAIL_HL_ARM_VECTOR_TABLE_PACK2; SAIL_HL_ARM_VECTOR_TABLE_PACK3;
    EQ_SYM_EQ] THEN
  SAIL_HL_ARM_VECTOR_TABLE_VALUE_TAC THEN PRINT_GOAL_TAC;;

let SAIL_HL_ARM_VECTOR_TABLE_CLAIM regs width definition =
  let configuration,source =
    SAIL_HL_ARM_VECTOR_MODEL_APPLICATION 3 definition in
  let next delta = "(QREG' (word_add n (word " ^ string_of_int delta ^ ")))" in
  let target = if regs = 1 then
    "arm_TBL (QREG' d) [QREG' n] (QREG' m)"
    else "arm_TBL" ^ string_of_int regs ^ " (QREG' d) (QREG' n) " ^
      next 1 ^ (if regs = 3 then " " ^ next 2 else "") ^ " (QREG' m)" in
  let statement = parse_term(
    configuration ^ "!d n m:5 word. !s t:armstate. " ^
    source ^ " d n m s t <=> " ^
    target ^ " " ^ string_of_int width ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_TABLE_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_TBL%s%d_EQ"
    (if regs = 1 then "" else string_of_int regs) width in
  sail_hl_report (name, theorem);
  name,theorem;;

(* Each table form is proved by exactly one process when the claims are
   split across forked processes (proof-fork.ml). *)
sail_hl_proof_fork "SAIL_HOL_LIGHT_ARM_VECTOR_TABLE_PROOFS_OK";;

let SAIL_HL_ARM_VECTOR_TABLE_CLAIMS = map
  (fun (regs,width,definition) ->
    SAIL_HL_ARM_VECTOR_TABLE_CLAIM regs width definition)
  (filter (fun (regs,width,_) ->
     sail_hl_proof_shard (Printf.sprintf "TBL%d_%d" regs width)) [
  1,64,sail_hl_arm_5fTBL64;
  1,128,sail_hl_arm_5fTBL128;
  2,64,sail_hl_arm_5fTBL264;
  2,128,sail_hl_arm_5fTBL2128;
  3,64,sail_hl_arm_5fTBL364;
  3,128,sail_hl_arm_5fTBL3128;
]);;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_TABLE_PROOFS_OK";;
