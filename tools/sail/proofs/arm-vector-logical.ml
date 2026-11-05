(* Agreement for actual register and modified-immediate vector logical bodies.
   Access checking is an explicit successful-enabled-AdvSIMD contract.
   Q64 operations clear bits64..127; all32 vector fields, including31 and
   every operand/destination overlap, are quantified. Immediate roots take
   arbitrary predecoded masks, not a proved AdvSIMDExpandImm decoder.
   The eighteen claims compare complete initial/final state relations. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-logical.ml";;

(* Pure bitwise identities used after translating the actual VBIT/VBIF body.
   These are universal word identities, not extra architecture assumptions. *)
(* Native specialization evaluates Ones to an unsigned numeral. Recover the
   complement form before applying the identities below. *)
let SAIL_HL_ARM_VECTOR_ONES64 =
  SYM(WORD_REDUCE_CONV `word_not(word 0:64 word)`);;
let SAIL_HL_ARM_VECTOR_ONES128 =
  SYM(WORD_REDUCE_CONV `word_not(word 0:128 word)`);;

let SAIL_HL_ARM_VECTOR_BIT = WORD_RULE
 `word_xor (d:N word) (word_and (word_xor d n) m) =
  word_or (word_and d (word_not m)) (word_and n m)`;;

let SAIL_HL_ARM_VECTOR_BIF = WORD_RULE
 `word_xor (d:N word) (word_and (word_xor d n) (word_not m)) =
  word_or (word_and d m) (word_and n (word_not m))`;;

let SAIL_HL_ARM_VECTOR_EOR = WORD_RULE
 `word_xor (m:N word)
    (word_and (word_xor (word 0) n) (word_not(word 0))) =
  word_xor m n`;;

let SAIL_HL_ARM_VECTOR_LOW64 = prove
 (`!x:128 word. (word_subword x (0,64):64 word) = word_zx x`,
  GEN_TAC THEN ONCE_REWRITE_TAC[WORD_ZX_SUBWORD] THEN
  REWRITE_TAC[DIMINDEX_64]);;

let SAIL_HL_ARM_VECTOR_LOGICAL_NORM definitions =
  REWRITE_TAC(definitions @
    [arm_AND_VEC; arm_BIC_VEC; arm_ORR_VEC; arm_EOR_VEC; arm_BIT; arm_BIF;
     arm_MOV_VEC; assign; LET_DEF; LET_END_DEF; FST; SND;
     NUM_OF_INT_OF_NUM; QREG'; DREG; READ_ZEROTOP_64; WRITE_ZEROTOP_64;
     READ_RVALUE; DIMINDEX_64; DIMINDEX_128; WORD_ZX_TRIVIAL;
     SAIL_HL_ARM_VECTOR_ONES64; SAIL_HL_ARM_VECTOR_ONES128;
     SAIL_HL_ARM_VECTOR_EOR; SAIL_HL_ARM_VECTOR_BIT; SAIL_HL_ARM_VECTOR_BIF;
     SAIL_HL_ARM_VECTOR_LOW64]) THEN
  SIMP_TAC[WORD_ZX_AND; WORD_ZX_OR; WORD_ZX_XOR; WORD_ZX_NOT;
           WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_128; ARITH] THEN
  REWRITE_TAC[WORD_AND_SYM; WORD_OR_SYM; WORD_XOR_SYM] THEN
  CONV_TAC WORD_REDUCE_CONV;;

(* The table assembles handwritten proof claims only. Generated instruction
   definitions are consumed unchanged from the typed Sail backend. *)
let SAIL_HL_ARM_VECTOR_LOGICAL_CLAIM immediate instruction width definition =
  let _, body = strip_forall (concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let unary = instruction = "MOV_VEC" in
  let fields = if immediate then "d" else if unary then "d n" else "d n m" in
  let quantifiers = "!" ^ fields ^ ":5 word. " ^
    (if immediate then Printf.sprintf "!imm:%d word. " width else "") ^
    "!s t:armstate. " in
  let source_arguments = fields ^ (if immediate then " imm" else "") in
  let target_arguments = "(QREG' d) " ^
    (if immediate then Printf.sprintf "(QREG' d) (rvalue(word_zx imm:128 word)) %d" width
     else "(QREG' n) " ^ (if unary then "" else "(QREG' m) ") ^
          string_of_int width) in
  let statement = parse_term(quantifiers ^ source ^ " " ^ source_arguments ^
    " s t <=> arm_" ^ instruction ^ " " ^ target_arguments ^ " s t") in
  let theorem = prove(statement,
    REPEAT GEN_TAC THEN SAIL_HL_ARM_VECTOR_LOGICAL_NORM [definition]) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s%d_%s_EQ"
    instruction width (if immediate then "IMM" else "REG") in
  sail_hl_report (name, theorem);
  name, theorem;;

let SAIL_HL_ARM_VECTOR_LOGICAL_REGISTER_CLAIMS = map
  (fun (instruction, width, definition) ->
    SAIL_HL_ARM_VECTOR_LOGICAL_CLAIM false instruction width definition) [
  "AND_VEC",64,sail_hl_arm_5fAND_5fVEC64_5fREG;
  "AND_VEC",128,sail_hl_arm_5fAND_5fVEC128_5fREG;
  "BIC_VEC",64,sail_hl_arm_5fBIC_5fVEC64_5fREG;
  "BIC_VEC",128,sail_hl_arm_5fBIC_5fVEC128_5fREG;
  "ORR_VEC",64,sail_hl_arm_5fORR_5fVEC64_5fREG;
  "ORR_VEC",128,sail_hl_arm_5fORR_5fVEC128_5fREG;
  "EOR_VEC",64,sail_hl_arm_5fEOR_5fVEC64_5fREG;
  "EOR_VEC",128,sail_hl_arm_5fEOR_5fVEC128_5fREG;
  "BIT",64,sail_hl_arm_5fBIT64_5fREG;
  "BIT",128,sail_hl_arm_5fBIT128_5fREG;
  "BIF",64,sail_hl_arm_5fBIF64_5fREG;
  "BIF",128,sail_hl_arm_5fBIF128_5fREG;
  "MOV_VEC",64,sail_hl_arm_5fMOV_5fVEC64_5fREG;
  "MOV_VEC",128,sail_hl_arm_5fMOV_5fVEC128_5fREG;
];;

let SAIL_HL_ARM_VECTOR_LOGICAL_IMMEDIATE_CLAIMS = map
  (fun (instruction, width, definition) ->
    SAIL_HL_ARM_VECTOR_LOGICAL_CLAIM true instruction width definition) [
  "BIC_VEC",64,sail_hl_arm_5fBIC_5fVEC64_5fIMM;
  "BIC_VEC",128,sail_hl_arm_5fBIC_5fVEC128_5fIMM;
  "ORR_VEC",64,sail_hl_arm_5fORR_5fVEC64_5fIMM;
  "ORR_VEC",128,sail_hl_arm_5fORR_5fVEC128_5fIMM;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_LOGICAL_PROOFS_OK";;
