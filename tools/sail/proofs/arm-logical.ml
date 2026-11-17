(* Actual immediate and shifted-register logical instruction bodies.
   Each shifted claim quantifies all four source ShiftType constructors
   and every legal encoded amount. Immediate values are decoded full-width
   operands, not a claim about the architectural bitmask decoder.
   Register fields, SP/XZR cases and overlapping operands are universal.
   The proofs compare the flat contracts, not full-platform execution. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-logical.ml";;
needs "tools/sail/proofs/arm-lemmas.ml";;
needs "tools/sail/proofs/arm-logical-lemmas.ml";;

let SAIL_HL_ARM_LOGICAL_NORM definitions =
  ASM_REWRITE_TAC(definitions @
    [arm_AND; arm_ANDS; arm_BIC; arm_BICS; arm_ORR; arm_ORN;
     arm_EOR; arm_EON; arm_MOV; arm_MVN; arm_TST;
     LET_DEF; LET_END_DEF; FST; SND; NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ;
     INT_OF_NUM_REM; WORD_ZX_TRIVIAL;
     SAIL_HL_ARM_LOGICAL_KIND; sail_hl_type_ShiftType_DISTINCT;
     SAIL_HL_ARM_LOGICAL_READ_SHIFT; regshift_operation;
     SAIL_HL_ARM_LOGICAL_SP_DEST; GSYM SAIL_HL_ARM_LOGICAL_FIELD31;
     XREG'; WREG'; READ_RVALUE; GSYM WORD_BITVAL;
     GSYM VAL_EQ; VAL_WORD_0]) THEN
  ASM_SIMP_TAC[MOD_LT; SAIL_HL_ARM_LOGICAL_ROTATE32;
               SAIL_HL_ARM_LOGICAL_ROTATE64] THEN
  REWRITE_TAC[SAIL_HL_ARM_LOGICAL_PACKED_REWRITES;
              SAIL_HL_ARM_MSB32; SAIL_HL_ARM_MSB64;
              assign; SEQ] THEN
  ASM_SIMP_TAC[SAIL_HL_ARM_XFLAG_COMMUTE;
               SAIL_HL_ARM_WFLAG_COMMUTE] THEN
  ASM_REWRITE_TAC[WSP; WRITE_ZEROTOP_32; ARM_ZERO_REGISTER;
                  READ_RVALUE; WRITE_RVALUE] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  ASM_REWRITE_TAC[ARM_ZERO_REGISTER; READ_RVALUE; WRITE_RVALUE] THEN
  PRINT_GOAL_TAC;;

(* Statement assembly only removes repetition in the handwritten proof
   claims. Exported instruction semantics come solely from the typed Sail
   backend. Every assembled statement is proved by the HOL kernel. *)
let SAIL_HL_ARM_LOGICAL_SOURCE_NAME definition =
  let _, body = strip_forall (concl definition) in
  fst(dest_const(fst(strip_comb(lhand body))));;

let SAIL_HL_ARM_LOGICAL_CLAIM shifted instruction width definition =
  let reg = if width = 32 then "WREG'" else "XREG'" in
  let spreg = if width = 32 then "WREG_SP" else "XREG_SP" in
  let flags = mem instruction ["ANDS"; "BICS"; "TST"] in
  let unary = mem instruction ["MOV"; "MVN"] in
  let test = instruction = "TST" in
  let source_name = SAIL_HL_ARM_LOGICAL_SOURCE_NAME definition in
  let prefix = if test then "n m" else if unary then "d m" else "d n m" in
  let prefix = if shifted then prefix
               else if test then "n" else if unary then "d" else "d n" in
  let amount_width = if width = 32 then 5 else 6 in
  let quantifiers = "!" ^ prefix ^ ":5 word. " ^
    (if shifted then Printf.sprintf
      "!amount:%d word. !kind:sail_hl_type_ShiftType. " amount_width
     else Printf.sprintf "!imm:%d word. " width) ^
    "!s t:armstate. " in
  let source_args = prefix ^ (if shifted then " amount kind" else " imm") in
  let destination = if shifted || flags then reg ^ " d" else spreg ^ " d" in
  let operand = if shifted then
      "Shiftedreg (" ^ reg ^ " m) (sail_hl_arm_logical_kind kind) (val amount)"
    else "rvalue imm" in
  let target = "arm_" ^ instruction ^
    (if test then " (" ^ reg ^ " n) (" ^ operand ^ ")"
     else if unary then " (" ^ destination ^ ") (" ^ operand ^ ")"
     else " (" ^ destination ^ ") (" ^ reg ^ " n) (" ^ operand ^ ")") in
  let statement = parse_term (quantifiers ^ source_name ^ " " ^ source_args ^
    " s t <=> " ^ target ^ " s t") in
  let prepare =
    (if test then ALL_TAC else ASM_CASES_TAC `d:5 word = word 31`) THEN
    (if shifted then
      STRUCT_CASES_TAC
        (SPEC `kind:sail_hl_type_ShiftType` (cases "sail_hl_type_ShiftType")) THEN
      MP_TAC(ISPEC (parse_term(Printf.sprintf "amount:%d word" amount_width)) VAL_BOUND) THEN
      CONV_TAC (DEPTH_CONV DIMINDEX_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC
    else ALL_TAC) in
  let theorem = prove(statement,
    REPEAT GEN_TAC THEN prepare THEN SAIL_HL_ARM_LOGICAL_NORM [definition]) in
  let marker = Printf.sprintf "SAIL_HL_ARM_%s%d_%s_EQ"
    instruction width (if shifted then "SHIFT" else "IMM") in
  sail_hl_report (marker, theorem);
  marker, theorem;;

let SAIL_HL_ARM_LOGICAL_IMMEDIATE_CLAIMS = map
  (fun (instruction,width,definition) ->
    SAIL_HL_ARM_LOGICAL_CLAIM false instruction width definition)
 [("AND",32,sail_hl_ARM_5fAND32_5fIMM);
  ("AND",64,sail_hl_ARM_5fAND64_5fIMM);
  ("ANDS",32,sail_hl_ARM_5fANDS32_5fIMM);
  ("ANDS",64,sail_hl_ARM_5fANDS64_5fIMM);
  ("ORR",32,sail_hl_ARM_5fORR32_5fIMM);
  ("ORR",64,sail_hl_ARM_5fORR64_5fIMM);
  ("EOR",32,sail_hl_ARM_5fEOR32_5fIMM);
  ("EOR",64,sail_hl_ARM_5fEOR64_5fIMM);
  ("MOV",32,sail_hl_ARM_5fMOV32_5fIMM);
  ("MOV",64,sail_hl_ARM_5fMOV64_5fIMM);
  ("TST",32,sail_hl_ARM_5fTST32_5fIMM);
  ("TST",64,sail_hl_ARM_5fTST64_5fIMM)];;

let SAIL_HL_ARM_LOGICAL_SHIFTED_CLAIMS = map
  (fun (instruction,width,definition) ->
    SAIL_HL_ARM_LOGICAL_CLAIM true instruction width definition)
 [("AND",32,sail_hl_ARM_5fAND32_5fSHIFT);
  ("AND",64,sail_hl_ARM_5fAND64_5fSHIFT);
  ("ANDS",32,sail_hl_ARM_5fANDS32_5fSHIFT);
  ("ANDS",64,sail_hl_ARM_5fANDS64_5fSHIFT);
  ("BIC",32,sail_hl_ARM_5fBIC32_5fSHIFT);
  ("BIC",64,sail_hl_ARM_5fBIC64_5fSHIFT);
  ("BICS",32,sail_hl_ARM_5fBICS32_5fSHIFT);
  ("BICS",64,sail_hl_ARM_5fBICS64_5fSHIFT);
  ("ORR",32,sail_hl_ARM_5fORR32_5fSHIFT);
  ("ORR",64,sail_hl_ARM_5fORR64_5fSHIFT);
  ("ORN",32,sail_hl_ARM_5fORN32_5fSHIFT);
  ("ORN",64,sail_hl_ARM_5fORN64_5fSHIFT);
  ("EOR",32,sail_hl_ARM_5fEOR32_5fSHIFT);
  ("EOR",64,sail_hl_ARM_5fEOR64_5fSHIFT);
  ("EON",32,sail_hl_ARM_5fEON32_5fSHIFT);
  ("EON",64,sail_hl_ARM_5fEON64_5fSHIFT);
  ("MOV",32,sail_hl_ARM_5fMOV32_5fSHIFT);
  ("MOV",64,sail_hl_ARM_5fMOV64_5fSHIFT);
  ("MVN",32,sail_hl_ARM_5fMVN32_5fSHIFT);
  ("MVN",64,sail_hl_ARM_5fMVN64_5fSHIFT);
  ("TST",32,sail_hl_ARM_5fTST32_5fSHIFT);
  ("TST",64,sail_hl_ARM_5fTST64_5fSHIFT)];;

assert(length SAIL_HL_ARM_LOGICAL_IMMEDIATE_CLAIMS = 12);;
assert(length SAIL_HL_ARM_LOGICAL_SHIFTED_CLAIMS = 22);;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_LOGICAL_PROOFS_OK";;
