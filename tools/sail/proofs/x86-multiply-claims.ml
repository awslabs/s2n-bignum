(* Complete register multiplication claims, loaded by x86-arithmetic.ml.

   Keep products opaque and compare their low/high words and flag choices.
   Widths below 32 preserve surrounding register bits; dword destinations
   clear the upper half. Implicit RAX/RDX outputs, legacy high-byte sources,
   two-input IMUL and independent MULX destinations retain every alias.
   The supplied-input and processor-configuration boundaries are documented
   in docs/X86.md. These are core register claims, not whole-step claims. *)

(* A product of two signed N-bit values fits in 2N bits. The remaining
   facts relate the low word, signed-fit test and high word to the same
   integer product. Prove these identities once at each requested width;
   do not expand multiplication into a circuit in an instruction proof. *)
let SAIL_HL_X86_NARROW_PRODUCT_FACTS width =
  if not(mem width [8;16;32]) then
    failwith "narrow multiply facts require width 8, 16 or 32";
  let narrow = mk_finty(num width)
  and wide = mk_finty(num(2 * width)) in
  let reduce = CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV THENC INT_REDUCE_CONV) in
  let dims = map (fun ty -> DIMINDEX_CONV(inst [ty,`:N`]
    `dimindex(:N)`)) [narrow;wide] in
  let x = parse_term(Printf.sprintf "x:%d word" width)
  and y = parse_term(Printf.sprintf "y:%d word" width)
  and bound = parse_term(Printf.sprintf "(&2 pow %d):int" (width - 1)) in
  let signed_product = prove
    (parse_term(Printf.sprintf
      "!x:%d word. !y:%d word. \
       ival(iword(ival x * ival y):%d word) = ival x * ival y"
      width width (2 * width)),
     REPEAT GEN_TAC THEN
     SUBGOAL_THEN
       (mk_conj(parse_term(Printf.sprintf
          "abs(ival(x:%d word)) <= &2 pow %d" width (width - 1)),
        parse_term(Printf.sprintf
          "abs(ival(y:%d word)) <= &2 pow %d" width (width - 1))))
       STRIP_ASSUME_TAC THENL
      [MP_TAC(ISPEC x IVAL_BOUND) THEN MP_TAC(ISPEC y IVAL_BOUND) THEN
       REWRITE_TAC[INT_ABS_BOUNDS] THEN
       CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
       CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
       ALL_TAC] THEN
     MATCH_MP_TAC IVAL_IWORD THEN
     MP_TAC(ISPECL
       [parse_term(Printf.sprintf "abs(ival(x:%d word))" width);
        bound;
        parse_term(Printf.sprintf "abs(ival(y:%d word))" width);
        bound] INT_LE_MUL2) THEN
     ASM_REWRITE_TAC[INT_ABS_POS; GSYM INT_ABS_MUL; INT_ABS_BOUNDS] THEN
     CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
     CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN INT_ARITH_TAC) in
  let remainder = reduce(INST_TYPE [narrow,`:N`] IWORD_REM_SIZE) in
  let low_iword = prove
    (parse_term(Printf.sprintf
      "!z:int. word_zx(iword z:%d word):%d word = iword z"
      (2 * width) width),
     GEN_TAC THEN REWRITE_TAC[WORD_ZX_SUBWORD] THEN
     CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
     SIMP_TAC(SAIL_HL_X86_SUBWORD_IWORD :: INT_DIV_1 ::
       ARITH_RULE(parse_term(Printf.sprintf "0 + %d <= %d"
         width (2 * width))) :: dims) THEN
     CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN
     REWRITE_TAC[INT_DIV_1; remainder] THEN REFL_TAC) in
  let sign_extension =
    reduce(INST_TYPE [narrow,`:M`;wide,`:N`] IVAL_WORD_SX) in
  let signed_fit = prove
    (parse_term(Printf.sprintf
      "!z:%d word. \
       ~(word_subword z (%d,%d):%d word = \
         word_sx(word(bitval(bit %d z)):1 word):%d word) <=> \
       ~(ival z = ival(word_zx z:%d word))"
      (2 * width) width width width (width - 1) width width),
     GEN_TAC THEN GEN_REWRITE_TAC
       (RAND_CONV o RAND_CONV o RAND_CONV) [GSYM sign_extension] THEN
     REWRITE_TAC[IVAL_EQ] THEN BITBLAST_TAC) in
  let widen =
    reduce(INST_TYPE [narrow,`:M`;`:512`,`:N`] VAL_WORD_ZX) in
  let nonzero = prove
    (parse_term(Printf.sprintf
      "!x:%d word. (word_zx x:512 word = word 0) <=> x = word 0"
      width),
     REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; widen]) in
  let half = reduce
    (INST_TYPE [narrow,`:M`;wide,`:N`] WORD_SUBWORD_DIMINDEX) in
  [signed_product;low_iword;signed_fit;nonzero;half];;

let SAIL_HL_X86_NARROW_PRODUCT_INSTANCES =
  map (fun width -> width,SAIL_HL_X86_NARROW_PRODUCT_FACTS width) [8;16;32];;

let SAIL_HL_X86_NARROW_WORD_PRODUCT_FACTS =
  List.concat(map snd SAIL_HL_X86_NARROW_PRODUCT_INSTANCES);;

(* A single AX write equals separate AH/AL writes on the whole state.
   The low-byte write sees the updated high byte; upper RAX bits remain
   unchanged. This assumes nothing about a source aliasing RAX. *)
let SAIL_HL_X86_AX_SPLIT_WRITE = prove
 (`!z:16 word. !s:x86state.
   write AX z s =
   write AL (word_zx z:8 word)
     (write AH (word_zx(word_ushr z 8):8 word) s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[AL; AH; AX; EAX; GSYM COMPONENT_COMPOSE_ASSOC; WRITE_SHORT] THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  CONV_TAC(DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN BITBLAST_TAC);;

List.iter (fun theorem ->
  if hyp theorem <> [] || frees(concl theorem) <> [] then
    failwith "open narrow multiply mathematical fact")
  (SAIL_HL_X86_AX_SPLIT_WRITE :: SAIL_HL_X86_NARROW_WORD_PRODUCT_FACTS);;

(* Prove the generated helper with an opaque operand before substituting
   a decoded register expression. Its nine-step OR circuit would otherwise
   copy that expression hundreds of times. These summaries follow from
   the actual generated definitions; no source calculation is replaced. *)
let SAIL_HL_X86_SOURCE_NONZERO_REWRITES =
  map (fun width ->
    let nonzero = if width = 64 then SAIL_HL_X86_ZERO_EXTEND64
      else List.nth (assoc width SAIL_HL_X86_NARROW_PRODUCT_INSTANCES) 3 in
    let definitions =
      [sail_hl_shared_x86_2darithmetic_or_5freduce_5f40;
       sail_hl_shared_x86_2darithmetic_zero_5fextend_5f3] in
    let theorem = prove
      (parse_term(Printf.sprintf
        "!x:%d word. sail_hl_shared_x86_2darithmetic_or_5freduce_5f40 x = \
         word(bitval(~(x = word 0))):1 word" width),
       SAIL_HL_X86_REWRITE_TAC(definitions @
         [LET_DEF;LET_END_DEF;FST;SND;NUM_OF_INT_OF_NUM]) THEN
       REWRITE_TAC[SAIL_HL_X86_OR_REDUCTION_512;nonzero]) in
    (* Match the literal normalization already checked in each root,
       including num_of_int(&1) becoming 1. *)
    CONV_RULE
      (DEPTH_CONV(DIMINDEX_CONV ORELSEC
        GEN_REWRITE_CONV I [NUM_OF_INT_OF_NUM] ORELSEC
        CHANGED_CONV NUM_RED_CONV ORELSEC INT_RED_CONV))
      (REWRITE_RULE definitions theorem)) [8;16;32;64];;

let SAIL_HL_X86_MULTIPLY_AX_WRITE =
  CONV_RULE(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV)
    (REWRITE_RULE
      (SAIL_HL_X86_LOW_SUBWORD `:8` :: SAIL_HL_X86_GPR_SHORT_REWRITES)
      (CONV_RULE(TOP_DEPTH_CONV(CHANGED_CONV COMPONENT_CANON_CONV))
        (REWRITE_RULE[AX;AL;AH;EAX;RAX] SAIL_HL_X86_AX_SPLIT_WRITE)));;

let SAIL_HL_X86_NARROW_MULTIPLY_RESULT_TAC width casts =
  let facts = if width = 64 then
    [SAIL_HL_X86_SIGNED_PRODUCT128; SAIL_HL_X86_LOW_IWORD128;
     SAIL_HL_X86_SIGNED_FIT128; SAIL_HL_X86_ZERO_EXTEND64;
     CONV_RULE(DEPTH_CONV DIMINDEX_CONV)
       (INST_TYPE [`:64`,`:M`;`:128`,`:N`] WORD_SUBWORD_DIMINDEX)]
    else assoc width SAIL_HL_X86_NARROW_PRODUCT_INSTANCES in
  let signed_product = List.nth facts 0
  and low_iword = List.nth facts 1
  and signed_fit = List.nth facts 2
  and nonzero = List.nth facts 3
  and half = List.nth facts 4 in
  REWRITE_TAC[BIT_WORD_BITVAL; SAIL_HL_X86_OR_REDUCTION_512;
    nonzero; WORD_XOR_EQ_0; signed_fit; signed_product] THEN
  REWRITE_TAC[half; WORD_USHR_ZERO] THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  (if width = 8 then
     REWRITE_TAC[GSYM SAIL_HL_X86_MULTIPLY_AX_WRITE]
   else ALL_TAC) THEN
  REWRITE_TAC(low_iword :: casts) THEN
  REWRITE_TAC[BIT_WORD_BITVAL; GSYM CF; GSYM OF; GSYM SF;
              GSYM ZF; GSYM AF; GSYM PF] THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
  REWRITE_TAC[SAIL_HL_X86_ARBITRARY_BIT0] THEN
  TRY(CONV_TAC(LAND_CONV
    (GEN_REWRITE_CONV I [SWAP_EXISTS_THM] THENC
     BINDER_CONV(BINDER_CONV(GEN_REWRITE_CONV I [SWAP_EXISTS_THM]))))) THEN
  (REFL_TAC ORELSE PRINT_GOAL_TAC);;

let SAIL_HL_X86_NARROW_MULTIPLY_TAC width definitions =
  let ty = mk_finty(num width) in
  let modulo = CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [ty,`:N`] WORD_MOD_SIZE) in
  REPEAT GEN_TAC THEN
  SAIL_HL_X86_REWRITE_TAC(definitions @
    [LET_DEF; LET_END_DEF; FST; SND; assign; SEQ; UNDEFINED_VALUES;
     SEQ_ID; GSYM WORD_IWORD; WORD_VAL]) THEN
  REWRITE_TAC[ASSIGNS_SEQ] THEN REWRITE_TAC[ASSIGNS_THM] THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LE; INT_OF_NUM_LT] THEN
  CONV_TAC(TOP_DEPTH_CONV(CHANGED_CONV COMPONENT_CANON_CONV)) THEN
  REWRITE_TAC SAIL_HL_X86_GPR_SHORT_REWRITES THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LE; INT_OF_NUM_LT;
    SAIL_HL_X86_LOW_SUBWORD ty; modulo; GSYM word_zx;
    SAIL_HL_X86_UNSIGNED_PRODUCT] THEN
  SAIL_HL_X86_NARROW_MULTIPLY_RESULT_TAC width [];;

let SAIL_HL_X86_MUL16_R_EQ = prove
 (`!m:4 word. !s t:x86state.
   sail_hl_X86_5fMUL16_5fR m s t <=>
   x86_MUL2 (DX,AX) (GPR16(Gpr m Lower_16)) s t`,
  SAIL_HL_X86_NARROW_MULTIPLY_TAC 16
    [sail_hl_X86_5fMUL16_5fR; x86_MUL2; DX; AX; EDX; EAX;
     RAX; RDX; GPR16]);;

let SAIL_HL_X86_MUL32_R_EQ = prove
 (`!m:4 word. !s t:x86state.
   sail_hl_X86_5fMUL32_5fR m s t <=>
   x86_MUL2 (RDX :> zerotop_32,RAX :> zerotop_32)
     (GPR32_Z(Gpr m Lower_32)) s t`,
  SAIL_HL_X86_NARROW_MULTIPLY_TAC 32
    [sail_hl_X86_5fMUL32_5fR; x86_MUL2; RAX; RDX; GPR32_Z]);;

let SAIL_HL_X86_IMUL116_R_EQ = prove
 (`!m:4 word. !s t:x86state.
   sail_hl_X86_5fIMUL116_5fR m s t <=>
   x86_IMUL2 (DX,AX) (GPR16(Gpr m Lower_16)) s t`,
  SAIL_HL_X86_NARROW_MULTIPLY_TAC 16
    [sail_hl_X86_5fIMUL116_5fR; x86_IMUL2; DX; AX; EDX; EAX;
     RAX; RDX; GPR16]);;

let SAIL_HL_X86_IMUL132_R_EQ = prove
 (`!m:4 word. !s t:x86state.
   sail_hl_X86_5fIMUL132_5fR m s t <=>
   x86_IMUL2 (RDX :> zerotop_32,RAX :> zerotop_32)
     (GPR32_Z(Gpr m Lower_32)) s t`,
  SAIL_HL_X86_NARROW_MULTIPLY_TAC 32
    [sail_hl_X86_5fIMUL132_5fR; x86_IMUL2; RAX; RDX; GPR32_Z]);;

let SAIL_HL_X86_MUL64_R_EQ = prove
 (`!m:4 word. !s t:x86state.
   sail_hl_X86_5fMUL64_5fR m s t <=>
   x86_MUL2 (RDX,RAX) (registers :> element m) s t`,
  SAIL_HL_X86_NARROW_MULTIPLY_TAC 64
    [sail_hl_X86_5fMUL64_5fR; x86_MUL2; RAX; RDX]);;

let SAIL_HL_X86_IMUL164_R_EQ = prove
 (`!m:4 word. !s t:x86state.
   sail_hl_X86_5fIMUL164_5fR m s t <=>
   x86_IMUL2 (RDX,RAX) (registers :> element m) s t`,
  SAIL_HL_X86_NARROW_MULTIPLY_TAC 64
    [sail_hl_X86_5fIMUL164_5fR; x86_IMUL2; RAX; RDX]);;

let SAIL_HL_X86_MUL8_R_EQ = prove
 (`!m:4 word. !s t:x86state.
   sail_hl_X86_5fMUL8_5fR m s t <=>
   x86_MUL2 (AH,AL) (GPR8(Gpr m Lower_8)) s t`,
  SAIL_HL_X86_NARROW_MULTIPLY_TAC 8
    [sail_hl_X86_5fMUL8_5fR; x86_MUL2; AH; AL; AX; EAX;
     RAX; GPR8]);;

let SAIL_HL_X86_IMUL18_R_EQ = prove
 (`!m:4 word. !s t:x86state.
   sail_hl_X86_5fIMUL18_5fR m s t <=>
   x86_IMUL2 (AH,AL) (GPR8(Gpr m Lower_8)) s t`,
  SAIL_HL_X86_NARROW_MULTIPLY_TAC 8
    [sail_hl_X86_5fIMUL18_5fR; x86_IMUL2; AH; AL; AX; EAX;
     RAX; GPR8]);;

(* Legacy fields four through seven select AH/CH/DH/BH. Split those two
   register-view cases symbolically without excluding high-byte aliases. *)
let SAIL_HL_X86_LEGACY_MULTIPLY_TAC definitions =
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `m:3 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `val(m:3 word) <= 7` ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `4 <= val(m:3 word)` THEN
  SAIL_HL_X86_NARROW_MULTIPLY_TAC 8 definitions;;

let SAIL_HL_X86_MUL8_LEGACY_R_EQ = prove
 (`!m:3 word. !s t:x86state.
   sail_hl_X86_5fMUL8_5fLEGACY_5fR m s t <=>
   x86_MUL2 (AH,AL)
     (if 4 <= val m
      then GPR8(Gpr (iword(&(val m) - &4):4 word) Upper_8)
      else GPR8(Gpr (word_zx m:4 word) Lower_8)) s t`,
  SAIL_HL_X86_LEGACY_MULTIPLY_TAC
    [sail_hl_X86_5fMUL8_5fLEGACY_5fR; x86_MUL2; AH; AL; AX; EAX;
     RAX; GPR8]);;

let SAIL_HL_X86_IMUL18_LEGACY_R_EQ = prove
 (`!m:3 word. !s t:x86state.
   sail_hl_X86_5fIMUL18_5fLEGACY_5fR m s t <=>
   x86_IMUL2 (AH,AL)
     (if 4 <= val m
      then GPR8(Gpr (iword(&(val m) - &4):4 word) Upper_8)
      else GPR8(Gpr (word_zx m:4 word) Lower_8)) s t`,
  SAIL_HL_X86_LEGACY_MULTIPLY_TAC
    [sail_hl_X86_5fIMUL18_5fLEGACY_5fR; x86_IMUL2; AH; AL; AX; EAX;
     RAX; GPR8]);;

(* Retained ModR/M decoding reconstructs both register fields. Strict-let
   normalization preserves intermediate captures before record projection;
   ordinary product and state identities finish the comparison. *)
let SAIL_HL_X86_NARROW_DECODED_MULTIPLY_TAC width definitions =
  let ty = mk_finty(num width) in
  let source_signed_value = REWRITE_RULE[]
    (CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
      (INST_TYPE[ty,`:M`;`:64`,`:N`] IVAL_WORD_SX)) in
  let modulo = CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
    (INST_TYPE [ty,`:N`] WORD_MOD_SIZE) in
  REPEAT GEN_TAC THEN
  SAIL_HL_X86_REWRITE_TAC(definitions @
    [assign; SEQ; UNDEFINED_VALUES; SEQ_ID; ASSIGNS_SEQ; ASSIGNS_THM;
     FST; SND; OUTL; OUTR; RDX]) THEN
  REWRITE_TAC SAIL_HL_X86_SOURCE_NONZERO_REWRITES THEN
  CONV_TAC SAIL_HL_X86_STRICT_LET_CONV THEN
  REWRITE_TAC[source_signed_value] THEN
  REWRITE_TAC[FST; SND; OUTL; OUTR; GSYM WORD_IWORD; WORD_VAL;
              WORD_SX_TRIVIAL; INT_OF_NUM_REM; NUM_OF_INT_OF_NUM] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[SAIL_HL_X86_REGISTER_BITS; WORD_VAL;
              SAIL_HL_X86_REGISTER_MOD;
              SAIL_HL_X86_UNSIGNED_PRODUCT; WORD_MOD_SIZE] THEN
  CONV_TAC SAIL_HL_X86_STRICT_LET_CONV THEN
  REWRITE_TAC[source_signed_value] THEN
  CONV_TAC(TOP_DEPTH_CONV(CHANGED_CONV COMPONENT_CANON_CONV)) THEN
  REWRITE_TAC SAIL_HL_X86_GPR_SHORT_REWRITES THEN
  REWRITE_TAC[SAIL_HL_X86_LOW_SUBWORD ty; modulo; GSYM word_zx] THEN
  SAIL_HL_X86_NARROW_MULTIPLY_RESULT_TAC width
    [IWORD_INT_MUL; IWORD_IVAL];;

let SAIL_HL_X86_IMUL16_RR_EQ = prove
 (`!d m:4 word. !s t:x86state.
   sail_hl_X86_5fIMUL16_5fRR d m s t <=>
   x86_IMUL3 (GPR16(Gpr d Lower_16))
     (GPR16(Gpr d Lower_16),GPR16(Gpr m Lower_16)) s t`,
  SAIL_HL_X86_NARROW_DECODED_MULTIPLY_TAC 16
    [sail_hl_X86_5fIMUL16_5fRR; x86_IMUL3; GPR16]);;

let SAIL_HL_X86_IMUL32_RR_EQ = prove
 (`!d m:4 word. !s t:x86state.
   sail_hl_X86_5fIMUL32_5fRR d m s t <=>
   x86_IMUL3 (GPR32_Z(Gpr d Lower_32))
     (GPR32_Z(Gpr d Lower_32),GPR32_Z(Gpr m Lower_32)) s t`,
  SAIL_HL_X86_NARROW_DECODED_MULTIPLY_TAC 32
    [sail_hl_X86_5fIMUL32_5fRR; x86_IMUL3; GPR32_Z]);;

let SAIL_HL_X86_IMUL64_RR_EQ = prove
 (`!d m:4 word. !s t:x86state.
   sail_hl_X86_5fIMUL64_5fRR d m s t <=>
   x86_IMUL3 (registers :> element d)
     (registers :> element d,registers :> element m) s t`,
  SAIL_HL_X86_NARROW_DECODED_MULTIPLY_TAC 64
    [sail_hl_X86_5fIMUL64_5fRR; x86_IMUL3]);;

let SAIL_HL_X86_MULX32_RRR_EQ = prove
 (`!hi lo m:4 word. !s t:x86state.
   sail_hl_X86_5fMULX32_5fRRR hi lo m s t <=>
   x86_MULX4 (GPR32_Z(Gpr hi Lower_32),GPR32_Z(Gpr lo Lower_32))
     (RDX :> zerotop_32,GPR32_Z(Gpr m Lower_32)) s t`,
  SAIL_HL_X86_NARROW_DECODED_MULTIPLY_TAC 32
    [sail_hl_X86_5fMULX32_5fRRR; x86_MULX4; GPR32_Z]);;

let SAIL_HL_X86_MULX64_RRR_EQ = prove
 (`!hi lo m:4 word. !s t:x86state.
   sail_hl_X86_5fMULX64_5fRRR hi lo m s t <=>
   x86_MULX4 (registers :> element hi,registers :> element lo)
     (RDX,registers :> element m) s t`,
  SAIL_HL_X86_NARROW_DECODED_MULTIPLY_TAC 64
    [sail_hl_X86_5fMULX64_5fRRR; x86_MULX4]);;

let SAIL_HL_X86_MULTIPLY_CLAIMS =
 ["SAIL_HL_X86_MUL8_R_EQ",SAIL_HL_X86_MUL8_R_EQ;
  "SAIL_HL_X86_MUL8_LEGACY_R_EQ",SAIL_HL_X86_MUL8_LEGACY_R_EQ;
  "SAIL_HL_X86_MUL16_R_EQ",SAIL_HL_X86_MUL16_R_EQ;
  "SAIL_HL_X86_MUL32_R_EQ",SAIL_HL_X86_MUL32_R_EQ;
  "SAIL_HL_X86_MUL64_R_EQ",SAIL_HL_X86_MUL64_R_EQ;
  "SAIL_HL_X86_IMUL18_R_EQ",SAIL_HL_X86_IMUL18_R_EQ;
  "SAIL_HL_X86_IMUL18_LEGACY_R_EQ",SAIL_HL_X86_IMUL18_LEGACY_R_EQ;
  "SAIL_HL_X86_IMUL116_R_EQ",SAIL_HL_X86_IMUL116_R_EQ;
  "SAIL_HL_X86_IMUL132_R_EQ",SAIL_HL_X86_IMUL132_R_EQ;
  "SAIL_HL_X86_IMUL164_R_EQ",SAIL_HL_X86_IMUL164_R_EQ;
  "SAIL_HL_X86_IMUL16_RR_EQ",SAIL_HL_X86_IMUL16_RR_EQ;
  "SAIL_HL_X86_IMUL32_RR_EQ",SAIL_HL_X86_IMUL32_RR_EQ;
  "SAIL_HL_X86_IMUL64_RR_EQ",SAIL_HL_X86_IMUL64_RR_EQ;
  "SAIL_HL_X86_MULX32_RRR_EQ",SAIL_HL_X86_MULX32_RRR_EQ;
  "SAIL_HL_X86_MULX64_RRR_EQ",SAIL_HL_X86_MULX64_RRR_EQ];;

List.iter (fun theorem ->
  if hyp theorem <> [] || frees(concl theorem) <> [] then
    failwith "open generated OR helper theorem")
  SAIL_HL_X86_SOURCE_NONZERO_REWRITES;;
