(* Every single-register/byte encoded memory form; actual Sail roots only. *)
loadt "arm/proofs/base.ml";;
loadt "tools/sail/proofs/fresh-model.ml";;
module Sail_hl_memory_model = struct
loadt "tools/sail/proofs/arm-memory-model-loader.ml";;
loadt "tools/sail/_build/arm-memory-single.ml";;
end;;
loadt "tools/sail/proofs/arm-memory-support.ml";;

let SAIL_HL_ARM_MEMORY_FORM operation width view form fields offset =
  let component register =
    (if view = "GPR" then (if width = 32 then "WREG'" else "XREG'")
     else if width = 64 then "DREG'" else "QREG'") ^ " " ^ register in
  let target = "arm_" ^ operation ^ " (" ^ component "rt" ^
    ") (XREG_SP n) (" ^ offset ^ ")" in
  "arm_" ^ operation ^ string_of_int width ^ "_" ^ view ^ "_" ^ form,
  fields,parse_term target;;

let SAIL_HL_ARM_MEMORY_SINGLE_FORMS =
  let forms operation width view scalar_forms =
    let byte = operation = "LDRB" || operation = "STRB" in
    let ordinary = map (fun form ->
      let fields,offset = match form with
      | "PRE" | "POST" | "UNSCALED" ->
          SAIL_HL_ARM_MEMORY_FIELDS ["rt";"n"] @ ["imm",`:9 word`],
          (if form = "PRE" then "Preimmediate_Offset"
           else if form = "POST" then "Postimmediate_Offset"
           else "Immediate_Offset") ^ " (word_sx (imm:9 word))"
      | "UIMM" ->
          SAIL_HL_ARM_MEMORY_FIELDS ["rt";"n"] @ ["imm",`:12 word`],
          if byte then "Immediate_Offset (word_zx (imm:12 word))"
          else "Immediate_Offset (word (val (imm:12 word) * " ^
               string_of_int(width / 8) ^ "))"
      | "REG0" | "REGS" ->
          SAIL_HL_ARM_MEMORY_FIELDS ["rt";"n";"m"],
          if form = "REG0" then "Register_Offset (XREG' m)"
          else "Shiftreg_Offset (XREG' m) " ^
               string_of_int(if width = 32 then 2 else if width = 64 then 3 else 4)
      | _ -> failwith "unknown scalar memory form" in
      SAIL_HL_ARM_MEMORY_FORM operation width view form fields offset
    ) scalar_forms in
    let structures = if view = "GPR" then [] else
      flat(map (fun element -> map (fun mode ->
        let fields = SAIL_HL_ARM_MEMORY_FIELDS
          (["rt";"n"] @ if mode = "POSTR" then ["m"] else []) in
        SAIL_HL_ARM_MEMORY_FORM operation width view
          ("LD1_E" ^ string_of_int element ^ "_" ^ mode) fields
          (SAIL_HL_ARM_MEMORY_POST mode (width / 8))
      ) ["NO";"POSTI";"POSTR"]) [8;16;32;64]) in
    ordinary @ structures in
  flat(map (fun operation ->
    flat(map (fun width ->
      forms operation width "GPR" ["POST";"PRE";"UIMM";"REG0";"REGS";"UNSCALED"]
    ) [32;64]) @
    forms operation 64 "SIMD" ["POST";"PRE";"UIMM"] @
    forms operation 128 "SIMD" ["POST";"PRE";"UIMM";"REG0";"REGS";"UNSCALED"]
  ) ["LDR";"STR"]) @
  flat(map (fun operation ->
    forms operation 32 "GPR" ["POST";"PRE";"UIMM";"REG0";"UNSCALED"]
  ) ["LDRB";"STRB"]);;

(* A vector LD1 reads consecutive lanes and writes the destination after
   each lane. The HOL instruction reads the entire word and writes it once.
   The rules below connect those two expressions. They do not introduce
   an instruction model, select an undefined value or restrict operands. *)
let SAIL_HL_ARM_MEMORY_SINGLE_BASE_INDEX = prove
 (`!t:5 word.
     num_of_int ((&(val t) + &0) rem &32) = val t`,
  GEN_TAC THEN REWRITE_TAC[INT_ADD_RID; INT_OF_NUM_REM;
    NUM_OF_INT_OF_NUM] THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `t:5 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:5)`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* Register-offset addressing selects all 64 bits of its X register.
   That slice is the original word, including XZR's zero value. *)
let SAIL_HL_ARM_MEMORY_SINGLE_REGISTER_SLICE = prove
 (`!x:64 word. word_subword x (0,64) = x`,
  GEN_TAC THEN MATCH_MP_TAC WORD_SUBWORD_TRIVIAL THEN
  REWRITE_TAC[DIMINDEX_64; LE_REFL]);;

(* Sail truncates a shifted register to the bits that survive the shift,
   then joins the zero low bits. These are exactly the 64-bit HOL shifts,
   including when the high bits of the original register are nonzero. *)
let SAIL_HL_ARM_MEMORY_SINGLE_SHIFT_RULES =
  map (fun shift ->
    prove(parse_term
      ("!x:64 word. (word_join (word_subword x (0," ^
       string_of_int (64 - shift) ^ "):" ^ string_of_int (64 - shift) ^
       " word) (word 0:" ^ string_of_int shift ^ " word):64 word) = " ^
       "word_shl x " ^ string_of_int shift),
      GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
      CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC[BIT_WORD_JOIN; BIT_WORD_SUBWORD; BIT_WORD_SHL;
        BIT_WORD_0] THEN
      CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[])) [2;3;4];;

(* The D-register E64 form has one already-normalized complete lane,
   rather than a subword expression that the multi-lane rule can match. *)
let SAIL_HL_ARM_MEMORY_SINGLE_INSERT64 = prove
 (`!old:64 word. !x:64 word. word_insert old (0,64) x = x`,
  CONV_TAC WORD_BLAST);;

(* STRB observes the low eight bits. Truncating its X-register value to
   the public W-register operand first does not change those bits. *)
let SAIL_HL_ARM_MEMORY_SINGLE_BYTE_CAST = prove
 (`!x:64 word.
     (word (val (word_zx x:32 word)):8 word) = word (val x)`,
  GEN_TAC THEN REWRITE_TAC[GSYM word_zx; WORD_EQ_BITS_ALT] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[BIT_WORD_ZX] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* Each supported element size divides the whole register width exactly.
   Prove that inserting every slice of a word reconstructs that word,
   regardless of the old destination contents. WORD_BLAST proves these
   fixed-width word equalities in HOL; no memory or state is assumed here. *)
let SAIL_HL_ARM_MEMORY_SINGLE_INSERT_RULES =
  flat(map (fun width ->
    map (fun element ->
      let old = "(old:" ^ string_of_int width ^ " word)" in
      let whole = "(whole:" ^ string_of_int width ^ " word)" in
      let expression =
        itlist (fun position previous ->
          "(word_insert " ^ previous ^ " (" ^ string_of_int position ^
          "," ^ string_of_int element ^ ") (word_subword " ^ whole ^
          " (" ^ string_of_int position ^ "," ^ string_of_int element ^
          "):" ^ string_of_int element ^ " word):" ^
          string_of_int width ^ " word)")
        (rev(map (fun i -> i * element) (0--(width / element - 1)))) old in
      prove(parse_term ("!old:" ^ string_of_int width ^
        " word. !whole:" ^ string_of_int width ^ " word. " ^
        expression ^ " = whole"), CONV_TAC WORD_BLAST)
    ) [8;16;32;64]
  ) [64;128]);;

let SAIL_HL_ARM_MEMORY_SINGLE_WORD_READ term =
  try
    ignore(SAIL_HL_ARM_MEMORY_WORD_READ_PARTS term);
    let width = SAIL_HL_ARM_MEMORY_PAIR_BYTE_WIDTH term in
    width = 8 || width = 16
  with Failure _ -> false;;

(* Locate the whole-word memory reads already present in the comparison.
   The lane conversion requires the same base and initial state, and proves
   the byte extent. It leaves an unrelated read unchanged. *)
let SAIL_HL_ARM_MEMORY_SINGLE_LANES_TAC =
  W(fun (_,goal) ->
    let reads = find_terms SAIL_HL_ARM_MEMORY_SINGLE_WORD_READ goal in
    CONV_TAC(TOP_DEPTH_CONV(fun term ->
      tryfind (fun whole ->
        if SAIL_HL_ARM_MEMORY_PAIR_BYTE_WIDTH term >=
           SAIL_HL_ARM_MEMORY_PAIR_BYTE_WIDTH whole then
          failwith "not a smaller lane";
        SAIL_HL_ARM_MEMORY_LANE_CONV whole term) reads)));;

(* Split a whole-word write into the same ascending-address lane writes
   used by LD1 stores. A balanced word_join of all slices reconstructs the
   original word; the checked pair-store conversion then splits each join.
   Its width and non-overlap premises are proved for every split, including
   an address range that wraps at the end of the 64-bit address space. *)
let SAIL_HL_ARM_MEMORY_SINGLE_STORE_RULES =
  flat(map (fun width ->
    map (fun element ->
      let whole = "(x:" ^ string_of_int width ^ " word)" in
      let positions = map (fun i -> i * element)
        (0--(width / element - 1)) in
      let slice position =
        "(word_subword " ^ whole ^ " (" ^ string_of_int position ^
        "," ^ string_of_int element ^ "):" ^
        string_of_int element ^ " word)" in
      let rec joined positions = match positions with
        | [position] -> slice position
        | _ ->
            let low,high = chop_list (length positions / 2) positions in
            "(word_join " ^ joined high ^ " " ^ joined low ^ ":" ^
            string_of_int (length positions * element) ^ " word)" in
      let join_rule = prove(parse_term
        ("!x:" ^ string_of_int width ^ " word. x = " ^ joined positions),
        CONV_TAC WORD_BLAST) in
      let stores =
        itlist (fun position previous ->
          "(write (memory :> wbytes (word_add a (word " ^
          string_of_int (position / 8) ^ "))) " ^ slice position ^
          " " ^ previous ^ ")") (rev positions) "(s:armstate)" in
      prove(parse_term
        ("!a:64 word. !x:" ^ string_of_int width ^
         " word. !s:armstate. write (memory :> wbytes a) x s = " ^ stores),
        REPEAT GEN_TAC THEN
        GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [join_rule] THEN
        CONV_TAC(LAND_CONV
          (TOP_DEPTH_CONV SAIL_HL_ARM_MEMORY_PAIR_STORE_CONV)) THEN
        PURE_REWRITE_TAC[WORD_ADD_0; WORD_ADD_ASSOC_CONSTS] THEN
        CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REFL_TAC)
    ) [8;16;32;64]
  ) [64;128]);;

(* Source addresses normalize the first lane's a + word 0 to a. Match
   that syntax in the original checked store equation before reversing
   it. Fusion is applied after event erasure makes the memory writes
   contiguous; it preserves the final contents of every memory byte.
   It does not claim equality of the original access-event sequences. *)
let SAIL_HL_ARM_MEMORY_SINGLE_STORE_FUSION_RULES =
  map (fun theorem -> GSYM(PURE_REWRITE_RULE [WORD_ADD_0] theorem))
    SAIL_HL_ARM_MEMORY_SINGLE_STORE_RULES;;

let SAIL_HL_ARM_MEMORY_SINGLE_TAC source_definition target_definition =
  REPEAT GEN_TAC THEN
  (* POSTR encoding 31 selects an immediate increment; the other encodings
     read the offset register. An exhaustive proof split preserves all
     values, including ZR in the ordinary register-offset forms. *)
  W(fun (_,goal) ->
    if vfree_in `m:5 word` goal then ASM_CASES_TAC `m:5 word = word 31`
    else ALL_TAC) THEN
  DISCH_THEN(fun guard ->
    MAP_EVERY ASSUME_TAC
      (guard::SAIL_HL_ARM_MEMORY_SINGLE_GUARD_FACTS guard) THEN MP_TAC guard) THEN
  SAIL_HL_ARM_MEMORY_PREPARE_TAC [] source_definition target_definition THEN
  PURE_REWRITE_TAC[SAIL_HL_ARM_MEMORY_SINGLE_BASE_INDEX;
    WREG'; DREG'; QREG'; WREG; DREG;
    READ_ZEROTOP_32; READ_ZEROTOP_64;
    WRITE_ZEROTOP_32; WRITE_ZEROTOP_64;
    BYTES8_WBYTES; BYTES16_WBYTES; BYTES32_WBYTES;
    BYTES64_WBYTES; BYTES128_WBYTES; WORD_ADD_0] THEN
  (* The actual writeback guard permits SP encoding 31. In the other
     base case it proves the source's overlap condition false; simplify
     that implication before eliminating the unused unknown choices. *)
  SAIL_HL_ARM_MEMORY_SINGLE_BRANCH_FACTS_TAC THEN
  PURE_ASM_REWRITE_TAC[COND_CLAUSES; COND_ID] THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
  (* The guard implication above can expose a previously conditional sum
     constructor. Reduce it with the original generated case equations
     before comparing memory values; no branch choice is added. *)
  SAIL_HL_ARM_MEMORY_STATE_CBV_TAC [source_definition] THEN
  PURE_REWRITE_TAC
    (SAIL_HL_ARM_MEMORY_SINGLE_REGISTER_SLICE :: MULT_CLAUSES ::
     SAIL_HL_ARM_MEMORY_SINGLE_SHIFT_RULES) THEN
  SAIL_HL_ARM_MEMORY_SINGLE_LANES_TAC THEN
  PURE_REWRITE_TAC
    (SAIL_HL_ARM_MEMORY_SINGLE_INSERT64 ::
     SAIL_HL_ARM_MEMORY_SINGLE_BYTE_CAST ::
     SAIL_HL_ARM_MEMORY_SINGLE_INSERT_RULES) THEN
  PURE_REWRITE_TAC SAIL_HL_ARM_MEMORY_SINGLE_STORE_FUSION_RULES THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_ARM_MEMORY_ERASE_WRITE_CONV) THEN
  PURE_REWRITE_TAC SAIL_HL_ARM_MEMORY_SINGLE_STORE_FUSION_RULES THEN
  PURE_REWRITE_TAC[EXISTS_SIMP; UNWIND_THM1; UNWIND_THM2] THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_ARM_MEMORY_ERASE_WRITE_CONV) THEN
  PURE_REWRITE_TAC SAIL_HL_ARM_MEMORY_SINGLE_STORE_FUSION_RULES THEN
  REWRITE_TAC[] THEN PRINT_GOAL_TAC;;

SAIL_HL_ARM_MEMORY_CLAIMS "SAIL_HOL_LIGHT_ARM_MEMORY_SINGLE_PROOFS_OK"
  SAIL_HL_ARM_MEMORY_SINGLE_TAC SAIL_HL_ARM_MEMORY_SINGLE_FORMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_MEMORY_SINGLE_PROOFS_OK";;
