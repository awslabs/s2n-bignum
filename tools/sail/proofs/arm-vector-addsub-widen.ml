(* All thirty decoded long/wide forms, including both narrow source halves.
   Signed casts use ival; unsigned casts use val. Per-lane addition and
   subtraction are modular words; only their packing into Q128 is compared
   bitwise. Register31 and every overlap remain universally quantified. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-addsub-widen.ml";;
needs "tools/sail/proofs/arm-vector-model-parameters.ml";;
needs "tools/sail/proofs/arm-vector-multiply-long-support.ml";;

let SAIL_HL_ARM_VECTOR_ADDSUB_WIDEN_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_SSUBL_ALT; arm_SSUBL2_ALT;
    arm_USUBL_ALT; arm_USUBL2_ALT; arm_SADDW_ALT; arm_SADDW2_ALT;
    arm_SSUBW_ALT; arm_SSUBW2_ALT; arm_USUBW_ALT; arm_USUBW2_ALT;
    assign; LET_DEF; LET_END_DEF; FST; SND; QREG'; DREG;
    READ_ZEROTOP_64; NUM_OF_INT_OF_NUM;
    IWORD_INT_ADD; IWORD_INT_SUB; GSYM WORD_IWORD;
    GSYM word_sx; GSYM word_zx] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[WORD_SUBWORD_SUBWORD; WORD_SUBWORD_ZX;
    DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(REDEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[IWORD_IVAL; WORD_ZX_TRIVIAL; WORD_SX_TRIVIAL; WORD_ADD_SYM] THEN
  SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_VALUE_TAC;;

let SAIL_HL_ARM_VECTOR_ADDSUB_WIDEN_CLAIM instruction element definition =
  let configuration,source =
    SAIL_HL_ARM_VECTOR_MODEL_APPLICATION 3 definition in
  let statement = parse_term(
    configuration ^ "!d n m:5 word. !s t:armstate. " ^ source ^
    " d n m s t <=> arm_" ^
    instruction ^ " (QREG' d) (QREG' n) (QREG' m) " ^
    string_of_int element ^ " s t") in
  let theorem = prove(statement, SAIL_HL_ARM_VECTOR_ADDSUB_WIDEN_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s128E%d_EQ" instruction element in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_ADDSUB_WIDEN_CLAIMS = map
  (fun (instruction,element,definition) ->
    SAIL_HL_ARM_VECTOR_ADDSUB_WIDEN_CLAIM instruction element definition) [
  "SSUBL",8,sail_hl_arm_5fSSUBL128E8;
  "SSUBL",16,sail_hl_arm_5fSSUBL128E16;
  "SSUBL",32,sail_hl_arm_5fSSUBL128E32;
  "SSUBL2",8,sail_hl_arm_5fSSUBL2128E8;
  "SSUBL2",16,sail_hl_arm_5fSSUBL2128E16;
  "SSUBL2",32,sail_hl_arm_5fSSUBL2128E32;
  "USUBL",8,sail_hl_arm_5fUSUBL128E8;
  "USUBL",16,sail_hl_arm_5fUSUBL128E16;
  "USUBL",32,sail_hl_arm_5fUSUBL128E32;
  "USUBL2",8,sail_hl_arm_5fUSUBL2128E8;
  "USUBL2",16,sail_hl_arm_5fUSUBL2128E16;
  "USUBL2",32,sail_hl_arm_5fUSUBL2128E32;
  "SADDW",8,sail_hl_arm_5fSADDW128E8;
  "SADDW",16,sail_hl_arm_5fSADDW128E16;
  "SADDW",32,sail_hl_arm_5fSADDW128E32;
  "SADDW2",8,sail_hl_arm_5fSADDW2128E8;
  "SADDW2",16,sail_hl_arm_5fSADDW2128E16;
  "SADDW2",32,sail_hl_arm_5fSADDW2128E32;
  "SSUBW",8,sail_hl_arm_5fSSUBW128E8;
  "SSUBW",16,sail_hl_arm_5fSSUBW128E16;
  "SSUBW",32,sail_hl_arm_5fSSUBW128E32;
  "SSUBW2",8,sail_hl_arm_5fSSUBW2128E8;
  "SSUBW2",16,sail_hl_arm_5fSSUBW2128E16;
  "SSUBW2",32,sail_hl_arm_5fSSUBW2128E32;
  "USUBW",8,sail_hl_arm_5fUSUBW128E8;
  "USUBW",16,sail_hl_arm_5fUSUBW128E16;
  "USUBW",32,sail_hl_arm_5fUSUBW128E32;
  "USUBW2",8,sail_hl_arm_5fUSUBW2128E8;
  "USUBW2",16,sail_hl_arm_5fUSUBW2128E16;
  "USUBW2",32,sail_hl_arm_5fUSUBW2128E32;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_ADDSUB_WIDEN_PROOFS_OK";;
