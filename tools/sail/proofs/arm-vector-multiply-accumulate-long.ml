(* Prove signed/unsigned widening multiply-add/subtract for forty forms.
   Vector and indexed forms retain both source halves, all encoded lanes and
   register overlaps. Claims compare complete final states under the declared
   register interpretation, not full-platform checks or instruction decoders. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
(* Evaluate fixed helper choices before the packing proofs expand bindings.
   The loader checks and declares the supplied fresh kernel bodies; its
   definition/rewrite commands are local to this generated-model module. *)
loadt "tools/sail/proofs/fresh-model.ml";;
module Sail_vector_multiply_accumulate_long_model = struct
open Sail_hl_fresh_model;;
loadt "tools/sail/_build/arm-vector-multiply-accumulate-long.ml";;
end;;
include Sail_vector_multiply_accumulate_long_model;;
needs "tools/sail/proofs/arm-vector-multiply-long-support.ml";;

(* Reuse only settled, independently proved lane/cast facts. The actual
   instruction models below are a separate export of the accumulator bodies. *)

let SAIL_HL_ARM_VECTOR_MULTIPLY_ACCUMULATE_LONG_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_SMLAL_VEC_ALT; arm_SMLAL2_VEC_ALT;
    arm_SMLSL_VEC_ALT; arm_SMLSL2_VEC_ALT; arm_UMLAL_VEC_ALT;
    arm_UMLAL2_VEC_ALT; arm_UMLSL_VEC_ALT; arm_UMLSL2_VEC_ALT;
    assign; LET_DEF; LET_END_DEF; FST; SND; QREG'; DREG;
    READ_ZEROTOP_64; NUM_OF_INT_OF_NUM; IWORD_INT_MUL;
    GSYM WORD_IWORD; GSYM word_sx; GSYM word_zx;
    QLANE; LANE_H; LANE_S; READ_COMPONENT_COMPOSE; through; read] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM;
    ADD_CLAUSES; ARITH_RULE `(n:num) * 16 = 16 * n`;
    ARITH_RULE `(n:num) * 32 = 32 * n`;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_MFIELD;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_LOW16;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_LOW32] THEN
  SIMP_TAC[WORD_SUBWORD_SUBWORD; WORD_SUBWORD_ZX;
    DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(REDEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_HIGH_POSITION;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_POSITION;
    ADD_CLAUSES; ARITH_RULE `(n:num) * 16 = 16 * n`;
    ARITH_RULE `(n:num) * 32 = 32 * n`;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_MFIELD;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_LOW16;
    SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_LOW32; WORD_ADD_SYM] THEN
  SAIL_HL_ARM_VECTOR_MULTIPLY_LONG_VALUE_TAC;;

let SAIL_HL_ARM_VECTOR_MULTIPLY_ACCUMULATE_LONG_CLAIM instruction element definition =
  let _, body = strip_forall(concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let statement = parse_term(
    "!d n m:5 word. !s t:armstate. " ^ source ^ " d n m s t <=> arm_" ^
    instruction ^ " (QREG' d) (QREG' n) (QREG' m) " ^
    string_of_int element ^ " s t") in
  let theorem = prove(statement,
    SAIL_HL_ARM_VECTOR_MULTIPLY_ACCUMULATE_LONG_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s128E%d_EQ" instruction element in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_MULTIPLY_ACCUMULATE_LONG_INDEXED_CLAIM
    instruction element high definition =
  let _, body = strip_forall(concl definition) in
  let source = fst(dest_const(fst(strip_comb(lhand body)))) in
  let register_width = if element = 16 then 4 else 5 in
  let index_width = if element = 16 then 2 else 1 in
  let offset = if high then 64 / element else 0 in
  let operand = if element = 16 then "(word_zx m:5 word)" else "m" in
  let statement = parse_term(
    "!d n:5 word. !m:" ^ string_of_int register_width ^ " word. !idx:" ^
    string_of_int index_width ^ " word. !s t:armstate. " ^ source ^
    " d n m idx s t <=> arm_" ^ instruction ^ " (QREG' d) (QREG' n) " ^
    "(QLANE " ^ operand ^ " " ^ string_of_int element ^ " (val idx + " ^
    string_of_int offset ^ ")) " ^ string_of_int element ^ " s t") in
  let theorem = prove(statement,
    SAIL_HL_ARM_VECTOR_MULTIPLY_ACCUMULATE_LONG_TAC definition) in
  let name = Printf.sprintf "SAIL_HL_ARM_%s128E%d_%s_EQ"
    instruction element (if high then "HI" else "LO") in
  sail_hl_report (name, theorem);
  name,theorem;;

let SAIL_HL_ARM_VECTOR_MULTIPLY_ACCUMULATE_LONG_CLAIMS = map
  (fun (instruction,element,definition) ->
    SAIL_HL_ARM_VECTOR_MULTIPLY_ACCUMULATE_LONG_CLAIM instruction element definition) [
    "SMLAL_VEC",8,sail_hl_arm_5fSMLAL_5fVEC128E8;
    "SMLAL_VEC",16,sail_hl_arm_5fSMLAL_5fVEC128E16;
    "SMLAL_VEC",32,sail_hl_arm_5fSMLAL_5fVEC128E32;
    "SMLAL2_VEC",8,sail_hl_arm_5fSMLAL2_5fVEC128E8;
    "SMLAL2_VEC",16,sail_hl_arm_5fSMLAL2_5fVEC128E16;
    "SMLAL2_VEC",32,sail_hl_arm_5fSMLAL2_5fVEC128E32;
    "SMLSL_VEC",8,sail_hl_arm_5fSMLSL_5fVEC128E8;
    "SMLSL_VEC",16,sail_hl_arm_5fSMLSL_5fVEC128E16;
    "SMLSL_VEC",32,sail_hl_arm_5fSMLSL_5fVEC128E32;
    "SMLSL2_VEC",8,sail_hl_arm_5fSMLSL2_5fVEC128E8;
    "SMLSL2_VEC",16,sail_hl_arm_5fSMLSL2_5fVEC128E16;
    "SMLSL2_VEC",32,sail_hl_arm_5fSMLSL2_5fVEC128E32;
    "UMLAL_VEC",8,sail_hl_arm_5fUMLAL_5fVEC128E8;
    "UMLAL_VEC",16,sail_hl_arm_5fUMLAL_5fVEC128E16;
    "UMLAL_VEC",32,sail_hl_arm_5fUMLAL_5fVEC128E32;
    "UMLAL2_VEC",8,sail_hl_arm_5fUMLAL2_5fVEC128E8;
    "UMLAL2_VEC",16,sail_hl_arm_5fUMLAL2_5fVEC128E16;
    "UMLAL2_VEC",32,sail_hl_arm_5fUMLAL2_5fVEC128E32;
    "UMLSL_VEC",8,sail_hl_arm_5fUMLSL_5fVEC128E8;
    "UMLSL_VEC",16,sail_hl_arm_5fUMLSL_5fVEC128E16;
    "UMLSL_VEC",32,sail_hl_arm_5fUMLSL_5fVEC128E32;
    "UMLSL2_VEC",8,sail_hl_arm_5fUMLSL2_5fVEC128E8;
    "UMLSL2_VEC",16,sail_hl_arm_5fUMLSL2_5fVEC128E16;
    "UMLSL2_VEC",32,sail_hl_arm_5fUMLSL2_5fVEC128E32;
  ];;

let SAIL_HL_ARM_VECTOR_MULTIPLY_ACCUMULATE_LONG_INDEXED_CLAIMS = map
  (fun (instruction,element,high,definition) ->
    SAIL_HL_ARM_VECTOR_MULTIPLY_ACCUMULATE_LONG_INDEXED_CLAIM
      instruction element high definition) [
    "SMLAL_VEC",16,false,sail_hl_arm_5fSMLAL_5fVEC128E16_5fLO;
    "SMLAL_VEC",16,true,sail_hl_arm_5fSMLAL_5fVEC128E16_5fHI;
    "SMLAL_VEC",32,false,sail_hl_arm_5fSMLAL_5fVEC128E32_5fLO;
    "SMLAL_VEC",32,true,sail_hl_arm_5fSMLAL_5fVEC128E32_5fHI;
    "SMLAL2_VEC",16,false,sail_hl_arm_5fSMLAL2_5fVEC128E16_5fLO;
    "SMLAL2_VEC",16,true,sail_hl_arm_5fSMLAL2_5fVEC128E16_5fHI;
    "SMLAL2_VEC",32,false,sail_hl_arm_5fSMLAL2_5fVEC128E32_5fLO;
    "SMLAL2_VEC",32,true,sail_hl_arm_5fSMLAL2_5fVEC128E32_5fHI;
    "UMLSL_VEC",16,false,sail_hl_arm_5fUMLSL_5fVEC128E16_5fLO;
    "UMLSL_VEC",16,true,sail_hl_arm_5fUMLSL_5fVEC128E16_5fHI;
    "UMLSL_VEC",32,false,sail_hl_arm_5fUMLSL_5fVEC128E32_5fLO;
    "UMLSL_VEC",32,true,sail_hl_arm_5fUMLSL_5fVEC128E32_5fHI;
    "UMLSL2_VEC",16,false,sail_hl_arm_5fUMLSL2_5fVEC128E16_5fLO;
    "UMLSL2_VEC",16,true,sail_hl_arm_5fUMLSL2_5fVEC128E16_5fHI;
    "UMLSL2_VEC",32,false,sail_hl_arm_5fUMLSL2_5fVEC128E32_5fLO;
    "UMLSL2_VEC",32,true,sail_hl_arm_5fUMLSL2_5fVEC128E32_5fHI;
  ];;

check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_MULTIPLY_ACCUMULATE_LONG_PROOFS_OK";;
