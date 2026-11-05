(* Agreement of actual EXT execution with both decoder-supported widths.
   The position arguments quantify every legal byte offset. Vector register
   31 and all register overlaps are included. D64 writes clear the upper
   Q64 bits. This proves neither decoding nor full AdvSIMD access checks;
   successful enabled access remains the external projection contract. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-vector-extract.ml";;

let SAIL_HL_ARM_VECTOR_EXTRACT_TAC definition =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[definition; arm_EXT; assign; LET_DEF; LET_END_DEF;
    FST; SND; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM; QREG'; DREG'; DREG;
    READ_ZEROTOP_64; WRITE_ZEROTOP_64] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EQ_SYM_EQ] THEN
  PRINT_GOAL_TAC;;

let SAIL_HL_ARM_EXT64_EQ = prove
 (`!d n m:5 word. !position:3 word. !s t:armstate.
   sail_hl_arm_5fEXT64 d n m position s t <=>
   arm_EXT (DREG' d) (DREG' n) (DREG' m) (val position * 8) s t`,
  SAIL_HL_ARM_VECTOR_EXTRACT_TAC sail_hl_arm_5fEXT64);;

let SAIL_HL_ARM_EXT128_EQ = prove
 (`!d n m:5 word. !position:4 word. !s t:armstate.
   sail_hl_arm_5fEXT128 d n m position s t <=>
   arm_EXT (QREG' d) (QREG' n) (QREG' m) (val position * 8) s t`,
  SAIL_HL_ARM_VECTOR_EXTRACT_TAC sail_hl_arm_5fEXT128);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_EXT64_EQ", SAIL_HL_ARM_EXT64_EQ;
  "SAIL_HL_ARM_EXT128_EQ", SAIL_HL_ARM_EXT128_EQ;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_VECTOR_EXTRACT_PROOFS_OK";;
