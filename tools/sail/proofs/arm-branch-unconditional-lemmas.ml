(* Offset and register-component facts and the tactic shared by the
   unconditional branch proofs. They add no platform axiom or instruction
   coverage. *)
needs "tools/sail/proofs/arm-branch-state-lemmas.ml";;

let SAIL_HL_ARM_BRANCH_OFFSET26 = prove
 (`!immediate:26 word.
   word_join immediate (word 0:2 word):28 word =
   word(val immediate * 4)`,
  CONV_TAC WORD_BLAST);;

let SAIL_HL_ARM_BRANCH_PC_INCREMENT = prove
 (`!pc:64 word. word_add (word_sub pc (word 4)) (word 4) = pc`,
  CONV_TAC WORD_BLAST);;

let SAIL_HL_ARM_BRANCH_LINK_READS = prove
 (`(!link:64 word. !s:armstate.
      read PC (write X30 link s) = read PC s) /\
   (!link:64 word. !s:armstate.
      read events (write X30 link s) = read events s) /\
   (!link:64 word. !s:armstate.
      read X30 (write X30 link s) = link)`,
  REWRITE_TAC[X30] THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC[]);;

(* Normalize source-generated branches using ordinary component laws.
   Only the exporter's documented BType-write boundary omits source writes;
   this tactic supplies no discarded metadata components. *)
let SAIL_HL_ARM_BRANCH_UNCONDITIONAL_TAC definitions =
  REPEAT GEN_TAC THEN
  REWRITE_TAC(definitions @
    [assign; SEQ; LET_DEF; LET_END_DEF; FST; SND;
     NUM_OF_INT_OF_NUM; READ_COMPONENT_COMPOSE; READ_WRITE_EVALUATE;
     READ_RVALUE; WRITE_RVALUE; ARM_ZERO_REGISTER;
     SAIL_HL_ARM_BRANCH_OFFSET26; SAIL_HL_ARM_BRANCH_PC_INCREMENT;
     SAIL_HL_ARM_BRANCH_PC_READS; SAIL_HL_ARM_BRANCH_LINK_READS]) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[XREG; XREG'; X30; iword; NUM_OF_INT_OF_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC[SAIL_HL_ARM_BRANCH_PC_INCREMENT];;
