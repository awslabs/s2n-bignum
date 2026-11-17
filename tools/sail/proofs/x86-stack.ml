(* LEAVE in long mode with no operand-size override.

   The generated relation retains Sail's original C9 body and pop helper.
   read_mem_data is interpreted as a total little-endian load and one
   EventLoad. Paging, permissions, faults and debug breakpoints are not
   compared. Under that declared boundary, compare the complete state,
   including unchanged memory, flags and registers, for every frame
   pointer, stored value and original event trace. *)
needs "x86/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
needs "tools/sail/proofs/x86-scalar-lemmas.ml";;
needs "tools/sail/proofs/fresh-model.ml";;

let sail_hl_stack_standard_new_definition = new_definition;;
module Sail_hl_x86_stack_model = struct
let new_definition = Sail_hl_fresh_model.new_definition;;
loadt "tools/sail/_build/x86-stack.ml";;
end;;
open Sail_hl_x86_stack_model;;
let new_definition = sail_hl_stack_standard_new_definition;;

let SAIL_HL_X86_LEAVE64_EQ = prove
 (`!s t:x86state. sail_hl_X86_5fLEAVE64 s t <=> x86_LEAVE s t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sail_hl_X86_5fLEAVE64; x86_LEAVE; assign; seq;
              LET_DEF; LET_END_DEF; RSP; RBP; GPR64; FST; SND;
              GSYM WORD_IWORD; WORD_VAL; NUM_OF_INT_OF_NUM;
              WORD_ZX_TRIVIAL] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC[UNWIND_THM1; bytes64; READ_COMPONENT_COMPOSE] THEN
  CONV_TAC(DEPTH_CONV SAIL_HL_X86_EVENTS_INWARD_CONV) THEN
  CONV_TAC(DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
  REWRITE_TAC[asword; through; read] THEN
  (REFL_TAC ORELSE PRINT_GOAL_TAC));;

sail_hl_report ("SAIL_HL_X86_LEAVE64_EQ", SAIL_HL_X86_LEAVE64_EQ);;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_X86_STACK_PROOFS_OK";;
