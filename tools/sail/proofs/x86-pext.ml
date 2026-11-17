(* PEXT, parallel bit extract, on registers at 64 and 32 bits (VEX F3 0F38
   F5, with has_bmi2 assumed present).

   Sail's body is a loop of 32 or 64 steps: step i stores src[i] & mask[i]
   at position k of a temporary and adds mask[i] to k. s2n-bignum's
   x86_PEXT is word_condense of the two operands. The proof shows that the
   loop computes it (see x86-pext-lemmas.ml for why the steps are kept as
   applications of one function and not substituted into each other).

   s2n-bignum's x86_PEXT also appends the event EventX86PEXT(x, y, width)
   with the operands zero-extended to 64 bits. Sail records no events. As
   for POPCNT, the statement follows Sail's relation by that event, taken
   from s2n-bignum's definition and not checked against Sail. Memory
   operands are not compared. *)
needs "x86/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
needs "tools/sail/proofs/x86-pext-lemmas.ml";;
needs "tools/sail/proofs/fresh-model.ml";;

let sail_hl_pext_standard_new_definition = new_definition;;
let sail_hl_pext_before = definitions ();;
module Sail_hl_x86_pext_model = struct
let new_definition = Sail_hl_fresh_model.new_definition;;
loadt "tools/sail/_build/x86-pext.ml";;
end;;
open Sail_hl_x86_pext_model;;
let new_definition = sail_hl_pext_standard_new_definition;;

(* The generated definitions, without the recursion theorem's constant:
   rewriting must use the theorem, not unfold the constant. *)
let sail_hl_pext_definitions =
  filter (fun theorem ->
    not (try fst(dest_const(fst(strip_comb
           (lhs(snd(strip_forall(concl theorem))))))) = "sail_hl_result_case"
         with Failure _ -> false))
    (filter (fun theorem -> not(mem theorem sail_hl_pext_before))
       (definitions ()));;

(* CLAIMS BEGIN *)
let sail_hl_pext_constant root =
  "sail_hl_" ^ String.concat "_5f" (String.split_on_char '_' root);;

(* The generated definitions are unfolded without substituting any let.
   Each step is then folded into an application of sail_hl_x86_pext_step,
   and the chain of 32 or 64 applications is the unrolled
   sail_hl_x86_pext_steps, whose value is word_condense. *)
let SAIL_HL_X86_PEXT_TAC definitions width =
  REPEAT GEN_TAC THEN PURE_REWRITE_TAC definitions THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(DEPTH_CONV(REWR_CONV SAIL_HL_X86_PEXT_INNER)) THEN
  CONV_TAC(ONCE_DEPTH_CONV SAIL_HL_X86_PEXT_CHAIN_CONV) THEN
  SAIL_HL_X86_SCALAR_NORMALIZE ALL_TAC ALL_TAC definitions [width] []
    [x86_PEXT; sail_hl_result_case; seq] THEN
  REWRITE_TAC[GSYM(SAIL_HL_X86_PEXT_UNROLL width);
    if width = 64 then SAIL_HL_X86_PEXT_CONDENSE_64
    else SAIL_HL_X86_PEXT_CONDENSE_32] THEN
  REWRITE_TAC[UNWIND_THM1] THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_EVENTS_INWARD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
  (REFL_TAC ORELSE PRINT_GOAL_TAC);;

(* ModR/M.reg is the destination, VEX.vvvv (n) the source and ModR/M.r/m
   (m) the mask. The event is appended after Sail's relation. *)
let SAIL_HL_X86_PEXT_CLAIM definitions width =
  let root = Printf.sprintf "X86_PEXT%d_RRR" width in
  let component = SAIL_HL_X86_GPR_COMPONENT width false in
  let name = "SAIL_HL_" ^ root ^ "_EQ" in
  print_endline(name ^ " starting");
  let started = Sys.time() in
  let theorem = prove(parse_term(Printf.sprintf
    "!d n m:4 word. !s t:x86state. \
     (%s d n m ,, \
      (\\u. (events := CONS (EventX86PEXT(word_zx (read %s s), \
                                            word_zx (read %s s), \
                                            dimindex(:%d))) \
                              (read events u)) u)) s t <=> \
     x86_PEXT %s %s %s s t"
    (sail_hl_pext_constant root) (component "n") (component "m") width
    (component "d") (component "n") (component "m")),
    SAIL_HL_X86_PEXT_TAC definitions width) in
  Printf.printf "CPU: %.3fs\n%!" (Sys.time() -. started);
  name,theorem;;

let SAIL_HL_X86_PEXT_CLAIMS =
  map (SAIL_HL_X86_PEXT_CLAIM sail_hl_pext_definitions) [64;32];;
if length SAIL_HL_X86_PEXT_CLAIMS <> 2 then
  failwith "wrong pext claim inventory";;

(* CLAIMS END *)

List.iter sail_hl_report SAIL_HL_X86_PEXT_CLAIMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_X86_PEXT_PROOFS_OK";;
